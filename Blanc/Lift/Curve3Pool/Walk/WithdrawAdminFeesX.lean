import Blanc.Lift.Curve3Pool.Walk.Dispatch
import Blanc.Lift.Curve3Pool.Walk.AdminBalancesX
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityLoop
import Blanc.Lift.Curve3Pool.Spec

/-!
# `withdraw_admin_fees`, on the actual derivation

From the frame's entry with the `withdraw_admin_fees` selector (`0x30c54085`) the
dispatcher walks past every earlier arm to the arm's test (`0x4d2c`) and falls into its
body (`0x4d3a`): the non-payable guard, the owner guard, the counter init at `0x140`,
then three iterations. Each iteration loads `coins[i]` at `keccak(0) + i`, does one
`balanceOf(self)` `STATICCALL` with the output window `0x220`, asserts the flag and
`RETURNDATASIZE > 31`, then loads `balances[i] = keccak(1) + i`: when the fresh answer
equals the recorded balance nothing moves; when it exceeds it the excess is sent
to the owner with a `raw_call`-shaped `CALL` (returndata-size check and three
identity-precompile copy `CALL`s); the tail bumps the counter and loops back until it
reaches `3`, exiting to `STOP`.

Reuse: `adminBal_disp_taken` (the shared `0x4c85 → 0x4d2c` hop) from
`Walk.AdminBalancesX`; the `xs`/`xji`/`xjd`/`xdead` walk macros and `xa_staticcall_img`,
`WordAt`/`Region` from `FrameWalkKit` via `Walk.Kit` (`Walk.Dispatch`);
`keccak_zero`/`keccak_one` via `Walk.RemoveLiquidityLoop`. The `0 → 0x3040` and
`0x3040 → 0x4c85` dispatcher walks are re-walked with the withdraw `hsw` (they differ
from `admin_balances` only there); hoisting them to `Dispatch.lean` needs an edit to
that file, not owned here.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-! ## Dispatcher to the `withdraw_admin_fees` arm -/

/-- **Dispatcher prefix for `withdraw_admin_fees`**: from the frame's start to `0x3040`
(past the `remove_liquidity` test, taken). -/
theorem wdx_disp_to_3040 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selWithdrawAdminFees)
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
      0x30c54085 := by
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

/-- **Dispatcher continuation for `withdraw_admin_fees`**: from `0x3040` to the
`admin_balances` test (`0x4c85`), taking every arm in between. -/
theorem wdx_disp_to_test {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selWithdrawAdminFees)
    (h : XAt sevm post 0x3040 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4c85 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  have hsw : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      0x30c54085 := by
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
theorem wdx_to_withdraw {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selWithdrawAdminFees)
    (h : XAt sevm post 0x4c85 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4d2c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  have hne : Sevm.selector sevm ≠ selAdminBalances := by
    rw [hsel]; decide
  exact adminBal_disp_taken hcode hne h

/-- **The dispatcher hands `withdraw_admin_fees` its body** (past the arm's own test at
`0x4d2c`, falling into `0x4d3a` on a match). -/
theorem wdx_disp_to_body {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hsel : Sevm.selector sevm = selWithdrawAdminFees)
    (h : XAt sevm post 0x4d2c (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    ∃ G', XAt sevm post 0x4d3a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L := by
  have hsw : Bytes.toB256 ((vyImg [] (Sevm.dataWord sevm 0)).sliceD (Bytes.toB256 [0]).toNat 32 0) =
      0x30c54085 := by
    rw [show (Bytes.toB256 [0]).toNat = 0 from rfl, vyImg_selector]; exact hsel
  xs 0x4d31 (.push [0x30, 0xc5, 0x40, 0x85] (by decide)) ri_push
  xs 0x4d33 (.push [0x00] (by decide)) ri_push
  xs 0x4d34 (.reg .mload) ri_mload_vy0
  xs 0x4d35 (.reg .eq) ri_eq
  xs 0x4d36 (.reg .iszero) ri_iszero
  xs 0x4d39 (.push [0x4f, 0x51] (by decide)) ri_push
  xji 0x4d3a 0x4f51 hw
  · exact ⟨_, h⟩
  · exact absurd (by rw [hsw]; decide) (isNe_jump hw)

/-! ## Guards and counter init -/

/-- **Guards of `withdraw_admin_fees`**: no value, the caller is the owner, the counter at
`0x140` set to `0` with `[3, 0x140]` on the stack, entering the loop at `0x4d5e`. -/
theorem wdx_guards {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (h : XAt sevm post 0x4d3a (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) L) :
    sevm.value = 0 ∧ sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot ∧
    ∃ G' M' img', Mem.Wf M' ∧ Mem.Reads M' img' ∧
      Region img' 0x140 (Nat.toB256 0).toBytes ∧
      XAt sevm post 0x4d5e
        (St (afterSload sevm b ownerSlot) [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]]
          M' G') L := by
  have hR : Mem.Reads (vyMem Mem.empty (Sevm.dataWord sevm 0))
      (vyImg [] (Sevm.dataWord sevm 0)) :=
    vyMem_reads Mem.wf_empty Mem.reads_empty _
  have hW : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  xs 0x4d3b (.reg .callvalue) ri_callvalue
  xs 0x4d3c (.reg .iszero) ri_iszero
  xs 0x4d3f (.push [0x4d, 0x44] (by decide)) ri_push
  xji 0x4d40 0x4d44 hw
  · xdead
  have hval : sevm.value = 0 := eqCheck_ne_zero_eq hw
  clear hw
  xjd 0x4d45
  xs 0x4d47 (.push [0x04] (by decide)) ri_push
  xw 0x4d48 (.reg .sload) ri_sload
  rw [show Bytes.toB256 [4] = ownerSlot from by decide] at h
  xs 0x4d49 (.reg .caller) ri_caller
  xs 0x4d4a (.reg .eq) ri_eq
  xs 0x4d4d (.push [0x4d, 0x52] (by decide)) ri_push
  xji 0x4d4e 0x4d52 hw
  · xdead
  have hown : sevm.caller.toB256 = (b.getStor sevm.currentTarget).get ownerSlot := by
    have e := eqCheck_ne_zero_eq hw
    rw [getStorVal_eq] at e
    exact e
  clear hw
  xjd 0x4d53
  xs 0x4d56 (.push [0x01, 0x40] (by decide)) ri_push
  xs 0x4d58 (.push [0x00] (by decide)) ri_push
  xs 0x4d5a (.push [0x03] (by decide)) ri_push
  xs 0x4d5b (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x4d5c (.reg (.dup 3)) (ri_dup (by rfl))
  xmo 0x4d5d (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  have hctrR : Region (Bytes.writeAt (vyImg [] (Sevm.dataWord sevm 0)) 320
      (Bytes.toB256 [0]).toBytes) 0x140 (Nat.toB256 0).toBytes :=
    Region.write_self _ _ _
  xs 0x4d5e (.reg .add) ri_add
  have h30 : Bytes.toB256 [0x03] + Bytes.toB256 [0x00] = Bytes.toB256 [0x03] := by decide
  rw [h30] at h
  exact ⟨hval, hown, _, _, _, hW, hR, hctrR, h⟩

/-! ## The `balanceOf` calldata in the image -/

/-- The `balanceOf(self)` calldata the staging writes leave at `0x1bc` (the zero word at
`0xc0` and the coin word at `0x160` are underneath; the selector word at `0x1a0` and the
address at `0x1c0` close the window). -/
theorem wdx_input (img coinB : Bytes) (self : Adr) :
    ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160 coinB) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0 self.toB256.toBytes).sliceD
      0x1bc 0x24 0) = balanceOfData self := by
  show ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
    (Bytes.toB256 [0]).toBytes) 0x160 coinB) 0x1a0
    (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0 self.toB256.toBytes).sliceD
    0x1bc 0x24 0) = balanceOfSel ++ self.toB256.toBytes
  have hsel : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160 coinB) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1bc balanceOfSel := by
    have := Region.write_self (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160 coinB) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes
    rw [adminBal_sel_bytes] at this
    exact this.right
  have hsel2 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160 coinB) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0 self.toB256.toBytes) 0x1bc
      balanceOfSel :=
    Region.write_other hsel (by simp only [balanceOfSel, B256.length_toBytes,
      List.length_cons, List.length_nil]; omega)
  refine Region.slice (Region.append' (o' := 0x1c0) ?_ ?_ (by rfl))
    (by simp only [balanceOfSel, List.length_append, B256.length_toBytes, List.length_cons,
      List.length_nil])
  · exact hsel2
  · exact Region.write_self _ _ _

/-- The answer word the `STATICCALL` wrote at `0x220` reads back. -/
theorem wdx_read_out (img : Bytes) (out : Bytes) (hlen : (out.take 32).length = 32) :
    Bytes.toB256 ((Bytes.writeAt img 0x220 (out.take 32)).sliceD 0x220 32 0) =
      Bytes.toB256 (out.take 32) :=
  Region.read (Region.write_self img 0x220 (out.take 32)) hlen

/-! ## One loop iteration: staticcall half -/

/-- `ISZERO (LT a b)` jumped: `¬ a < b`. -/
theorem wdx_not_lt_of_hw {a b : B256}
    (hw : B256.eqCheck (B256.ltCheck a b) 0 ≠ 0) : ¬ a < b := by
  intro hlt
  have h1 : B256.ltCheck a b = 1 := by
    unfold B256.ltCheck
    simp only [hlt, ↓reduceIte]
  rw [h1] at hw
  exact absurd rfl hw

/-- **One `withdraw_admin_fees` iteration, staticcall half** (`0x4d5e → 0x4dfb`): with the
counter at `k`, one `balanceOf` `STATICCALL`, the `ans ≥ rec` assert, and the recorded
balance load; either the fresh answer equals the recording (skip to the tail at `0x4f3c`)
or it exceeds it (fall into the transfer at `0x4dfc`). -/
theorem wdx_iter_static {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {M : Mem}
    {img : Bytes} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (k : Fin 3) (hid : IdReady sevm d)
    (hpc : d.getCode sevm.currentTarget ≠ .empty)
    (hsk : StaticKeeps sevm ((d.getStor sevm.currentTarget).get (coinSlot k)))
    (hctrR : Region img 0x140 (Nat.toB256 ↑k).toBytes)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hcoinK : ¬ sevm.benvStat.rules.isPrecomp
      (((d.getStor sevm.currentTarget).get (coinSlot k)).toAdr))
    (h : XAt sevm post 0x4d5e
      (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) L) :
    ∃ (c : Exec.Frame) (out : Bytes) (L' : List Exec.Frame) (d' : Devm) (M' : Mem)
      (img' : Bytes) (G' : Nat) (ansW recW : B256),
      L = c :: L' ∧
      c.sevm.currentTarget = ((d.getStor sevm.currentTarget).get (coinSlot k)).toAdr ∧
      c.sevm.data = balanceOfData sevm.currentTarget ∧
      c.sevm.isStatic = true ∧
      c.post.output = out ∧ 32 ≤ out.length ∧
      c.post.logs = [] ∧
      ansW = Bytes.toB256 (out.take 32) ∧
      recW = (d'.getStor sevm.currentTarget).get (balanceSlot k) ∧
      recW.toNat ≤ ansW.toNat ∧
      (d'.getStor sevm.currentTarget) = (d.getStor sevm.currentTarget) ∧
      d'.logs = d.logs ∧
      d'.output = d.output ∧
      0 < sevm.depth ∧ IdReady sevm d' ∧
      d'.getCode sevm.currentTarget = d.getCode sevm.currentTarget ∧
      Region img' 0x140 (Nat.toB256 ↑k).toBytes ∧
      Region img' 0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes ∧
      Region img' 0x180 (ansW - recW).toBytes ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧
      ((ansW = recW ∧ XAt sevm post 0x4f3c
        (St d' [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') L') ∨
       (ansW ≠ recW ∧ XAt sevm post 0x4dfc
        (St d' [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') L')) := by
  xjd 0x4d5f
  xs 0x4d62 (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x4d63 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Region.read hctrR (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4d65 (.push [0x03] (by decide)) ri_push
  xs 0x4d66 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x4d67 (.reg .lt) ri_lt
  xs 0x4d6a (.push [0x4d, 0x6f] (by decide)) ri_push
  have hltK : Nat.toB256 ↑k < Bytes.toB256 [0x03] := by
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega),
      show (Bytes.toB256 [0x03]).toNat = 3 by decide]
    exact k.isLt
  xji 0x4d6b 0x4d6f hw
  · exact absurd hw (ltCheck_ne_zero_of_lt hltK)
  clear hw
  xjd 0x4d70
  xs 0x4d72 (.push [0x00] (by decide)) ri_push
  xs 0x4d74 (.push [0xc0] (by decide)) ri_push
  xmo 0x4d75 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  have hctrR_C : Region (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x140
      (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR (Or.inr (by decide))
  xs 0x4d77 (.push [0x20] (by decide)) ri_push
  xs 0x4d79 (.push [0xc0] (by decide)) ri_push
  xmo 0x4d7a (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_zero] at h
  xs 0x4d7b (.reg .add) ri_add
  have hslot : coinsBase + Nat.toB256 ↑k = coinSlot k := rfl
  rw [hslot] at h
  xw 0x4d7c (.reg .sload) ri_sload
  rw [getStorVal_eq] at h
  xs 0x4d7f (.push [0x01, 0x60] (by decide)) ri_push
  xmo 0x4d80 (.reg .mstore) (ri_mstore_imgAt (o := 0x160) rfl)
  have hctrR_D : Region (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x140
      (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_C (Or.inl (by simp only [B256.length_toBytes]; omega))
  have hcoinW0 : Region (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes :=
    Region.write_self _ _ _
  xs 0x4d82 (.push [0x20] (by decide)) ri_push
  xs 0x4d85 (.push [0x02, 0x20] (by decide)) ri_push
  xs 0x4d87 (.push [0x24] (by decide)) ri_push
  xs 0x4d8c (.push [0x70, 0xa0, 0x82, 0x31] (by decide)) ri_push
  xs 0x4d8f (.push [0x01, 0xa0] (by decide)) ri_push
  xmo 0x4d90 (.reg .mstore) (ri_mstore_imgAt (o := 0x1a0) rfl)
  have hctrR_E : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_D (Or.inl (by simp only [B256.length_toBytes]; omega))
  have hcoinW1 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes :=
    Region.write_other hcoinW0 (Or.inl (by simp only [B256.length_toBytes]; omega))
  xs 0x4d91 (.reg .address) ri_address
  xs 0x4d94 (.push [0x01, 0xc0] (by decide)) ri_push
  xmo 0x4d95 (.reg .mstore) (ri_mstore_imgAt (o := 0x1c0) rfl)
  have hctrR_F : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_E (Or.inl (by simp only [B256.length_toBytes]; omega))
  have hcoinW2 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0
      (Bytes.toB256 [0]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes :=
    Region.write_other hcoinW1 (Or.inl (by simp only [B256.length_toBytes]; omega))
  xs 0x4d98 (.push [0x01, 0xbc] (by decide)) ri_push
  xs 0x4d9b (.push [0x01, 0x60] (by decide)) ri_push
  xmo 0x4d9c (.reg .mload) (ri_mload_imgAt (o := 0x160) rfl)
  rw [Region.read hcoinW2 (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4d9d (.reg .gas) ri_gas_remaining
  replace h := xa_staticcall_img (pc' := 0x4d9e) (i := 0x1bc) (n := 0x24) (o := 0x220)
    (z := 0x20) hfork (atN hcode (by kernel_rfl)) rfl rfl rfl rfl rfl hR hW h
  clear hR hW
  obtain ⟨d1, flag, out, M', L1, h, hexec, hR, hW, hrd, hob, hstor1, hlogs1, hk⟩ := h
  have hctrR_G : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x220 (out.take 32)) 0x140
      (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_F (Or.inl (by simp only [B256.length_toBytes]; omega))
  xs 0x4da1 (.push [0x4d, 0xa6] (by decide)) ri_push
  xji 0x4da2 0x4da6 hw
  · xdead
  rcases hk hw with ⟨hpre, -⟩ | ⟨c, hL, hdepth, houtKeep, hacc, hcodeKeep, htgt, hdata, hstat, hout,
    hclogs, -, -⟩
  · exact absurd hpre hcoinK
  clear hk hw
  obtain ⟨d0, hrunStatic, hcodeStatic⟩ := hexec
  have h4 := hsk _ _ _ _ _ _ _ _ rfl hrunStatic
  change d0.getCode 4 = (afterSload sevm d (coinSlot k)).getCode 4 at h4
  rw [afterSload_getCode, hcodeStatic] at h4
  have hid1 : IdReady sevm d1 :=
    ⟨by rw [h4]; exact hid.nodeleg,
      hacc _ (by rw [afterSload_accessedAddresses]; exact hid.warm), hid.pre, hid.fork⟩
  have hcode1 : d1.getCode sevm.currentTarget = d.getCode sevm.currentTarget := by
    have hpc0 : (afterSload sevm d (coinSlot k)).getCode sevm.currentTarget ≠ .empty := by
      rw [afterSload_getCode]; exact hpc
    rw [hcodeKeep _ hpc0, afterSload_getCode]
  rw [wdx_input] at hdata
  xjd 0x4da7
  xs 0x4da9 (.push [0x1f] (by decide)) ri_push
  xs 0x4daa (.reg .returndatasize) ri_returndatasize
  xs 0x4dab (.reg .gt) ri_gt
  xs 0x4dae (.push [0x4d, 0xb3] (by decide)) ri_push
  xji 0x4daf 0x4db3 hw
  · xdead
  have hlen32 : 32 ≤ out.length := by
    have hgt := gtCheck_ne_zero hw
    rw [B256.lt_iff_toNat_lt_toNat, hrd, B256.toNat_toB256_of_lt hob,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at hgt
    omega
  clear hw
  xjd 0x4db4
  xs 0x4db6 (.push [0x00] (by decide)) ri_push
  xs 0x4db7 (.reg .pop) ri_pop
  xs 0x4dba (.push [0x02, 0x20] (by decide)) ri_push
  xmo 0x4dbb (.reg .mload) (ri_mload_imgAt (o := 0x220) rfl)
  have hlen : (out.take 32).length = 32 := by rw [List.length_take]; omega
  rw [wdx_read_out _ _ hlen] at h
  clear hlen
  xs 0x4dbe (.push [0x01, 0x40] (by decide)) ri_push
  xmo 0x4dbf (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Region.read hctrR_G (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4dc1 (.push [0x03] (by decide)) ri_push
  xs 0x4dc2 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x4dc3 (.reg .lt) ri_lt
  xs 0x4dc6 (.push [0x4d, 0xcb] (by decide)) ri_push
  xji 0x4dc7 0x4dcb hw
  · exact absurd hw (ltCheck_ne_zero_of_lt hltK)
  clear hw
  xjd 0x4dcc
  xs 0x4dce (.push [0x01] (by decide)) ri_push
  xs 0x4dd0 (.push [0xc0] (by decide)) ri_push
  xmo 0x4dd1 (.reg .mstore) (ri_mstore_imgAt (o := 0xc0) rfl)
  have hctrR_H0 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x220 (out.take 32)) 0xc0
      (Bytes.toB256 [1]).toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_G (Or.inr (by decide))
  xs 0x4dd3 (.push [0x20] (by decide)) ri_push
  xs 0x4dd5 (.push [0xc0] (by decide)) ri_push
  xmo 0x4dd6 (.reg .keccak256) (ri_keccak_imgAt (o := 0xc0) (z := 0x20) rfl rfl)
  rw [keccak_one] at h
  xs 0x4dd7 (.reg .add) ri_add
  have hslotB : balancesBase + Nat.toB256 ↑k = balanceSlot k := rfl
  rw [hslotB] at h
  xw 0x4dd8 (.reg .sload) ri_sload
  rw [getStorVal_eq] at h
  xs 0x4dd9 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4dda (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x4ddb (.reg .lt) ri_lt
  xs 0x4ddc (.reg .iszero) ri_iszero
  xs 0x4ddf (.push [0x4d, 0xe4] (by decide)) ri_push
  xji 0x4de0 0x4de4 hw
  · xdead
  have hge : ((d1.getStor sevm.currentTarget).get (balanceSlot k)).toNat ≤
      (Bytes.toB256 (out.take 32)).toNat := by
    have hge' := wdx_not_lt_of_hw hw
    rw [B256.lt_iff_toNat_lt_toNat] at hge'
    omega
  have hgeB : (d1.getStor sevm.currentTarget).get (balanceSlot k) ≤
      Bytes.toB256 (out.take 32) :=
    not_lt.mp (wdx_not_lt_of_hw hw)
  clear hw
  xjd 0x4de5
  xs 0x4de6 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4de7 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x4de8 (.reg .sub) ri_sub
  xs 0x4de9 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x4dea (.reg .pop) ri_pop
  xs 0x4deb (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x4dec (.reg .pop) ri_pop
  xs 0x4def (.push [0x01, 0x80] (by decide)) ri_push
  xmo 0x4df0 (.reg .mstore) (ri_mstore_imgAt (o := 0x180) rfl)
  have hctrR_H : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x220 (out.take 32)) 0xc0
      (Bytes.toB256 [1]).toBytes) 0x180
      (Bytes.toB256 (out.take 32) - (d1.getStor sevm.currentTarget).get
        (balanceSlot k)).toBytes) 0x140 (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_H0 (Or.inl (by simp only [B256.length_toBytes]; omega))
  have hcoinR0 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x220 (out.take 32)) 0xc0
      (Bytes.toB256 [1]).toBytes) 0x180
      (Bytes.toB256 (out.take 32) - (d1.getStor sevm.currentTarget).get
        (balanceSlot k)).toBytes) 0x160
      ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes :=
    Region.write_other (Region.write_other (Region.write_other hcoinW2
      (Or.inl (by simp only [B256.length_toBytes]; omega))) (Or.inr (by decide)))
      (Or.inl (by simp only [B256.length_toBytes]; omega))
  have hfeesR0 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x220 (out.take 32)) 0xc0
      (Bytes.toB256 [1]).toBytes) 0x180
      (Bytes.toB256 (out.take 32) - (d1.getStor sevm.currentTarget).get
        (balanceSlot k)).toBytes) 0x180
      (Bytes.toB256 (out.take 32) - (d1.getStor sevm.currentTarget).get
        (balanceSlot k)).toBytes :=
    Region.write_self _ _ _
  xs 0x4df2 (.push [0x00] (by decide)) ri_push
  xs 0x4df5 (.push [0x01, 0x80] (by decide)) ri_push
  xmo 0x4df6 (.reg .mload) (ri_mload_imgAt (o := 0x180) rfl)
  have hfeesW : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0xc0 (Bytes.toB256 [0]).toBytes)
      0x160 ((d.getStor sevm.currentTarget).get (coinSlot k)).toBytes) 0x1a0
      (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31]).toBytes) 0x1c0
      sevm.currentTarget.toB256.toBytes) 0x220 (out.take 32)) 0xc0
      (Bytes.toB256 [1]).toBytes) 0x180
      (Bytes.toB256 (out.take 32) - (d1.getStor sevm.currentTarget).get
        (balanceSlot k)).toBytes) 0x180
      (Bytes.toB256 (out.take 32) - (d1.getStor sevm.currentTarget).get
        (balanceSlot k)).toBytes :=
    Region.write_self _ _ _
  rw [Region.read hfeesW (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4df7 (.reg .gt) ri_gt
  xs 0x4df8 (.reg .iszero) ri_iszero
  xs 0x4dfb (.push [0x4f, 0x3c] (by decide)) ri_push
  have hfees : (Bytes.toB256 (out.take 32) -
      (d1.getStor sevm.currentTarget).get (balanceSlot k)).toNat =
      (Bytes.toB256 (out.take 32)).toNat -
        ((d1.getStor sevm.currentTarget).get (balanceSlot k)).toNat :=
    B256.toNat_sub_eq_of_le _ _ hgeB
  xji 0x4dfc 0x4f3c hw
  · have hneFees : B256.gtCheck (Bytes.toB256 (out.take 32) -
        (d1.getStor sevm.currentTarget).get (balanceSlot k)) 0 ≠ 0 :=
      eqCheck_eq_zero hw
    have hpos := gtCheck_ne_zero hneFees
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero, hfees] at hpos
    have hne : Bytes.toB256 (out.take 32) ≠
        (d1.getStor sevm.currentTarget).get (balanceSlot k) := by
      intro e
      rw [e] at hpos
      omega
    refine ⟨c, out, L1, _, _, _, _,
      Bytes.toB256 (out.take 32),
      (d1.getStor sevm.currentTarget).get (balanceSlot k), hL, htgt, hdata, hstat, hout,
      hlen32, hclogs, rfl, by rw [afterSload_getStor sevm d1 (balanceSlot k)], hge,
      by rw [afterSload_getStor sevm d1 (balanceSlot k), hstor1,
        afterSload_getStor sevm d (coinSlot k)],
      by rw [afterSload_logs sevm d1 (balanceSlot k), hlogs1,
        afterSload_logs sevm d (coinSlot k)],
      by rw [afterSload_output sevm d1 (balanceSlot k), houtKeep,
        afterSload_output sevm d (coinSlot k)], hdepth, hid1.afterSload _,
      by rw [afterSload_getCode, hcode1], hctrR_H, hcoinR0, hfeesR0, hR, hW,
      Or.inr ⟨hne, h⟩⟩
  · have heqFees : B256.gtCheck (Bytes.toB256 (out.take 32) -
        (d1.getStor sevm.currentTarget).get (balanceSlot k)) 0 = 0 :=
      eqCheck_ne_zero_eq hw
    have hle := gtCheck_eq_zero heqFees
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero, hfees] at hle
    have heq : Bytes.toB256 (out.take 32) =
        (d1.getStor sevm.currentTarget).get (balanceSlot k) := by
      apply B256.toNat_inj
      omega
    refine ⟨c, out, L1, _, _, _, _,
      Bytes.toB256 (out.take 32),
      (d1.getStor sevm.currentTarget).get (balanceSlot k), hL, htgt, hdata, hstat, hout,
      hlen32, hclogs, rfl, by rw [afterSload_getStor sevm d1 (balanceSlot k)], hge,
      by rw [afterSload_getStor sevm d1 (balanceSlot k), hstor1,
        afterSload_getStor sevm d (coinSlot k)],
      by rw [afterSload_logs sevm d1 (balanceSlot k), hlogs1,
        afterSload_logs sevm d (coinSlot k)],
      by rw [afterSload_output sevm d1 (balanceSlot k), houtKeep,
        afterSload_output sevm d (coinSlot k)], hdepth, hid1.afterSload _,
      by rw [afterSload_getCode, hcode1], hctrR_H, hcoinR0, hfeesR0, hR, hW,
      Or.inl ⟨heq, h⟩⟩

/-! ## The loop tail -/

/-- **The `withdraw_admin_fees` loop tail** (`0x4f3c`): the counter becomes `k + 1`; either
loop back to `0x4d5e` (still below `3`) or fall out to `0x4f50` (reached `3`). -/
theorem wdx_tail {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {M : Mem}
    {img : Bytes} {G : Nat}
    (hcode : sevm.code = code)
    (k : Nat) (hk3 : k < 3)
    (hctrR : Region img 0x140 (Nat.toB256 k).toBytes)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x4f3c
      (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) L) :
    (k + 1 < 3 ∧ ∃ G' M' img',
      Region img' 0x140 (Nat.toB256 (k + 1)).toBytes ∧
      Mem.Reads M' img' ∧ Mem.Wf M' ∧
      XAt sevm post 0x4d5e
        (St d [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M' G') L)
    ∨ (k + 1 = 3 ∧ ∃ M' G', XAt sevm post 0x4f50 (St d [] M' G') L) := by
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
  xjd 0x4f3d
  xjd 0x4f3e
  xs 0x4f3f (.reg (.dup 1)) (ri_dup (by rfl))
  xmo 0x4f40 (.reg .mload) (ri_mload_imgAt (o := 0x140) rfl)
  rw [Region.read hctrR (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4f42 (.push [0x01] (by decide)) ri_push
  xs 0x4f43 (.reg .add) ri_add
  rw [hplus] at h
  xs 0x4f44 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4f45 (.reg (.dup 3)) (ri_dup (by rfl))
  xmo 0x4f46 (.reg .mstore) (ri_mstore_imgAt (o := 0x140) rfl)
  have hctrR' : Region (Bytes.writeAt img 0x140 (Nat.toB256 (k + 1)).toBytes) 0x140
      (Nat.toB256 (k + 1)).toBytes :=
    Region.write_self _ _ _
  xs 0x4f47 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x4f48 (.reg .eq) ri_eq
  xs 0x4f49 (.reg .iszero) ri_iszero
  xs 0x4f4c (.push [0x4d, 0x5e] (by decide)) ri_push
  have h32 : (Bytes.toB256 [0x03]).toNat = 3 := by decide
  have hkp1 : (Nat.toB256 (k + 1)).toNat = k + 1 :=
    B256.toNat_toB256_of_lt (by omega : k + 1 < 2 ^ 256)
  by_cases hdone : k + 1 = 3
  · xji 0x4f4d 0x4d5e hw
    · xjd 0x4f4e
      xs 0x4f4f (.reg .pop) ri_pop
      xs 0x4f50 (.reg .pop) ri_pop
      exact Or.inr ⟨hdone, _, _, h⟩
    · have hne := isNe_jump hw
      have h3 : (Bytes.toB256 [0x03]).toNat ≠ (Nat.toB256 (k + 1)).toNat :=
        fun e => hne (B256.toNat_inj _ _ e)
      rw [h32, hkp1] at h3
      omega
  · have hback : k + 1 < 3 := by omega
    xji 0x4f4d 0x4d5e hw
    · have heq := isNe_fall hw
      have h3 : (Bytes.toB256 [0x03]).toNat = (Nat.toB256 (k + 1)).toNat :=
        congrArg B256.toNat heq
      rw [h32, hkp1] at h3
      omega
    · exact Or.inl ⟨hback, _, _, _, hctrR', hR, hW, h⟩

/-! ## The transfer: staging and first identity copy -/

/-- **Transfer staging and first identity copy** (`0x4dfc → 0x4e44`): the `transfer`
selector word staged at `0x2c0`, the selector's first four bytes copied through the
identity precompile to `0x320`; no child, storage/logs/output kept. -/
theorem wdx_xfer_stage {sevm : Sevm} {post d' : Devm} {L : List Exec.Frame} {M : Mem}
    {img : Bytes} {G : Nat}
    (hcode : sevm.code = code)
    (k : Fin 3) (feesW : B256) (hdepth : 0 < sevm.depth) (hid : IdReady sevm d')
    (hctrR : Region img 0x140 (Nat.toB256 ↑k).toBytes)
    (hcoinR : Region img 0x160
      ((d'.getStor sevm.currentTarget).get (coinSlot k)).toBytes)
    (hfeesR : Region img 0x180 feesW.toBytes)
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x4dfc
      (St d' [Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M G) L) :
    ∃ (d1 : Devm) (M1 : Mem) (img1 : Bytes) (G1 : Nat),
      BaseRel d' d1 ∧
      Region img1 0x140 (Nat.toB256 ↑k).toBytes ∧
      Region img1 0x2a0 (Bytes.toB256 [0x04]).toBytes ∧
      Region img1 0x160 ((d'.getStor sevm.currentTarget).get (coinSlot k)).toBytes ∧
      Region img1 0x180 feesW.toBytes ∧
      Region img1 0x320 transferSel ∧
      Mem.Reads M1 img1 ∧ Mem.Wf M1 ∧
      XAt sevm post 0x4e44
        (St d1 [Bytes.toB256 [0x02, 0xa0], Bytes.toB256 [0x00],
          Bytes.toB256 [0x03], Bytes.toB256 [0x01, 0x40]] M1 G1) L := by
  xs 0x4dfe (.push [0x00] (by decide)) ri_push
  xs 0x4e00 (.push [0x04] (by decide)) ri_push
  xs 0x4e03 (.push [0x02, 0xa0] (by decide)) ri_push
  xmo 0x4e04 (.reg .mstore) (ri_mstore_imgAt (o := 0x2a0) rfl)
  have hctrR_1 : Region (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes) 0x140
      (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR (Or.inl (by simp only [B256.length_toBytes]; omega))
  xs 0x4e25 (.push [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) ri_push
  xs 0x4e28 (.push [0x02, 0xc0] (by decide)) ri_push
  xmo 0x4e29 (.reg .mstore) (ri_mstore_imgAt (o := 0x2c0) rfl)
  have hctrR_2 : Region (Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes)
      0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes) 0x140
      (Nat.toB256 ↑k).toBytes :=
    Region.write_other hctrR_1 (Or.inl (by simp only [B256.length_toBytes]; omega))
  xs 0x4e2c (.push [0x02, 0xa0] (by decide)) ri_push
  xs 0x4e2e (.push [0x04] (by decide)) ri_push
  xs 0x4e2f (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4e31 (.push [0x20] (by decide)) ri_push
  xs 0x4e32 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x4e35 (.push [0x03, 0x00] (by decide)) ri_push
  xs 0x4e36 (.reg .add) ri_add
  have hadd1 : Bytes.toB256 [0x03, 0x00] + Bytes.toB256 [0x00] =
      Bytes.toB256 [0x03, 0x00] := by decide
  rw [hadd1] at h
  xs 0x4e37 (.reg .add) ri_add
  have hadd2 : Bytes.toB256 [0x03, 0x00] + Bytes.toB256 [0x20] =
      Bytes.toB256 [0x03, 0x20] := by decide
  rw [hadd2] at h
  xs 0x4e38 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x4e3a (.push [0x20] (by decide)) ri_push
  xs 0x4e3b (.reg (.dup 5)) (ri_dup (by rfl))
  xs 0x4e3c (.reg .add) ri_add
  have hadd3 : Bytes.toB256 [0x02, 0xa0] + Bytes.toB256 [0x20] =
      Bytes.toB256 [0x02, 0xc0] := by decide
  rw [hadd3] at h
  xs 0x4e3e (.push [0x00] (by decide)) ri_push
  xs 0x4e40 (.push [0x04] (by decide)) ri_push
  xs 0x4e41 (.reg .gas) ri_gas_remaining
  replace h := xa_identity_img (pc' := 0x4e42) (i := 0x2c0) (n := 4) (o := 0x320)
    (z := 4) hid (atN hcode (by kernel_rfl)) rfl (by decide) (by decide) (by decide)
    (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L1, h, hk⟩ := h
  rcases hk with ⟨h0, hgas⟩ | ⟨rfl, b2, G2, M, hsha, rfl, hR, hW⟩
  · have hz := hgas rfl hdepth (by decide)
    obtain ⟨_, s, -⟩ := xa_next (n := .reg .pop) (atN hcode (by kernel_rfl)) (by nofun) h
    exact absurd (gasLeft_of_run_pop s) (by rw [hz]; decide)
  · xs 0x4e43 (.reg .pop) ri_pop
    xs 0x4e44 (.reg .pop) ri_pop
    have hctrR_2c : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00]).toBytes) 0x320 (((Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00]).toBytes).sliceD 0x2c0 4 0).take 4)) 0x140
        (Nat.toB256 ↑k).toBytes :=
      Region.write_other hctrR_2 (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hb12 : BaseRel d' b2 := by
      exact ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
    have hlen4a : Region (Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes)
        0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes) 0x2a0
        (Bytes.toB256 [0x04]).toBytes :=
      Region.write_other (Region.write_self _ _ _)
        (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hlen4 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00]).toBytes) 0x320 (((Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00]).toBytes).sliceD 0x2c0 4 0).take 4)) 0x2a0 (Bytes.toB256 [0x04]).toBytes :=
      Region.write_other hlen4a (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hcoinR1a : Region (Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes)
        0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes) 0x160
        ((d'.getStor sevm.currentTarget).get (coinSlot k)).toBytes :=
      Region.write_other (Region.write_other hcoinR
        (Or.inl (by simp only [B256.length_toBytes]; omega)))
        (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hcoinR1 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00]).toBytes) 0x320 (((Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00]).toBytes).sliceD 0x2c0 4 0).take 4)) 0x160
        ((d'.getStor sevm.currentTarget).get (coinSlot k)).toBytes :=
      Region.write_other hcoinR1a (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hfeesR1a : Region (Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes)
        0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes) 0x180
        feesW.toBytes :=
      Region.write_other (Region.write_other hfeesR
        (Or.inl (by simp only [B256.length_toBytes]; omega)))
        (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hfeesR1 : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00]).toBytes) 0x320 (((Bytes.writeAt (Bytes.writeAt img 0x2a0
        (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
          0x00]).toBytes).sliceD 0x2c0 4 0).take 4)) 0x180 feesW.toBytes :=
      Region.write_other hfeesR1a (Or.inl (by simp only [B256.length_toBytes]; omega))
    have hselWord : WordAt (Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) :=
      WordAt.write_self _ _ _
    have hsel4 : ((Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes).sliceD 0x2c0 4 0).take 4 = transferSel := by
      rw [hselWord.prefix (by decide)]; decide
    have hselCopy : Region (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes) 0x320
        (((Bytes.writeAt (Bytes.writeAt img 0x2a0 (Bytes.toB256 [0x04]).toBytes) 0x2c0 (Bytes.toB256 [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]).toBytes).sliceD 0x2c0 4 0).take 4)) 0x320 transferSel := by
      rw [hsel4]; exact Region.write_self _ _ _
    exact ⟨b2, M, _, _, hb12, hctrR_2c, hlen4, hcoinR1, hfeesR1, hselCopy, hR, hW, h⟩

/-- Assemble the transfer payload after the selector copy, ending before the checked
identity copy (`0x4e44 → 0x4e78`). -/
theorem wdx_xfer_payload {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {M : Mem} {img : Bytes} {G : Nat} (hcode : sevm.code = code)
    (k : Fin 3) (coin fees : B256)
    (hctr : Region img 0x140 (Nat.toB256 ↑k).toBytes)
    (hcoin : Region img 0x160 coin.toBytes) (hfees : Region img 0x180 fees.toBytes)
    (hlen : Region img 0x2a0 (Bytes.toB256 [4]).toBytes)
    (hsel : Region img 0x320 transferSel) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x4e44
      (St b [Bytes.toB256 [0x02, 0xa0], Bytes.toB256 [0],
        Bytes.toB256 [3], Bytes.toB256 [0x01, 0x40]] M G) L) :
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧
      Region img' 0x140 (Nat.toB256 ↑k).toBytes ∧
      Region img' 0x160 coin.toBytes ∧
      Region img' 0x300 ((0x44 : B256).toBytes ++
        (transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes)) ∧
      XAt sevm post 0x4e78
        (St b [Bytes.toB256 [3, 0], Bytes.toB256 [3], Bytes.toB256 [1, 0x40]] M' G') L := by
  xs 0x4e45 (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x4e46 (.reg .mload) (ri_mload_imgAt (o := 0x2a0) rfl)
  rw [Region.read hlen (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4e47 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x4e48 (.reg .add) ri_add
  have e4 : Bytes.toB256 [0] + Bytes.toB256 [4] = (4 : B256) := by decide
  rw [e4] at h
  xs 0x4e49 (.reg (.swap 1)) (ri_swap (by rfl))
  xs 0x4e4a (.reg .pop) ri_pop
  xs 0x4e4b (.reg .pop) ri_pop
  xs 0x4e4c (.reg .caller) ri_caller
  xs 0x4e4e (.push [0x20] (by decide)) ri_push
  xs 0x4e4f (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x4e52 (.push [3, 0] (by decide)) ri_push
  xs 0x4e53 (.reg .add) ri_add
  xs 0x4e54 (.reg .add) ri_add
  xmo 0x4e55 (.reg .mstore) (ri_mstore_imgAt (o := 0x324) (by decide))
  xs 0x4e57 (.push [0x20] (by decide)) ri_push
  xs 0x4e58 (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x4e59 (.reg .add) ri_add
  have e24 : (4 : B256) + Bytes.toB256 [0x20] = (0x24 : B256) := by decide
  rw [e24] at h
  xs 0x4e5a (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x4e5b (.reg .pop) ri_pop
  xs 0x4e5e (.push [1, 0x80] (by decide)) ri_push
  xmo 0x4e5f (.reg .mload) (ri_mload_imgAt (o := 0x180) rfl)
  rw [Region.read (Region.write_other hfees (Or.inl (by simp only [B256.length_toBytes]; omega)))
    (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4e61 (.push [0x20] (by decide)) ri_push
  xs 0x4e62 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x4e65 (.push [3, 0] (by decide)) ri_push
  xs 0x4e66 (.reg .add) ri_add
  xs 0x4e67 (.reg .add) ri_add
  xmo 0x4e68 (.reg .mstore) (ri_mstore_imgAt (o := 0x344) (by decide))
  xs 0x4e6a (.push [0x20] (by decide)) ri_push
  xs 0x4e6b (.reg (.dup 1)) (ri_dup (by rfl))
  xs 0x4e6c (.reg .add) ri_add
  have e44 : (0x24 : B256) + Bytes.toB256 [0x20] = (0x44 : B256) := by decide
  rw [e44] at h
  xs 0x4e6d (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x4e6e (.reg .pop) ri_pop
  xs 0x4e6f (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4e72 (.push [3, 0] (by decide)) ri_push
  xmo 0x4e73 (.reg .mstore) (ri_mstore_imgAt (o := 0x300) rfl)
  xs 0x4e76 (.push [3, 0] (by decide)) ri_push
  xs 0x4e77 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x4e78 (.reg .pop) ri_pop
  obtain ⟨img', hR, hI⟩ := Mem.Reads.forget hR
  have fctr : Region img' 0x140 (Nat.toB256 ↑k).toBytes := by rw [hI]; wchainT; exact hctr
  have fcoin : Region img' 0x160 coin.toBytes := by rw [hI]; wchainT; exact hcoin
  have flen : Region img' 0x300 (0x44 : B256).toBytes := by rw [hI]; wchainT
  have fsel : Region img' 0x320 transferSel := by rw [hI]; wchainT; exact hsel
  have fdst : Region img' 0x324 sevm.caller.toB256.toBytes := by rw [hI]; wchainT
  have famt : Region img' 0x344 fees.toBytes := by rw [hI]; wchainT
  have fargs := Region.append' fdst famt (by simp only [B256.length_toBytes])
  have fcall := Region.append' fsel fargs (by decide)
  have fdata := Region.append' flen fcall (by simp only [B256.length_toBytes])
  exact ⟨_, img', _, hR, hW, fctr, fcoin, fdata, h⟩

/-- The checked identity copy of the complete transfer payload (`0x4e78 → 0x4e94`). -/
theorem wdx_xfer_copy {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {M : Mem} {img : Bytes} {G : Nat} (hcode : sevm.code = code)
    (k : Fin 3) (coin fees : B256) (hid : IdReady sevm b)
    (hctr : Region img 0x140 (Nat.toB256 ↑k).toBytes)
    (hcoin : Region img 0x160 coin.toBytes)
    (hdata : Region img 0x300 ((0x44 : B256).toBytes ++
      (transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes)))
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x4e78
      (St b [Bytes.toB256 [3, 0], Bytes.toB256 [3], Bytes.toB256 [1, 0x40]] M G) L) :
    ∃ b' M' img' G', BaseRel b b' ∧ Mem.Reads M' img' ∧ Mem.Wf M' ∧
      Region img' 0x140 (Nat.toB256 ↑k).toBytes ∧
      Region img' 0x160 coin.toBytes ∧
      Region img' 0x3a0 ((0x44 : B256).toBytes ++
        (transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes)) ∧
      XAt sevm post 0x4e94
        (St b' [Bytes.toB256 [3], Bytes.toB256 [1, 0x40]] M' G') L := by
  xs 0x4e79 (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x4e7a (.reg .mload) (ri_mload_imgAt (o := 0x300) rfl)
  rw [hdata.left.read (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4e7c (.push [0x20] (by decide)) ri_push
  xs 0x4e7d (.reg .add) ri_add
  xs 0x4e7e (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4e81 (.push [3, 0xa0] (by decide)) ri_push
  xs 0x4e82 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x4e83 (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x4e85 (.push [0] (by decide)) ri_push
  xs 0x4e87 (.push [4] (by decide)) ri_push
  xs 0x4e88 (.reg .gas) ri_gas_remaining
  replace h := xa_identity_img (pc' := 0x4e89) (i := 0x300) (n := 0x64)
    (o := 0x3a0) (z := 0x64) hid (atN hcode (by kernel_rfl)) rfl
    (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, L', h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b', G', M', hsha, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x4e8c (.push [0x4e, 0x91] (by decide)) ri_push
    xji 0x4e8d 0x4e91 hw
    · xdead
    · exact absurd rfl hw
  have copied := hdata.copy (n := 0x64) (z := 0x64) (by simp only [List.length_append, B256.length_toBytes, transferSel,
    List.length_cons, List.length_nil]) (by simp only [List.length_append, B256.length_toBytes,
    transferSel, List.length_cons, List.length_nil])
  rw [copied] at hR
  have hbase : BaseRel b b' :=
    ⟨hsha.stor, hsha.code, hsha.addrs, hsha.logs, hsha.output, hsha.error⟩
  obtain ⟨img', hR, hI⟩ := Mem.Reads.forget hR
  have fctr : Region img' 0x140 (Nat.toB256 ↑k).toBytes := by rw [hI]; wchainT; exact hctr
  have fcoin : Region img' 0x160 coin.toBytes := by rw [hI]; wchainT; exact hcoin
  have fdata : Region img' 0x3a0 ((0x44 : B256).toBytes ++
      (transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes)) := by
    rw [hI]; exact Region.write_self _ _ _
  xs 0x4e8c (.push [0x4e, 0x91] (by decide)) ri_push
  xji 0x4e8d 0x4e91 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x4e92
  xs 0x4e93 (.reg .pop) ri_pop
  xs 0x4e94 (.reg .pop) ri_pop
  exact ⟨b', M', img', _, hbase, hR, hW, fctr, fcoin, fdata, h⟩

/-- The actual transfer CALL and its successful flag (`0x4e94 → 0x4eb1`). -/
theorem wdx_xfer_call {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {M : Mem} {img : Bytes} {G : Nat} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (coin fees : B256)
    (hcoinR : Region img 0x160 coin.toBytes)
    (hdata : Region img 0x3a0 ((0x44 : B256).toBytes ++
      (transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes)))
    (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hcoin : ¬ sevm.benvStat.rules.isPrecomp coin.toAdr)
    (hpc : b.getCode sevm.currentTarget ≠ .empty) (hK : CallKeeps sevm coin)
    (h : XAt sevm post 0x4e94
      (St b [Bytes.toB256 [3], Bytes.toB256 [1, 0x40]] M G) L) :
    ∃ c L' d G', L = c :: L' ∧
      ChildOf b d coin.toAdr (transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes)
        0 sevm.isStatic c ∧
      ((∀ x, (c.post.getStor sevm.currentTarget).get x =
        (c.pre.getStor sevm.currentTarget).get x) ∧ c.post.getCode 4 = c.pre.getCode 4) ∧
      Mem.Reads d.memory (Bytes.writeAt img 0x460 (d.returnData.take 32)) ∧
      Mem.Wf d.memory ∧ d.returnData.length < 2 ^ 256 ∧
      XAt sevm post 0x4eb1
        (St d [Bytes.toB256 [3], Bytes.toB256 [1, 0x40]] d.memory G') L' := by
  xs 0x4e96 (.push [0x20] (by decide)) ri_push
  xs 0x4e99 (.push [4, 0x60] (by decide)) ri_push
  xs 0x4e9c (.push [3, 0xa0] (by decide)) ri_push
  xmo 0x4e9d (.reg .mload) (ri_mload_imgAt (o := 0x3a0) rfl)
  rw [hdata.left.read (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4ea0 (.push [3, 0xc0] (by decide)) ri_push
  xs 0x4ea2 (.push [0] (by decide)) ri_push
  xs 0x4ea5 (.push [1, 0x60] (by decide)) ri_push
  xmo 0x4ea6 (.reg .mload) (ri_mload_imgAt (o := 0x160) rfl)
  rw [hcoinR.read (B256.length_toBytes _), B256.toB256_toBytes] at h
  xs 0x4ea7 (.reg .gas) ri_gas_remaining
  have hin : img.sliceD 0x3c0 0x44 0 =
      transferSel ++ sevm.caller.toB256.toBytes ++ fees.toBytes := by
    refine Region.slice hdata.right ?_
    simp only [List.length_append, B256.length_toBytes, transferSel,
      List.length_cons, List.length_nil]
  replace h := xa_call_img (pc' := 0x4ea8) (i := 0x3c0) (n := 0x44)
    (o := 0x460) (z := 0x20) hfork (atN hcode (by kernel_rfl)) rfl
    (by decide) (by decide) (by decide) (by decide) hR hW h
  clear hR hW
  obtain ⟨d, flag, L', h, hrun, hrd, hk⟩ := h
  obtain ⟨hks, hk4⟩ := hK _ _ _ _ _ _ _ _ _ rfl hrun
  rw [hin] at hk
  xs 0x4eab (.push [0x4e, 0xb0] (by decide)) ri_push
  xji 0x4eac 0x4eb0 hw
  · xdead
  obtain ⟨hR, hW, hout, hch⟩ := hk hw
  rcases hch with ⟨hp, -⟩ | ⟨c, rfl, -, -, hc⟩
  · exact absurd hp hcoin
  xjd 0x4eb1
  rw [zero_lit] at hc
  refine ⟨c, L', d, _, rfl, ?_, hc.keeps hpc hks hk4, hR, hW, hrd, h⟩
  exact hc.congr_left (fun _ => rfl) (fun _ => rfl) rfl rfl rfl

/-- The transfer reply passes the deployed raw-call check (`0x4eb1 → 0x4f3c`). -/
theorem wdx_xfer_tail {sevm : Sevm} {post d : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} (hcode : sevm.code = code) (hid : IdReady sevm d)
    (hR : Mem.Reads M (Bytes.writeAt img 0x460 (d.returnData.take 0x20))) (hW : Mem.Wf M)
    (hrd : d.returnData.length < 2 ^ 256)
    (h : XAt sevm post 0x4eb1 (St d [3, 0x140] M G) L) :
    RawCallOk d.returnData ∧ ∃ b6 M6 img6 G7, BaseRel d b6 ∧ Mem.Reads M6 img6 ∧ Mem.Wf M6 ∧
      (∀ o w, WordAt img o w → (o + 32 ≤ 0x240 ∨ 0x280 ≤ o) →
        (o + 32 ≤ 0x440 ∨ 0x480 ≤ o) → WordAt img6 o w) ∧
      XAt sevm post 0x4f3c (St b6 [3, 0x140] M6 G7) L := by
  have hj : ∃ nW G5, nW.toNat = (d.returnData.take 32).length ∧
      XAt sevm post 0x4ec4 (St d (nW :: d.returnData.length.toB256 :: Bytes.toB256 [0x20] ::
        [3, 0x140]) M G5) L := by
    xs 0x4eb3 (.push [0x20] (by decide)) ri_push
    xs 0x4eb4 (.reg .returndatasize) ri_returndatasize
    xs 0x4eb5 (.reg (.dup 0)) (ri_dup (by rfl))
    xs 0x4eb6 (.reg (.dup 2)) (ri_dup (by rfl))
    xs 0x4eb7 (.reg .gt) ri_gt
    xs 0x4eb8 (.reg .iszero) ri_iszero
    xs 0x4ebb (.push [0x4e, 0xc1] (by decide)) ri_push
    xji 0x4ebc 0x4ec1 hw
    · xs 0x4ebd (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x4ec0 (.push [0x4e, 0xc3] (by decide)) ri_push
      xjmp 0x4ec3
      xjd 0x4ec4
      refine ⟨_, _, ?_, h⟩
      have hlt := gtCheck_ne_zero (eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hlt
      rw [List.length_take, B256.toNat_toB256_of_lt hrd]
      omega
    · xjd 0x4ec2
      xs 0x4ec3 (.reg (.dup 1)) (ri_dup (by rfl))
      xjd 0x4ec4
      refine ⟨_, _, ?_, h⟩
      have hge := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrd,
        show (Bytes.toB256 [0x20]).toNat = 32 by decide] at hge
      rw [List.length_take, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
      omega
  obtain ⟨nW, G5, hn, h⟩ := hj
  xs 0x4ec5 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x4ec6 (.reg .pop) ri_pop
  xs 0x4ec7 (.reg (.swap 0)) (ri_swap (by rfl))
  xs 0x4ec8 (.reg .pop) ri_pop
  xs 0x4ecb (.push [0x4, 0x40] (by decide)) ri_push
  xmo 0x4ecc (.reg .mstore) (ri_mstore_imgAt (o := 0x440) rfl)
  xs 0x4ecf (.push [0x4, 0x40] (by decide)) ri_push
  xs 0x4ed0 (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x4ed1 (.reg .mload) (ri_mload_imgAt (o := 0x440) rfl)
  rw [(WordAt.write_self _ _ _).read] at h
  xs 0x4ed3 (.push [0x20] (by decide)) ri_push
  xs 0x4ed4 (.reg .add) ri_add
  xs 0x4ed5 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x4ed8 (.push [0x2, 0x40] (by decide)) ri_push
  xs 0x4ed9 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x4eda (.reg (.dup 4)) (ri_dup (by rfl))
  xs 0x4edc (.push [0x0] (by decide)) ri_push
  xs 0x4ede (.push [0x4] (by decide)) ri_push
  xs 0x4edf (.reg .gas) ri_gas_remaining
  have hn32 : (d.returnData.take 32).length ≤ 32 := by rw [List.length_take]; omega
  have hsz : (Bytes.toB256 [0x20] + nW).toNat = 32 + (d.returnData.take 32).length := by
    rw [B256.toNat_add, hn, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  replace h := xa_identity_img (pc' := 0x4ee0) (i := 0x440) (n := 32 + (d.returnData.take 32).length)
    (o := 0x240) (z := 32 + (d.returnData.take 32).length) hid
    (atN hcode (by kernel_rfl)) rfl (by decide) hsz (by decide) hsz hR hW h
  clear hR hW
  obtain ⟨d, L5, h, hk⟩ := h
  rcases hk with ⟨h0, -⟩ | ⟨rfl, b6, G6, M, hsha3, rfl, hR, hW⟩
  · rw [St.self h0 rfl] at h
    xs 0x4ee3 (.push [0x4e, 0xe8] (by decide)) ri_push
    xji 0x4ee4 0x4ee8 hw
    · xdead
    · exact absurd rfl hw
  have r5 : Region (Bytes.writeAt (Bytes.writeAt img 0x460 (d.returnData.take 32)) 0x440
      nW.toBytes) 0x440 (nW.toBytes ++ d.returnData.take 32) :=
    Region.append' (o' := 0x460) (Region.write_self _ _ _)
      (Region.write_other (Region.write_self _ _ _) (by simp only [B256.length_toBytes]; omega))
      (by simp only [B256.length_toBytes])
  rw [Region.copy r5 (by simp only [List.length_append, B256.length_toBytes])
    (by simp only [List.length_append, B256.length_toBytes])] at hR
  have hb46 : BaseRel d b6 :=
    ⟨hsha3.stor, hsha3.code, hsha3.addrs, hsha3.logs, hsha3.output, hsha3.error⟩
  clear hsha3 r5
  have e6 := Mem.Reads.forget hR
  clear hR
  obtain ⟨img6, hR, hI⟩ := e6
  have k_keep : ∀ o w, WordAt img o w → (o + 32 ≤ 0x240 ∨ 0x280 ≤ o) →
      (o + 32 ≤ 0x440 ∨ 0x480 ≤ o) → WordAt img6 o w := by
    intro o w hw h1 h2
    rw [hI]
    refine WordAt.write_other (WordAt.write_other (WordAt.write_other hw ?_) ?_) ?_ <;>
      simp only [B256.length_toBytes, List.length_take, List.length_append] <;> omega
  have k_buf : Region img6 0x240 (nW.toBytes ++ d.returnData.take 32) := by
    rw [hI]; exact Region.write_self _ _ _
  clear hI
  xs 0x4ee3 (.push [0x4e, 0xe8] (by decide)) ri_push
  xji 0x4ee4 0x4ee8 hw
  · exact absurd hw (by decide)
  clear hw
  xjd 0x4ee9
  xs 0x4eea (.reg .pop) ri_pop
  xs 0x4eeb (.reg .pop) ri_pop
  have kr : Region img6 0x260 (d.returnData.take 32) := by
    have := k_buf.right; rwa [B256.length_toBytes] at this
  have kn : WordAt img6 0x240 nW := Region.word k_buf.left
  have hj2 : RawCallOk d.returnData ∧ ∃ M7 G7, Mem.Reads M7 img6 ∧ Mem.Wf M7 ∧
      XAt sevm post 0x4f3c (St b6 [3, 0x140] M7 G7) L := by
    xs 0x4eed (.push [0x0] (by decide)) ri_push
    xs 0x4ef0 (.push [0x2, 0x40] (by decide)) ri_push
    xmo 0x4ef1 (.reg .mload) (ri_mload_imgAt (o := 0x240) rfl)
    rw [kn.read] at h
    xs 0x4ef2 (.reg .gt) ri_gt
    xs 0x4ef3 (.reg .iszero) ri_iszero
    xs 0x4ef6 (.push [0x4f, 0x3b] (by decide)) ri_push
    xji 0x4ef7 0x4f3b hw
    · have hpos := gtCheck_ne_zero (eqCheck_eq_zero hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x0]).toNat = 0 by decide] at hpos
      clear hw
      xs 0x4efa (.push [0x2, 0x40] (by decide)) ri_push
      xs 0x4efb (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x4efd (.push [0x20] (by decide)) ri_push
      xs 0x4efe (.reg .add) ri_add
      xmo 0x4eff (.reg .mload) (ri_mload_imgAt (o := 0x260) (by decide))
      xs 0x4f01 (.push [0x0] (by decide)) ri_push
      xs 0x4f02 (.reg (.dup 2)) (ri_dup (by rfl))
      xmo 0x4f03 (.reg .mload) (ri_mload_imgAt (o := 0x240) rfl)
      rw [kn.read] at h
      xs 0x4f04 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x4f06 (.push [0x20] (by decide)) ri_push
      xs 0x4f07 (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x4f08 (.reg .sgt) ri_sgt
      xs 0x4f09 (.reg .iszero) ri_iszero
      xs 0x4f0c (.push [0x4f, 0x11] (by decide)) ri_push
      xji 0x4f0d 0x4f11 hw
      · xdead
      clear hw
      xjd 0x4f12
      xs 0x4f13 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x4f14 (.reg (.swap 1)) (ri_swap (by rfl))
      xs 0x4f15 (.reg (.swap 0)) (ri_swap (by rfl))
      xs2 0x4f16 (.reg .slt) ri_slt
      xs 0x4f17 (.reg .iszero) ri_iszero
      xs 0x4f1a (.push [0x4f, 0x1f] (by decide)) ri_push
      xji 0x4f1b 0x4f1f hw
      · xdead
      clear hw
      xjd 0x4f20
      xs 0x4f21 (.reg (.dup 0)) (ri_dup (by rfl))
      xs 0x4f23 (.push [0x20] (by decide)) ri_push
      xs 0x4f24 (.reg .sub) ri_sub
      xs 0x4f27 (.push [0x1, 0x0] (by decide)) ri_push
      xs 0x4f28 (.reg .exp) ri_exp
      xs 0x4f29 (.reg (.dup 2)) (ri_dup (by rfl))
      xs 0x4f2a (.reg .div) ri_div
      xs 0x4f2b (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x4f2c (.reg .pop) ri_pop
      xs 0x4f2d (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x4f2e (.reg .pop) ri_pop
      xs 0x4f2f (.reg (.swap 0)) (ri_swap (by rfl))
      xs 0x4f30 (.reg .pop) ri_pop
      xs 0x4f31 (.reg .iszero) ri_iszero
      xs 0x4f32 (.reg .iszero) ri_iszero
      xs 0x4f35 (.push [0x4f, 0x3a] (by decide)) ri_push
      xji 0x4f36 0x4f3a hq
      · xdead
      xjd 0x4f3b
      xjd 0x4f3c
      refine ⟨.inr ?_, _, _, hR, hW, h⟩
      have hq0 := eqCheck_eq_zero (eqCheck_ne_zero_eq hq)
      have hxs : (img6.sliceD 0x260 32 0).length = 32 := List.length_sliceD _ _ _ _
      have hquot := rawCheck_quot (len := nW) (by omega) (by omega) hxs rfl
      rw [hn, kr.head (by omega)] at hquot
      rw [show d.returnData.take (min d.returnData.length 32) = d.returnData.take 32 by
        rw [Nat.min_comm, ← List.take_take, List.take_length]]
      rw [← hquot]
      exact fun e => hq0 (B256.toNat_inj _ _ (by rw [e]; rfl))
    · have hz := gtCheck_eq_zero (eqCheck_ne_zero_eq hw)
      rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x0]).toNat = 0 by decide] at hz
      xjd 0x4f3c
      refine ⟨.inl ?_, _, _, hR, hW, h⟩
      rw [List.length_take] at hn
      omega
  clear hR hW
  obtain ⟨hok, M7, G7, hR, hW, h⟩ := hj2
  exact ⟨hok, b6, M7, img6, G7, hb46, hR, hW, k_keep, h⟩
