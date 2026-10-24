import Blanc.Lift.Usdc.InitReach
import Blanc.Lift.Usdc.ImplV2.Cert
import Blanc.Lift.Usdc.ImplV2_1.Cert
import Blanc.Lift.Usdc.Impl.Cert
import Blanc.Lift.Usdc.InitReachV2
import Blanc.Lift.Usdc.InitReachV2_1
import Blanc.Lift.Usdc.InitReachV2_2

/-!
# FiatTokenV1's `initialize` as compiled into V2, V2_1 and V2_2

The three compilations of `initialize(string,string,string,uint8,address,address,address,address)`
in the V2-line implementation codes are one shape over their jump tags and table indices
(`I06Tags`), block by block (`b_<pc>_<entry>`, named after V2's blocks): the external wrapper
(`b_0541_139`: ABI decode of the three strings into memory and of the five static words), the
body (`b_177e_51`: the initialized and nonzero-address checks, the three
`string storage = string memory` stores through `StrStore.helper` over `MLOAD`, the packed
fixed-slot stores) and the owner setter (`b_416c_65`). The equations placing each code's
entries at these shapes are `rfl`.
-/

namespace Blanc.Lift.Usdc.Init06

open Jaune Blanc Blanc.Lift

section Blocks

/-- The jump tags (`t…`) and table indices (`k…`) of one compilation. -/
structure I06Tags : Type where
  t0 : UInt8 × UInt8
  t1 : UInt8 × UInt8
  t2 : UInt8 × UInt8
  t3 : UInt8 × UInt8
  t4 : UInt8 × UInt8
  t5 : UInt8 × UInt8
  t6 : UInt8 × UInt8
  t7 : UInt8 × UInt8
  t8 : UInt8 × UInt8
  t9 : UInt8 × UInt8
  t10 : UInt8 × UInt8
  t11 : UInt8 × UInt8
  k12 : Nat
  t13 : UInt8 × UInt8
  t14 : UInt8 × UInt8
  t15 : UInt8 × UInt8
  t16 : UInt8 × UInt8
  t17 : UInt8 × UInt8
  t18 : UInt8 × UInt8
  t19 : UInt8 × UInt8
  t20 : UInt8 × UInt8
  t21 : UInt8 × UInt8
  t22 : UInt8 × UInt8
  t23 : UInt8 × UInt8
  t24 : UInt8 × UInt8
  k25 : Nat
  t26 : UInt8 × UInt8
  t27 : UInt8 × UInt8
  t28 : UInt8 × UInt8
  t29 : UInt8 × UInt8
  k30 : Nat

def b_0554_139 (_ι : I06Tags) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

def b_056f_139 (_ι : I06Tags) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

def b_0581_139 (_ι : I06Tags) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

def b_05a3_139 (_ι : I06Tags) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

def b_05f6_139 (_ι : I06Tags) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

def b_0608_139 (_ι : I06Tags) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

def b_062a_139 (_ι : I06Tags) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

def b_067d_139 (_ι : I06Tags) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

def b_068f_139 (_ι : I06Tags) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

def b_06b1_139 (_ι : I06Tags) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

def b_0470_139 (_ι : I06Tags) : SFunc :=
  .dest (.last .stop)

def b_06b5_139 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg (.dup 0)) (.next (.reg (.dup
    0)) (.next (.push [0x1f] (by decide)) (.next (.reg .add) (.next (.push [0x20] (by decide))
    (.next (.reg (.dup 0)) (.next (.reg (.swap 1)) (.next (.reg .div) (.next (.reg .mul) (.next
    (.push [0x20] (by decide)) (.next (.reg .add) (.next (.push [0x40] (by decide)) (.next (.reg
    .mload) (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.push [0x40]
    (by decide)) (.next (.reg .mstore) (.next (.reg (.dup 0)) (.next (.reg (.swap 3)) (.next (.reg
    (.swap 2)) (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg
    (.dup 1)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next
    (.reg (.dup 3)) (.next (.reg (.dup 3)) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next
    (.reg (.dup 4)) (.next (.reg .calldatacopy) (.next (.push [0x00] (by decide)) (.next (.reg
    (.swap 2)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg
    (.swap 1)) (.next (.reg .mstore) (.next (.reg .pop) (.next (.reg (.swap 2)) (.next (.reg (.swap
    5)) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg (.dup 1)) (.next (.reg
    .calldataload) (.next (.push [0xff] (by decide)) (.next (.reg .and) (.next (.reg (.swap 2))
    (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1))
    (.next (.reg .add) (.next (.reg .calldataload) (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by
    decide)) (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg .and) (.next (.reg (.swap
    1)) (.next (.push [0x40] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.reg
    .calldataload) (.next (.reg (.dup 2)) (.next (.reg .and) (.next (.reg (.swap 1)) (.next (.push
    [0x60] (by decide)) (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg .calldataload) (.next
    (.reg (.dup 1)) (.next (.reg .and) (.next (.reg (.swap 1)) (.next (.push [0x80] (by decide))
    (.next (.reg .add) (.next (.reg .calldataload) (.next (.reg .and) (.next (tagPush ι.t11)
    (.callNext ι.k12 (b_0470_139
    ι))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def b_0693_139 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg (.dup 0)) (.next (.reg .calldataload) (.next (.reg (.swap 0)) (.next (.push
    [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg (.dup 4)) (.next
    (.push [0x01] (by decide)) (.next (.reg (.dup 3)) (.next (.reg .mul) (.next (.reg (.dup 4))
    (.next (.reg .add) (.next (.reg .gt) (.next (.push [0x01, 0x00, 0x00, 0x00, 0x00] (by decide))
    (.next (.reg (.dup 3)) (.next (.reg .gt) (.next (.reg .or) (.next (.reg .iszero) (.next (tagPush
    ι.t10) (.branch (b_06b1_139 ι) (b_06b5_139 ι)))))))))))))))))))))

def b_0681_139 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg (.dup 3)) (.next (.push [0x20] (by
    decide)) (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg .gt) (.next (.reg .iszero)
    (.next (tagPush ι.t9) (.branch (b_068f_139 ι) (b_0693_139 ι)))))))))))

def b_062e_139 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg (.dup 0)) (.next (.reg (.dup
    0)) (.next (.push [0x1f] (by decide)) (.next (.reg .add) (.next (.push [0x20] (by decide))
    (.next (.reg (.dup 0)) (.next (.reg (.swap 1)) (.next (.reg .div) (.next (.reg .mul) (.next
    (.push [0x20] (by decide)) (.next (.reg .add) (.next (.push [0x40] (by decide)) (.next (.reg
    .mload) (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.push [0x40]
    (by decide)) (.next (.reg .mstore) (.next (.reg (.dup 0)) (.next (.reg (.swap 3)) (.next (.reg
    (.swap 2)) (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg
    (.dup 1)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next
    (.reg (.dup 3)) (.next (.reg (.dup 3)) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next
    (.reg (.dup 4)) (.next (.reg .calldatacopy) (.next (.push [0x00] (by decide)) (.next (.reg
    (.swap 2)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg
    (.swap 1)) (.next (.reg .mstore) (.next (.reg .pop) (.next (.reg (.swap 2)) (.next (.reg (.swap
    5)) (.next (.reg (.swap 4)) (.next (.reg (.swap 3)) (.next (.push [0x20] (by decide)) (.next
    (.reg (.dup 1)) (.next (.reg .add) (.next (.reg (.swap 3)) (.next (.reg .pop) (.next (.reg
    .calldataload) (.next (.reg (.swap 1)) (.next (.reg .pop) (.next (.reg .pop) (.next (.push
    [0x01, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .gt) (.next
    (.reg .iszero) (.next (tagPush ι.t8) (.branch (b_067d_139 ι) (b_0681_139
    ι))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def b_060c_139 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg (.dup 0)) (.next (.reg .calldataload) (.next (.reg (.swap 0)) (.next (.push
    [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg (.dup 4)) (.next
    (.push [0x01] (by decide)) (.next (.reg (.dup 3)) (.next (.reg .mul) (.next (.reg (.dup 4))
    (.next (.reg .add) (.next (.reg .gt) (.next (.push [0x01, 0x00, 0x00, 0x00, 0x00] (by decide))
    (.next (.reg (.dup 3)) (.next (.reg .gt) (.next (.reg .or) (.next (.reg .iszero) (.next (tagPush
    ι.t7) (.branch (b_062a_139 ι) (b_062e_139 ι)))))))))))))))))))))

def b_05fa_139 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg (.dup 3)) (.next (.push [0x20] (by
    decide)) (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg .gt) (.next (.reg .iszero)
    (.next (tagPush ι.t6) (.branch (b_0608_139 ι) (b_060c_139 ι)))))))))))

def b_05a7_139 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg (.dup 0)) (.next (.reg (.dup
    0)) (.next (.push [0x1f] (by decide)) (.next (.reg .add) (.next (.push [0x20] (by decide))
    (.next (.reg (.dup 0)) (.next (.reg (.swap 1)) (.next (.reg .div) (.next (.reg .mul) (.next
    (.push [0x20] (by decide)) (.next (.reg .add) (.next (.push [0x40] (by decide)) (.next (.reg
    .mload) (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.push [0x40]
    (by decide)) (.next (.reg .mstore) (.next (.reg (.dup 0)) (.next (.reg (.swap 3)) (.next (.reg
    (.swap 2)) (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg
    (.dup 1)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next
    (.reg (.dup 3)) (.next (.reg (.dup 3)) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next
    (.reg (.dup 4)) (.next (.reg .calldatacopy) (.next (.push [0x00] (by decide)) (.next (.reg
    (.swap 2)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg
    (.swap 1)) (.next (.reg .mstore) (.next (.reg .pop) (.next (.reg (.swap 2)) (.next (.reg (.swap
    5)) (.next (.reg (.swap 4)) (.next (.reg (.swap 3)) (.next (.push [0x20] (by decide)) (.next
    (.reg (.dup 1)) (.next (.reg .add) (.next (.reg (.swap 3)) (.next (.reg .pop) (.next (.reg
    .calldataload) (.next (.reg (.swap 1)) (.next (.reg .pop) (.next (.reg .pop) (.next (.push
    [0x01, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .gt) (.next
    (.reg .iszero) (.next (tagPush ι.t5) (.branch (b_05f6_139 ι) (b_05fa_139
    ι))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def b_0585_139 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg (.dup 0)) (.next (.reg .calldataload) (.next (.reg (.swap 0)) (.next (.push
    [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg (.dup 4)) (.next
    (.push [0x01] (by decide)) (.next (.reg (.dup 3)) (.next (.reg .mul) (.next (.reg (.dup 4))
    (.next (.reg .add) (.next (.reg .gt) (.next (.push [0x01, 0x00, 0x00, 0x00, 0x00] (by decide))
    (.next (.reg (.dup 3)) (.next (.reg .gt) (.next (.reg .or) (.next (.reg .iszero) (.next (tagPush
    ι.t4) (.branch (b_05a3_139 ι) (b_05a7_139 ι)))))))))))))))))))))

def b_0573_139 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg (.dup 3)) (.next (.push [0x20] (by
    decide)) (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg .gt) (.next (.reg .iszero)
    (.next (tagPush ι.t3) (.branch (b_0581_139 ι) (b_0585_139 ι)))))))))))

def b_0558_139 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.push [0x20] (by
    decide)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.reg (.dup 1)) (.next (.reg
    .calldataload) (.next (.push [0x01, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg (.dup 1))
    (.next (.reg .gt) (.next (.reg .iszero) (.next (tagPush ι.t2) (.branch (b_056f_139 ι)
    (b_0573_139 ι)))))))))))))))

def b_0541_139 (ι : I06Tags) : SFunc :=
  .dest (.next (tagPush ι.t0) (.next (.push [0x04] (by decide)) (.next (.reg (.dup 0)) (.next (.reg
    .calldatasize) (.next (.reg .sub) (.next (.push [0x01, 0x00] (by decide)) (.next (.reg (.dup 1))
    (.next (.reg .lt) (.next (.reg .iszero) (.next (tagPush ι.t1) (.branch (b_0554_139 ι)
    (b_0558_139 ι))))))))))))

def b_17a2_51 (ι : I06Tags) : SFunc :=
  .next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x08, 0xc3, 0x79, 0xa0, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg
    (.dup 1)) (.next (.reg .mstore) (.next (.push [0x04] (by decide)) (.next (.reg .add) (.next
    (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [0x20] (by decide)) (.next (.reg .add)
    (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .sub) (.next (.reg (.dup 2)) (.next
    (.reg .mstore) (.next (.push [0x2a] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .mstore)
    (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (tagPush
    ι.t14) (.next (.push [0x2a] (by decide)) (.next (.reg (.swap 1)) (.next (.reg .codecopy) (.next
    (.push [0x40] (by decide)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg .pop) (.next
    (.reg .pop) (.next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next
    (.reg (.swap 1)) (.next (.reg .sub) (.next (.reg (.swap 0)) (.last
    .revert)))))))))))))))))))))))))))))))))))))

def b_180e_51 (ι : I06Tags) : SFunc :=
  .next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x08, 0xc3, 0x79, 0xa0, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg
    (.dup 1)) (.next (.reg .mstore) (.next (.push [0x04] (by decide)) (.next (.reg .add) (.next
    (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [0x20] (by decide)) (.next (.reg .add)
    (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .sub) (.next (.reg (.dup 2)) (.next
    (.reg .mstore) (.next (.push [0x2f] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .mstore)
    (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (tagPush
    ι.t16) (.next (.push [0x2f] (by decide)) (.next (.reg (.swap 1)) (.next (.reg .codecopy) (.next
    (.push [0x40] (by decide)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg .pop) (.next
    (.reg .pop) (.next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next
    (.reg (.swap 1)) (.next (.reg .sub) (.next (.reg (.swap 0)) (.last
    .revert)))))))))))))))))))))))))))))))))))))

def b_187a_51 (ι : I06Tags) : SFunc :=
  .next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x08, 0xc3, 0x79, 0xa0, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg
    (.dup 1)) (.next (.reg .mstore) (.next (.push [0x04] (by decide)) (.next (.reg .add) (.next
    (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [0x20] (by decide)) (.next (.reg .add)
    (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .sub) (.next (.reg (.dup 2)) (.next
    (.reg .mstore) (.next (.push [0x29] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .mstore)
    (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (tagPush
    ι.t18) (.next (.push [0x29] (by decide)) (.next (.reg (.swap 1)) (.next (.reg .codecopy) (.next
    (.push [0x40] (by decide)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg .pop) (.next
    (.reg .pop) (.next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next
    (.reg (.swap 1)) (.next (.reg .sub) (.next (.reg (.swap 0)) (.last
    .revert)))))))))))))))))))))))))))))))))))))

def b_18e6_51 (ι : I06Tags) : SFunc :=
  .next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x08, 0xc3, 0x79, 0xa0, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg
    (.dup 1)) (.next (.reg .mstore) (.next (.push [0x04] (by decide)) (.next (.reg .add) (.next
    (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [0x20] (by decide)) (.next (.reg .add)
    (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .sub) (.next (.reg (.dup 2)) (.next
    (.reg .mstore) (.next (.push [0x2e] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .mstore)
    (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (tagPush
    ι.t20) (.next (.push [0x2e] (by decide)) (.next (.reg (.swap 1)) (.next (.reg .codecopy) (.next
    (.push [0x40] (by decide)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg .pop) (.next
    (.reg .pop) (.next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next
    (.reg (.swap 1)) (.next (.reg .sub) (.next (.reg (.swap 0)) (.last
    .revert)))))))))))))))))))))))))))))))))))))

def b_1952_51 (ι : I06Tags) : SFunc :=
  .next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x08, 0xc3, 0x79, 0xa0, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg
    (.dup 1)) (.next (.reg .mstore) (.next (.push [0x04] (by decide)) (.next (.reg .add) (.next
    (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [0x20] (by decide)) (.next (.reg .add)
    (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .sub) (.next (.reg (.dup 2)) (.next
    (.reg .mstore) (.next (.push [0x28] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .mstore)
    (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (tagPush
    ι.t22) (.next (.push [0x28] (by decide)) (.next (.reg (.swap 1)) (.next (.reg .codecopy) (.next
    (.push [0x40] (by decide)) (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.reg .pop) (.next
    (.reg .pop) (.next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 0)) (.next
    (.reg (.swap 1)) (.next (.reg .sub) (.next (.reg (.swap 0)) (.last
    .revert)))))))))))))))))))))))))))))))))))))

def b_1a77_51 (_ι : I06Tags) : SFunc :=
  .dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x08] (by decide)) (.next (.reg (.dup
    0)) (.next (.reg .sload) (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg .and) (.next (.push [0x01,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg .or) (.next (.reg (.swap 0)) (.next (.reg
    .sstore) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop) (.next
    (.reg .pop) (.next (.reg .pop) .ret)))))))))))))))))

def b_19dd_51 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg .pop) (.next (.push [0x06] (by decide)) (.next (.reg (.dup 0)) (.next (.reg
    .sload) (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0x00] (by decide)) (.next (.reg .and) (.next (.push [0xff] (by decide)) (.next
    (.reg (.dup 7)) (.next (.reg .and) (.next (.reg .or) (.next (.reg (.swap 0)) (.next (.reg
    .sstore) (.next (.push [0x08] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .sload) (.next
    (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00] (by decide)) (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.reg .and)
    (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg (.dup 7)) (.next (.reg (.dup
    1)) (.next (.reg .and) (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg (.swap 1))
    (.next (.reg .or) (.next (.reg (.swap 0)) (.next (.reg (.swap 2)) (.next (.reg .sstore) (.next
    (.push [0x01] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .sload) (.next (.reg (.dup 2))
    (.next (.reg .and) (.next (.reg (.dup 6)) (.next (.reg (.dup 4)) (.next (.reg .and) (.next (.reg
    .or) (.next (.reg (.swap 0)) (.next (.reg .sstore) (.next (.push [0x02] (by decide)) (.next
    (.reg (.dup 0)) (.next (.reg .sload) (.next (.reg (.swap 0)) (.next (.reg (.swap 1)) (.next
    (.reg .and) (.next (.reg (.swap 1)) (.next (.reg (.dup 4)) (.next (.reg .and) (.next (.reg
    (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg (.swap 1)) (.next (.reg .or) (.next (.reg (.swap
    0)) (.next (.reg .sstore) (.next (tagPush ι.t28) (.next (.reg (.dup 1)) (.next (tagPush ι.t29)
    (.callNext ι.k30 (b_1a77_51 ι)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def b_19c9_51 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg .pop) (.next (.reg (.dup 5)) (.next (.reg .mload) (.next (tagPush ι.t27) (.next
    (.reg (.swap 0)) (.next (.push [0x07] (by decide)) (.next (.reg (.swap 0)) (.next (.push [0x20]
    (by decide)) (.next (.reg (.dup 9)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (tagPush
    ι.t24) (.callNext ι.k25 (b_19dd_51 ι))))))))))))))

def b_19b5_51 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg .pop) (.next (.reg (.dup 6)) (.next (.reg .mload) (.next (tagPush ι.t26) (.next
    (.reg (.swap 0)) (.next (.push [0x05] (by decide)) (.next (.reg (.swap 0)) (.next (.push [0x20]
    (by decide)) (.next (.reg (.dup 10)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (tagPush
    ι.t24) (.callNext ι.k25 (b_19c9_51 ι))))))))))))))

def b_19a2_51 (ι : I06Tags) : SFunc :=
  .dest (.next (.reg (.dup 7)) (.next (.reg .mload) (.next (tagPush ι.t23) (.next (.reg (.swap 0))
    (.next (.push [0x04] (by decide)) (.next (.reg (.swap 0)) (.next (.push [0x20] (by decide))
    (.next (.reg (.dup 11)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (tagPush ι.t24)
    (.callNext ι.k25 (b_19b5_51 ι)))))))))))))

def b_1936_51 (ι : I06Tags) : SFunc :=
  .dest (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .and)
    (.next (tagPush ι.t21) (.branch (b_1952_51 ι) (b_19a2_51 ι))))))

def b_18ca_51 (ι : I06Tags) : SFunc :=
  .dest (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg (.dup 2)) (.next (.reg .and)
    (.next (tagPush ι.t19) (.branch (b_18e6_51 ι) (b_1936_51 ι))))))

def b_185e_51 (ι : I06Tags) : SFunc :=
  .dest (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg (.dup 3)) (.next (.reg .and)
    (.next (tagPush ι.t17) (.branch (b_187a_51 ι) (b_18ca_51 ι))))))

def b_17f2_51 (ι : I06Tags) : SFunc :=
  .dest (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg (.dup 4)) (.next (.reg .and)
    (.next (tagPush ι.t15) (.branch (b_180e_51 ι) (b_185e_51 ι))))))

def b_177e_51 (ι : I06Tags) : SFunc :=
  .dest (.next (.push [0x08] (by decide)) (.next (.reg .sload) (.next (.push [0x01, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00] (by decide)) (.next (.reg (.swap 0)) (.next (.reg .div) (.next (.push [0xff] (by
    decide)) (.next (.reg .and) (.next (.reg .iszero) (.next (tagPush ι.t13) (.branch (b_17a2_51 ι)
    (b_17f2_51 ι)))))))))))

def b_416c_65 (_ι : I06Tags) : SFunc :=
  .dest (.next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .sload) (.next (.push
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    (by decide)) (.next (.reg .and) (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next
    (.reg (.swap 2)) (.next (.reg (.swap 0)) (.next (.reg (.swap 2)) (.next (.reg .and) (.next (.reg
    (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg (.swap 1)) (.next (.reg .or) (.next (.reg (.swap
    0)) (.next (.reg .sstore) .ret))))))))))))))))

def ιV2 : I06Tags :=
  ⟨(0x04, 0x70), (0x05, 0x58), (0x05, 0x73), (0x05, 0x85), (0x05, 0xa7), (0x05, 0xfa), (0x06, 0x0c),
    (0x06, 0x2e), (0x06, 0x81), (0x06, 0x93), (0x06, 0xb5), (0x17, 0x7e), 51, (0x17, 0xf2), (0x57,
    0xfe), (0x18, 0x5e), (0x57, 0x55), (0x18, 0xca), (0x56, 0x17), (0x19, 0x36), (0x57, 0xd0),
    (0x19, 0xa2), (0x59, 0x3d), (0x19, 0xb5), (0x53, 0xc7), 80, (0x19, 0xc9), (0x19, 0xdd), (0x1a,
    0x77), (0x41, 0x6c), 65⟩

def ιV2_1 : I06Tags :=
  ⟨(0x04, 0x52), (0x05, 0x6d), (0x05, 0x88), (0x05, 0x9a), (0x05, 0xbc), (0x06, 0x0f), (0x06, 0x21),
    (0x06, 0x43), (0x06, 0x96), (0x06, 0xa8), (0x06, 0xca), (0x16, 0xf4), 52, (0x17, 0x68), (0x51,
    0xac), (0x17, 0xd4), (0x50, 0xde), (0x18, 0x40), (0x4f, 0xa0), (0x18, 0xac), (0x51, 0x59),
    (0x19, 0x18), (0x52, 0xbf), (0x19, 0x2b), (0x4d, 0x50), 78, (0x19, 0x3f), (0x19, 0x53), (0x19,
    0xed), (0x3d, 0x95), 68⟩

def ιV2_2 : I06Tags :=
  ⟨(0x04, 0x89), (0x05, 0xa4), (0x05, 0xbf), (0x05, 0xd1), (0x05, 0xf3), (0x06, 0x46), (0x06, 0x58),
    (0x06, 0x7a), (0x06, 0xcd), (0x06, 0xdf), (0x07, 0x01), (0x19, 0xe1), 61, (0x1a, 0x55), (0x59,
    0x8f), (0x1a, 0xc1), (0x58, 0xc1), (0x1b, 0x2d), (0x57, 0x34), (0x1b, 0x99), (0x59, 0x3c),
    (0x1c, 0x05), (0x5a, 0x7c), (0x1c, 0x18), (0x54, 0xcd), 103, (0x1c, 0x2c), (0x1c, 0x40), (0x1c,
    0xda), (0x42, 0x2f), 85⟩

end Blocks

/-- The `string storage = string memory` helper of each compilation. -/
def τV2 : StrTags := ⟨(0x54, 0x08), (0x54, 0x35), (0x54, 0x1a), (0x54, 0x41), (0x54, 0xd1),
  (0x54, 0xd2), 8, 90, 64, 82⟩

def τV2_1 : StrTags := ⟨(0x4d, 0x91), (0x4d, 0xbe), (0x4d, 0xa3), (0x4d, 0xca), (0x4e, 0x5a),
  (0x4e, 0x5b), 9, 88, 66, 81⟩

def τV2_2 : StrTags := ⟨(0x55, 0x0e), (0x55, 0x3b), (0x55, 0x20), (0x55, 0x47), (0x55, 0xd7),
  (0x55, 0xd8), 14, 116, 82, 108⟩

theorem helper_V2 : ImplV2.cert.prog[80]? =
    some (StrStore.helper τV2 (.reg .mload) (StrStore.shortMem τV2)) := rfl
theorem entries_V2 : StrStore.Entries τV2 (.reg .mload) ImplV2.cert.prog := ⟨rfl, rfl, rfl, rfl⟩
theorem helper_V2_1 : ImplV2_1.cert.prog[78]? =
    some (StrStore.helper τV2_1 (.reg .mload) (StrStore.shortMem τV2_1)) := rfl
theorem entries_V2_1 : StrStore.Entries τV2_1 (.reg .mload) ImplV2_1.cert.prog :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem helper_V2_2 : Impl.cert.prog[103]? =
    some (StrStore.helper τV2_2 (.reg .mload) (StrStore.shortMem τV2_2)) := rfl
theorem entries_V2_2 : StrStore.Entries τV2_2 (.reg .mload) Impl.cert.prog := ⟨rfl, rfl, rfl, rfl⟩

theorem wrap_V2 : ImplV2.cert.prog[139]? = some (b_0541_139 ιV2) := by decide +kernel
theorem body_V2 : ImplV2.cert.prog[51]? = some (b_177e_51 ιV2) := by decide +kernel
theorem owner_V2 : ImplV2.cert.prog[65]? = some (b_416c_65 ιV2) := by decide +kernel
theorem wrap_V2_1 : ImplV2_1.cert.prog[136]? = some (b_0541_139 ιV2_1) := by decide +kernel
theorem body_V2_1 : ImplV2_1.cert.prog[52]? = some (b_177e_51 ιV2_1) := by decide +kernel
theorem owner_V2_1 : ImplV2_1.cert.prog[68]? = some (b_416c_65 ιV2_1) := by decide +kernel
theorem wrap_V2_2 : Impl.cert.prog[168]? = some (b_0541_139 ιV2_2) := by decide +kernel
theorem body_V2_2 : Impl.cert.prog[61]? = some (b_177e_51 ιV2_2) := by decide +kernel
theorem owner_V2_2 : Impl.cert.prog[85]? = some (b_416c_65 ιV2_2) := by decide +kernel

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {T : Conf}

/-- A word kept by a callee that only wrote the scratch word at `0` and grew memory. -/
theorem memWord_keeps_scratch {M M' : Mem} {x : B256} {o : Nat}
    (h : SolcStorageReturn.Keeps (M.write 0 x.toBytes) M') (ho : 32 ≤ o) (hs : o + 32 ≤ M.size) :
    memWord M' o = memWord M o := by
  have e : memWord M' o = memWord (M.write 0 x.toBytes) o := by
    unfold memWord Mem.read
    rw [h.1]
  rw [e, memWord_write_far hs (by rw [B256.length_toBytes]; omega)]

/-- The keys FiatTokenV1's `initialize` writes: its fixed slots and the payload words of its
three decoded strings (lengths `L1`, `L2`, `L3`) at slots `4`, `5`, `7`. -/
def KeysInit (L1 L2 L3 : Nat) (key : B256) : Prop :=
  key ∈ ([0, 1, 2, 4, 5, 6, 7, 8] : List B256) ∨
    (∃ j : Nat, j < (L1 + 31) / 32 ∧ key = (4 : B256).toBytes.keccak + j.toB256) ∨
    (∃ j : Nat, j < (L2 + 31) / 32 ∧ key = (5 : B256).toBytes.keccak + j.toB256) ∨
    (∃ j : Nat, j < (L3 + 31) / 32 ∧ key = (7 : B256).toBytes.keccak + j.toB256)

/-- One `string storage = string memory` call of the body: the helper stores the slot, zero,
or a payload word of the string whose header is at `p`, or returns the slot with every word but
the scratch word kept. -/
theorem helper06_call {Q : Sevm → Devm → Ninst → Devm → Prop}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d') {τ : StrTags} {kh : Nat}
    (hh : fs[kh]? = some (StrStore.helper τ (.reg .mload) (StrStore.shortMem τ)))
    (E : StrStore.Entries τ (.reg .mload) fs) {k : SFunc} {b : Devm} {t p slot r : B256}
    {B : List B256} {M : Mem} {G : Nat} {L : B256} (hL : memWord M p.toNat = L)
    (hp : p.toNat + 32 < 2 ^ 256)
    (run : Reach (FreePtr.PotStep Q) fs sevm ⟨St b (t :: (M.read p.toNat 32).1.toB256 ::
      (p + Bytes.toB256 [32]) :: slot :: r :: B) (M.read p.toNat 32).2 G, .callNext kh k, []⟩ T)
    (hT : AtSstore T) :
    StrStore.StoreAt slot ((L.toNat + 31) / 32) T ∨ ∃ b' M' G',
      SolcStorageReturn.Keeps ((M.read p.toNat 32).2.write 0 slot.toBytes) M' ∧
      Reach (FreePtr.PotStep Q) fs sevm ⟨St b' (slot :: B) M' G', k, []⟩ T := by
  have erase : ∀ {s d n d'}, FreePtr.PotStep Q s d n d' → Ninst.Run s d n d' := fun h => eraseQ h.1
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  rw [hh] at hg
  cases hg
  have e1 : (M.read p.toNat 32).1.toB256 = (L.toNat).toB256 := by
    rw [toB256_toNat]
    exact hL
  have e2 : p + Bytes.toB256 [32] = (p.toNat + 32).toB256 := by
    rw [← StrStore.toB256_add, toB256_toNat]
    rfl
  rw [e1, e2] at run
  rcases StrStore.reach erase (by intro h; cases h) (ReachPayload.mload_rdStep eraseQ)
      (StrStore.shortMem_ok erase E.exit) E (by omega) (ReachPayload.mload_win eraseQ) run hT with
    st | ⟨f, K', b', M', G', hK, hk, run⟩
  · exact .inl (st.mono (StrStore.count_le _ _))
  · cases hK
    exact .inr ⟨b', M', G', hk, run⟩

theorem body06_reach {Q : Sevm → Devm → Ninst → Devm → Prop}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d') {ι : I06Tags} {τ : StrTags}
    (hh : fs[ι.k25]? = some (StrStore.helper τ (.reg .mload) (StrStore.shortMem τ)))
    (E : StrStore.Entries τ (.reg .mload) fs) (ho : fs[ι.k30]? = some (b_416c_65 ι))
    {b : Devm} {a4 a3 a2 a1 dec p3 p2 p1 r : B256} {S : List B256} {M : Mem} {G : Nat}
    {L1 L2 L3 : B256}
    (h1 : memWord M p1.toNat = L1) (h2 : memWord M p2.toNat = L2) (h3 : memWord M p3.toNat = L3)
    (q2 : 32 ≤ p2.toNat) (q3 : 32 ≤ p3.toNat)
    (s2 : p2.toNat + 32 ≤ M.size) (s3 : p3.toNat + 32 ≤ M.size)
    (b1 : p1.toNat + 32 < 2 ^ 256) (b2 : p2.toNat + 32 < 2 ^ 256) (b3 : p3.toNat + 32 < 2 ^ 256)
    (run : Reach (FreePtr.PotStep Q) fs sevm ⟨St b (a4 :: a3 :: a2 :: a1 :: dec :: p3 :: p2 :: p1 ::
      r :: S) M G, b_177e_51 ι, []⟩ T) (hT : AtSstore T) :
    InitStore (KeysInit L1.toNat L2.toNat L3.toNat) T := by
  have erase : ∀ {s d n d'}, FreePtr.PotStep Q s d n d' → Ninst.Run s d n d' := fun h => eraseQ h.1
  rsd
  rsx
  rsload
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  repeat rsa
  rcases helper06_call eraseQ hh E h1 b1 run hT with ⟨key, v, S', hs, hk | hv | ⟨j, hj, hk⟩⟩ |
    ⟨b', M', G', hk1, run⟩
  · exact InitStore.of_eq hs (.inl (.inl (by rw [hk]; decide)))
  · exact InitStore.of_eq hs (.inr hv)
  · exact InitStore.of_eq hs (.inl (.inr (.inl ⟨j, hj, by rw [hk]; rfl⟩)))
  have m1 : ∀ o, 32 ≤ o → o + 32 ≤ M.size → memWord M' o = memWord M o := fun o ho hs =>
    (memWord_keeps_scratch hk1 ho (le_trans hs (SolcStorageReturn.Keeps.read M _ _).2)).trans rfl
  rsd
  repeat rsa
  rcases helper06_call eraseQ hh E ((m1 _ q2 s2).trans h2) b2 run hT with
    ⟨key, v, S', hs, hk | hv | ⟨j, hj, hk⟩⟩ | ⟨b'', M'', G'', hk2, run⟩
  · exact InitStore.of_eq hs (.inl (.inl (by rw [hk]; decide)))
  · exact InitStore.of_eq hs (.inr hv)
  · exact InitStore.of_eq hs (.inl (.inr (.inr (.inl ⟨j, hj, by rw [hk]; rfl⟩))))
  have sz1 : M.size ≤ M'.size := le_trans (SolcStorageReturn.Keeps.read M _ _).2
    (le_trans (size_write_ge _ _ _) hk1.2)
  have m2 : ∀ o, 32 ≤ o → o + 32 ≤ M'.size → memWord M'' o = memWord M' o := fun o ho hs =>
    (memWord_keeps_scratch hk2 ho (le_trans hs (SolcStorageReturn.Keeps.read M' _ _).2)).trans rfl
  rsd
  repeat rsa
  rcases helper06_call eraseQ hh E ((m2 _ q3 (by omega)).trans ((m1 _ q3 s3).trans h3)) b3 run hT
    with ⟨key, v, S', hs, hk | hv | ⟨j, hj, hk⟩⟩ | ⟨b₃, M₃, G₃, -, run⟩
  · exact InitStore.of_eq hs (.inl (.inl (by rw [hk]; decide)))
  · exact InitStore.of_eq hs (.inr hv)
  · exact InitStore.of_eq hs (.inl (.inr (.inr (.inr ⟨j, hj, by rw [hk]; rfl⟩))))
  rsd
  repeat rsa
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact InitStore.of_top rfl (.inl (by decide))
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat rsa
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact InitStore.of_top rfl (.inl (by decide))
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat rsa
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact InitStore.of_top rfl (.inl (by decide))
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat rsa
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact InitStore.of_top rfl (.inl (by decide))
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat rsa
  obtain ⟨g, _, hg, run⟩ := rs_callIn run hT
  rw [ho] at hg
  cases hg
  repeat rsa
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact InitStore.of_top rfl (.inl (by decide))
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  obtain ⟨f, K', b₄, G₄, hK, run⟩ := rs_retM run hT
  cases hK
  repeat rsa
  rcases Reach.sstoreS run with rfl | ⟨_, hstep, run⟩
  · exact InitStore.of_top rfl (.inl (by decide))
  obtain ⟨_, _, e⟩ := SolcStorageReturn.ri_sstore_any (erase hstep)
  subst e
  clear hstep
  repeat rsa
  exact (Reach.not_ret_nilS run hT).elim

/-- The length word of the dynamic string whose head is at calldata offset `h`. -/
def len06 (sevm : Sevm) (h : B256) : Nat :=
  (Sevm.dataWord sevm (Bytes.toB256 [4] + Sevm.dataWord sevm h)).toNat

/-- The keys `initialize` writes, with the frame's three decoded string lengths. -/
def KeysInit06 (sevm : Sevm) : B256 → Prop :=
  KeysInit (len06 sevm (Bytes.toB256 [4])) (len06 sevm (Bytes.toB256 [4] + Bytes.toB256 [32]))
    (len06 sevm (Bytes.toB256 [4] + Bytes.toB256 [32] + Bytes.toB256 [32]))

/-- **The wrapper and body on a reach to an `SSTORE`.** From the dispatcher's memory (free
pointer `0x80`), a reach of the wrapper to an `SSTORE` stops at a write of `KeysInit06` or of
zero. -/
theorem wrap06_reach {Q : Sevm → Devm → Ninst → Devm → Prop}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d') {ι : I06Tags} {τ : StrTags}
    (hb : fs[ι.k12]? = some (b_177e_51 ι))
    (hh : fs[ι.k25]? = some (StrStore.helper τ (.reg .mload) (StrStore.shortMem τ)))
    (E : StrStore.Entries τ (.reg .mload) fs) (ho : fs[ι.k30]? = some (b_416c_65 ι))
    {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    (hfp : memWord M 64 = Bytes.toB256 [0x80])
    (run : Reach (FreePtr.PotStep Q) fs sevm ⟨St b S M G, b_0541_139 ι, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInit06 sevm) T := by
  have erase : ∀ {s d n d'}, FreePtr.PotStep Q s d n d' → Ninst.Run s d n d' := fun h => eraseQ h.1
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw1, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  have off1 := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hw1)
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw3, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  have len1 := toNat_le_of_gtCheck_eq_zero (CdStrWrap.or_gt_zero (eq_zero_of_iszero_ne_zero hw3))
  have big : (Bytes.toB256 [1, 0, 0, 0, 0]).toNat = 2 ^ 32 := by decide
  rw [big] at off1 len1
  have h128 : (Bytes.toB256 [0x80]).toNat = 128 := by decide
  rsd
  obtain ⟨M1, G1, A1, run⟩ := alloc06Frag_reach erase (by rw [hfp, h128]; omega)
    (by rw [hfp, h128]; omega) run hT
  have n1 := A1.next
  rw [hfp, h128] at n1
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw4, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  have off2 := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hw4)
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw6, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  have len2 := toNat_le_of_gtCheck_eq_zero (CdStrWrap.or_gt_zero (eq_zero_of_iszero_ne_zero hw6))
  rw [big] at off2 len2
  rsd
  have r1 := Nat.div_mul_le_self
    ((Sevm.dataWord sevm (Bytes.toB256 [4] + Sevm.dataWord sevm (Bytes.toB256 [4]))).toNat + 31) 32
  obtain ⟨M2, G2, A2, run⟩ := alloc06Frag_reach erase (by omega) (by omega) run hT
  have n2 := A2.next
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw7, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  have off3 := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hw7)
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  repeat rsa
  rcases rs_branch run hT with ⟨-, _, run⟩ | ⟨hw9, _, run⟩
  · exact (Reach.false_of_sstoreFree (E := []) rfl run hT rfl (fun _ h => by cases h)).elim
  have len3 := toNat_le_of_gtCheck_eq_zero (CdStrWrap.or_gt_zero (eq_zero_of_iszero_ne_zero hw9))
  rw [big] at off3 len3
  rsd
  have r2 := Nat.div_mul_le_self
    ((Sevm.dataWord sevm (Bytes.toB256 [4] + Sevm.dataWord sevm (Bytes.toB256 [4] +
      Bytes.toB256 [32]))).toNat + 31) 32
  obtain ⟨M3, G3, A3, run⟩ := alloc06Frag_reach erase (by omega) (by omega) run hT
  have n3 := A3.next
  repeat rsa
  obtain ⟨_, T', inside, rfl⟩ := rs_callInto (E := []) rfl hb rfl (fun _ h => by cases h) run hT
  have hT' : AtSstore T' := AtSstore.below.mp hT
  have f1 := A1.fit
  have f2 := A2.fit
  have f3 := A3.fit
  have g2 := A2.grow
  have g3 := A3.grow
  rw [hfp, h128] at f1
  have k12 : memWord M2 (memWord M 64).toNat = memWord M1 (memWord M 64).toNat :=
    A2.keep _ (by rw [hfp, h128]; omega) (by rw [hfp, h128]; omega) (by rw [hfp, h128]; omega)
  have k13 : memWord M3 (memWord M 64).toNat = memWord M2 (memWord M 64).toNat :=
    A3.keep _ (by rw [hfp, h128]; omega) (by rw [hfp, h128]; omega) (by rw [hfp, h128]; omega)
  have k23 : memWord M3 (memWord M1 64).toNat = memWord M2 (memWord M1 64).toNat :=
    A3.keep _ (by omega) (by omega) (by omega)
  refine InitStore.below.mpr (body06_reach eraseQ hh E ho
    (k13.trans (k12.trans A1.hdr)) (k23.trans A2.hdr) A3.hdr
    (by omega) (by omega) (by omega) (by omega)
    (by rw [hfp, h128]; omega) (by omega) (by omega) inside hT')

/-- **`initialize` from entry `0` on a reach to an `SSTORE`.** A reach of a V2-line code from
its solc 0.6 dispatcher, with empty stack and memory and the `initialize` selector, stops at a
write of `KeysInit06` or of zero. -/
theorem root06_reach {Q : Sevm → Devm → Ninst → Devm → Prop}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d') {ι : I06Tags} {τ : StrTags}
    {a c : UInt8 × UInt8} {sel : SFunc} {kW : Nat}
    (hw : sel.selWalk 0x3357162b = .inl (Bytes.toB256 [0x33, 0x57, 0x16, 0x2b], kW))
    (hwrap : fs[kW]? = some (b_0541_139 ι)) (hb : fs[ι.k12]? = some (b_177e_51 ι))
    (hh : fs[ι.k25]? = some (StrStore.helper τ (.reg .mload) (StrStore.shortMem τ)))
    (E : StrStore.Entries τ (.reg .mload) fs) (ho : fs[ι.k30]? = some (b_416c_65 ι))
    (hs : selWord sevm = 0x3357162b) {d : Devm} {G : Nat}
    (run : Reach (FreePtr.PotStep Q) fs sevm ⟨St d [] Mem.empty G, dispatch06 a c sel, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInit06 sevm) T := by
  have erase : ∀ {s d n d'}, FreePtr.PotStep Q s d n d' → Ninst.Run s d n d' := fun h => eraseQ h.1
  obtain ⟨g, b', G', hg, run⟩ := dispatch06_reach erase hs hw run hT
  rw [hwrap] at hg
  cases hg
  have w := Mem.memWord_write_word Mem.empty (Bytes.toB256 [0x40]).toNat (Bytes.toB256 [0x80])
  rw [show (Bytes.toB256 [0x40]).toNat = 64 by decide] at w run
  exact wrap06_reach eraseQ hb hh E ho w.1 run hT

theorem route_V2 : InitReachV2.selTree.selWalk 0x3357162b =
    .inl (Bytes.toB256 [0x33, 0x57, 0x16, 0x2b], 139) := by
  decide +kernel

/-- **V2 `initialize` on a prefix reach.** A reach of the V2 code from entry `0`, with empty
stack and memory and the `initialize` selector, to an `SSTORE` stops at a write of `KeysInit06`
or of zero. -/
theorem init_reach_V2 {Q : Sevm → Devm → Ninst → Devm → Prop}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    (hs : selWord sevm = 0x3357162b) {d : Devm} {G : Nat}
    (run : Reach (FreePtr.PotStep Q) ImplV2.cert.prog sevm
      ⟨St d [] Mem.empty G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInit06 sevm) T := by
  rw [InitReachV2.root_eq] at run
  exact root06_reach eraseQ route_V2 wrap_V2 body_V2 helper_V2 entries_V2 owner_V2
    hs run hT

theorem route_V2_1 : InitReachV2_1.selTree.selWalk 0x3357162b =
    .inl (Bytes.toB256 [0x33, 0x57, 0x16, 0x2b], 136) := by
  decide +kernel

/-- **V2_1 `initialize` on a prefix reach.** A reach of the V2_1 code from entry `0`, with empty
stack and memory and the `initialize` selector, to an `SSTORE` stops at a write of `KeysInit06`
or of zero. -/
theorem init_reach_V2_1 {Q : Sevm → Devm → Ninst → Devm → Prop}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    (hs : selWord sevm = 0x3357162b) {d : Devm} {G : Nat}
    (run : Reach (FreePtr.PotStep Q) ImplV2_1.cert.prog sevm
      ⟨St d [] Mem.empty G, ImplV2_1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInit06 sevm) T := by
  rw [InitReachV2_1.root_eq] at run
  exact root06_reach eraseQ route_V2_1 wrap_V2_1 body_V2_1 helper_V2_1 entries_V2_1 owner_V2_1
    hs run hT

theorem route_V2_2 : InitReachV2_2.selTree.selWalk 0x3357162b =
    .inl (Bytes.toB256 [0x33, 0x57, 0x16, 0x2b], 168) := by
  decide +kernel

/-- **V2_2 `initialize` on a prefix reach.** A reach of the V2_2 code from entry `0`, with empty
stack and memory and the `initialize` selector, to an `SSTORE` stops at a write of `KeysInit06`
or of zero. -/
theorem init_reach_V2_2 {Q : Sevm → Devm → Ninst → Devm → Prop}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    (hs : selWord sevm = 0x3357162b) {d : Devm} {G : Nat}
    (run : Reach (FreePtr.PotStep Q) Impl.cert.prog sevm
      ⟨St d [] Mem.empty G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) : InitStore (KeysInit06 sevm) T := by
  rw [InitReachV2_2.root_eq] at run
  exact root06_reach eraseQ route_V2_2 wrap_V2_2 body_V2_2 helper_V2_2 entries_V2_2 owner_V2_2
    hs run hT

end Blanc.Lift.Usdc.Init06
