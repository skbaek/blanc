import Blanc.Lift.Curve3Pool.Cert
import Blanc.Lift.VyperCheckedArith
import Blanc.Lift.CallSiteChildren

/-!
# `get_y_D`'s lifted trees, by shape

`get_y_D` (pc `0x3999`, entry 753) lifts to twenty entries: the prologue with the first coin
test, three coin-loop iterations (`0x3a1b` test, `0x3a50` accumulation, `0x3acc` counter
tail) unrolled over entries 18 … 121, the post-loop set-up at `0x3adc`, and the Newton `y`
loop at `0x3b88` duplicated by the certificate's entry cap: the first pass inline in entries
120 and 121, peeled copies 143, 165, 187 and the steady head 205, with counter tails at
`0x3c9d` (142, 164, 186, 204) and exits at `0x3cae` (141, 163, 185).

Each distinct shape is one definition here, parameterised by its goto targets and by the
subtree it continues with, and every certificate entry of the closure is one kernel equation
(`decide +kernel`) between its lookup and its shape.  The checked-arithmetic idioms appear as
`vyMulT`/`vyAddT`/`vySubT`/`vyDivT` (`Blanc/Lift/VyperCheckedArith.lean`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-- The lifted runtime program (as in `KitCheck.lean`). -/
abbrev progYD : List SFunc := Cert.prog cert


/-- The exit at `0x3cae`: `return y` (through scratch word 0 and the return slot `0x200`). -/
def ydExit : SFunc :=
  (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x03, 0x00] (by decide)) (.next
    (.reg .mload) (.next (.push [0x00] (by decide)) (.next (.reg .mstore) (.next (.push [0x00]
    (by decide)) (.next (.reg .mload) (.next (.push [0x02, 0x00] (by decide)) (.next (.reg
    .mload) .ret)))))))))))

/-- The counter tail at `0x3c9d`: `_i += 1`, back to `k` unless it reached 255, else `fall`. -/
def ydTail (k : Nat) (fall : SFunc) : SFunc :=
  (.dest (.dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide))
    (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore) (.next
    (.reg (.dup 1)) (.next (.reg .eq) (.next (.reg .iszero) (.next (.push [0x3b, 0x88] (by
    decide)) (.branchTo fall k))))))))))))))

/-- One Newton pass of the `y` loop at `0x3b88`, with exit `e`, tail `t`, head `k`. -/
def ydHead (e t k : Nat) (fall : SFunc) : SFunc :=
  (.dest (.next (.push [0x03, 0x00] (by decide)) (.next (.reg .mload) (.next (.push [0x02, 0xe0]
    (by decide)) (.next (.reg .mstore) (.next (.push [0x03, 0x00] (by decide)) (.next (.reg
    .mload) (.next (.push [0x03, 0x00] (by decide)) (.next (.reg .mload) (vyMulT 0x3b 0xac
    vyRevertT (.next (.push [0x02, 0x20] (by decide)) (.next (.reg .mload) (vyAddT 0x3b 0xc6
    vyRevertT (.next (.push [0x02] (by decide)) (.next (.push [0x03, 0x00] (by decide)) (.next
    (.reg .mload) (vyMulT 0x3b 0xe7 vyRevertT (.next (.push [0x02, 0xc0] (by decide)) (.next
    (.reg .mload) (vyAddT 0x3c 0x01 vyRevertT (.next (.push [0x01, 0xe0] (by decide)) (.next
    (.reg .mload) (vySubT 0x3c 0x19 vyRevertT (vyDivT 0x3c 0x2b vyRevertT (.next (.push [0x03,
    0x00] (by decide)) (.next (.reg .mstore) (.next (.push [0x02, 0xe0] (by decide)) (.next (.reg
    .mload) (.next (.push [0x03, 0x00] (by decide)) (.next (.reg .mload) (.next (.reg .gt) (.next
    (.reg .iszero) (.next (.push [0x3c, 0x72] (by decide)) (.branch (.next (.push [0x01] (by
    decide)) (.next (.push [0x03, 0x00] (by decide)) (.next (.reg .mload) (.next (.push [0x02,
    0xe0] (by decide)) (.next (.reg .mload) (vySubT 0x3c 0x5a vyRevertT (.next (.reg .gt) (.next
    (.reg .iszero) (.next (.reg .iszero) (.next (.push [0x3c, 0x6d] (by decide)) (.branch (.next
    (.push [0x3c, 0xae] (by decide)) (.jump e)) (.dest (.next (.push [0x3c, 0x9d] (by decide))
    (.jump t)))))))))))))) (.dest (.next (.push [0x01] (by decide)) (.next (.push [0x02, 0xe0]
    (by decide)) (.next (.reg .mload) (.next (.push [0x03, 0x00] (by decide)) (.next (.reg
    .mload) (vySubT 0x3c 0x89 vyRevertT (.next (.reg .gt) (.next (.reg .iszero) (.next (.reg
    .iszero) (.next (.push [0x3c, 0x9c] (by decide)) (.branch (.next (.push [0x3c, 0xae] (by
    decide)) (.jump e)) (.dest (ydTail k fall))))))))))))))))))))))))))))))))))))))))))))))))

/-- The prologue: arguments to the frame, the `i` range asserts, `c`, `S_`, `Ann`, `_x`, the
coin-loop counter. -/
def ydEntry (rest : SFunc) : SFunc :=
  (.dest (.next (.push [0x02, 0x00] (by decide)) (.next (.reg .mstore) (.next (.push [0x01, 0x40]
    (by decide)) (.next (.reg .mstore) (.next (.push [0x01, 0x60] (by decide)) (.next (.reg
    .mstore) (.next (.push [0x01, 0x80] (by decide)) (.next (.reg .mstore) (.next (.push [0x01,
    0xa0] (by decide)) (.next (.reg .mstore) (.next (.push [0x01, 0xc0] (by decide)) (.next (.reg
    .mstore) (.next (.push [0x01, 0xe0] (by decide)) (.next (.reg .mstore) (.next (.push [0x00]
    (by decide)) (.next (.push [0x01, 0x60] (by decide)) (.next (.reg .mload) (.next (.reg .slt)
    (.next (.reg .iszero) (.next (.push [0x39, 0xc6] (by decide)) (.branch vyRevertT (.dest (.next
    (.push [0x03] (by decide)) (.next (.push [0x01, 0x60] (by decide)) (.next (.reg .mload)
    (.next (.reg .slt) (.next (.push [0x39, 0xd6] (by decide)) (.branch vyRevertT (.dest (.next
    (.push [0x01, 0xe0] (by decide)) (.next (.reg .mload) (.next (.push [0x02, 0x20] (by decide))
    (.next (.reg .mstore) (.next (.push [0x00] (by decide)) (.next (.push [0x02, 0x40] (by
    decide)) (.next (.reg .mstore) (.next (.push [0x01, 0x40] (by decide)) (.next (.reg .mload)
    (.next (.push [0x03] (by decide)) (vyMulT 0x39 0xfe vyRevertT (.next (.push [0x02, 0x60] (by
    decide)) (.next (.reg .mstore) (.next (.push [0x00] (by decide)) (.next (.push [0x02, 0x80]
    (by decide)) (.next (.reg .mstore) (.next (.push [0x02, 0xa0] (by decide)) (.next (.push
    [0x00] (by decide)) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg
    (.dup 3)) (.next (.reg .mstore) (.next (.reg .add)
    rest)))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The coin-loop test at `0x3a1b`: skip coin `i`, else load `_x = xp[_i]`. -/
def ydTest (k1 k2 : Nat) : SFunc :=
  (.dest (.next (.push [0x01, 0x60] (by decide)) (.next (.reg .mload) (.next (.push [0x02, 0xa0]
    (by decide)) (.next (.reg .mload) (.next (.reg .xor) (.next (.reg .iszero) (.next (.push
    [0x3a, 0x4b] (by decide)) (.branch (.next (.push [0x01, 0x80] (by decide)) (.next (.push
    [0x02, 0xa0] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg
    (.dup 1)) (.next (.reg .lt) (.next (.push [0x3a, 0x3d] (by decide)) (.branch .undefined
    (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg
    .mload) (.next (.push [0x02, 0x80] (by decide)) (.next (.reg .mstore) (.next (.push [0x3a,
    0x50] (by decide)) (.jump k1))))))))))))))))) (.dest (.next (.push [0x3a, 0xcc] (by decide))
    (.jump k2))))))))))))

/-- The coin-loop counter tail at `0x3acc`, ending in the `JUMPI` node `jmp`. -/
def ydCoinTail (jmp : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide)) (.next
    (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore) (.next (.reg
    (.dup 1)) (.next (.reg .eq) (.next (.reg .iszero) (.next (.push [0x3a, 0x1b] (by decide))
    jmp))))))))))))

/-- The coin-loop accumulation at `0x3a50`: `S_ += _x; c = c * D / (_x * N_COINS)`. -/
def ydAcc (tail : SFunc) : SFunc :=
  (.dest (.next (.push [0x02, 0x40] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .mload)
    (.next (.push [0x02, 0x80] (by decide)) (.next (.reg .mload) (vyAddT 0x3a 0x68 vyRevertT
    (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.reg .pop) (.next (.push [0x02, 0x20]
    (by decide)) (.next (.reg .mload) (.next (.push [0x01, 0xe0] (by decide)) (.next (.reg
    .mload) (vyMulT 0x3a 0x8e vyRevertT (.next (.push [0x02, 0x80] (by decide)) (.next (.reg
    .mload) (.next (.push [0x03] (by decide)) (vyMulT 0x3a 0xaf vyRevertT (vyDivT 0x3a 0xc1
    vyRevertT (.next (.push [0x02, 0x20] (by decide)) (.next (.reg .mstore)
    tail))))))))))))))))))))))

/-- After the coin loop (`0x3adc`): `c = c * D / (Ann * N_COINS)`, `b = S_ + D / Ann`,
`y_prev = 0`, `y = D`, the `y`-loop counter. -/
def ydPost (head : SFunc) : SFunc :=
  (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x02, 0x20] (by decide)) (.next
    (.reg .mload) (.next (.push [0x01, 0xe0] (by decide)) (.next (.reg .mload) (vyMulT 0x3a
    0xfa vyRevertT (.next (.push [0x02, 0x60] (by decide)) (.next (.reg .mload) (.next (.push
    [0x03] (by decide)) (vyMulT 0x3b 0x1b vyRevertT (vyDivT 0x3b 0x2d vyRevertT (.next (.push
    [0x02, 0x20] (by decide)) (.next (.reg .mstore) (.next (.push [0x02, 0x40] (by decide))
    (.next (.reg .mload) (.next (.push [0x01, 0xe0] (by decide)) (.next (.reg .mload) (.next
    (.push [0x02, 0x60] (by decide)) (.next (.reg .mload) (vyDivT 0x3b 0x4e vyRevertT (vyAddT
    0x3b 0x63 vyRevertT (.next (.push [0x02, 0xc0] (by decide)) (.next (.reg .mstore) (.next
    (.push [0x00] (by decide)) (.next (.push [0x02, 0xe0] (by decide)) (.next (.reg .mstore)
    (.next (.push [0x01, 0xe0] (by decide)) (.next (.reg .mload) (.next (.push [0x03, 0x00] (by
    decide)) (.next (.reg .mstore) (.next (.push [0x03, 0x20] (by decide)) (.next (.push [0x00]
    (by decide)) (.next (.push [0xff] (by decide)) (.next (.reg (.dup 1)) (.next (.reg (.dup 3))
    (.next (.reg .mstore) (.next (.reg .add) head)))))))))))))))))))))))))))))))))))))))

/-- The post-loop with the first `y` pass inline (entries 120, 121). -/
abbrev ydPost0 : SFunc := ydPost (ydHead 141 142 143 .undefined)

/-! ## The certificate's entries, by shape -/

theorem progYD_753 : progYD[753]? = some (ydEntry (ydTest 763 18)) := by decide +kernel

theorem progYD_763 : progYD[763]? = some (ydAcc (ydCoinTail (.branchTo .undefined 49))) := by decide +kernel

theorem progYD_18 : progYD[18]? = some (ydCoinTail (.branchTo .undefined 49)) := by decide +kernel

theorem progYD_49 : progYD[49]? = some (ydTest 76 77) := by decide +kernel

theorem progYD_76 : progYD[76]? = some (ydAcc (ydCoinTail (.branchTo .undefined 99))) := by decide +kernel

theorem progYD_77 : progYD[77]? = some (ydCoinTail (.branchTo .undefined 99)) := by decide +kernel

theorem progYD_99 : progYD[99]? = some (ydTest 120 121) := by decide +kernel

theorem progYD_120 : progYD[120]? = some (ydAcc (ydCoinTail (.branch ydPost0 .undefined))) := by decide +kernel

theorem progYD_121 : progYD[121]? = some (ydCoinTail (.branch ydPost0 .undefined)) := by decide +kernel

theorem progYD_141 : progYD[141]? = some (ydExit) := by decide +kernel

theorem progYD_163 : progYD[163]? = some (ydExit) := by decide +kernel

theorem progYD_185 : progYD[185]? = some (ydExit) := by decide +kernel

theorem progYD_142 : progYD[142]? = some (ydTail 143 .undefined) := by decide +kernel

theorem progYD_164 : progYD[164]? = some (ydTail 165 .undefined) := by decide +kernel

theorem progYD_186 : progYD[186]? = some (ydTail 187 .undefined) := by decide +kernel

theorem progYD_204 : progYD[204]? = some (ydTail 205 ydExit) := by decide +kernel

theorem progYD_143 : progYD[143]? = some (ydHead 163 164 165 .undefined) := by decide +kernel

theorem progYD_165 : progYD[165]? = some (ydHead 185 186 187 .undefined) := by decide +kernel

theorem progYD_187 : progYD[187]? = some (ydHead 185 204 205 .undefined) := by decide +kernel

theorem progYD_205 : progYD[205]? = some (ydHead 185 204 205 ydExit) := by decide +kernel

end Blanc.Lift.Curve3Pool
