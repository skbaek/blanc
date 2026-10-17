import Blanc.Lift.Curve3Pool.Callee.GetYDTrees

/-!
# `get_y`'s lifted trees, by shape

`get_y` (pc `0x18a4`, entry 252) calls `_A` and `get_D` (with frame save/restore chains, walked
on the certificate's own trees in `GetY.lean`), then runs the same coin loop and Newton `y`
loop as `get_y_D` at other offsets: the coin-loop test at `0x1a50` (entries 547 inline, 44,
95), the accumulation at `0x1aa1` (559, 70, 115; behind one more `JUMPDEST` at `0x1aa0` in 560,
71, 116), the counter tail at `0x1b1d` (9, 72, 117), the post-loop at `0x1b2d` with the first
`y` pass inline, peeled copies 138, 160, 182 and the steady head 201 of the `y` loop at
`0x1bd9`, counter tails at `0x1cee` (137, 159, 181, 200) and exits at `0x1cff` (136, 158,
180).

Each distinct shape is one definition here, parameterised by its goto targets and by the
subtree it continues with, and every certificate entry of the closure is one kernel equation
(`decide +kernel`) between its lookup and its shape.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune


/-- The exit at `0x1cff`: `return y` (through scratch word 0 and the return slot `0x200`). -/
def gyExit : SFunc :=
  (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x04, 0x80] (by decide)) (.next
    (.reg .mload) (.next (.push [0x00] (by decide)) (.next (.reg .mstore) (.next (.push [0x00]
    (by decide)) (.next (.reg .mload) (.next (.push [0x02, 0x00] (by decide)) (.next (.reg
    .mload) .ret)))))))))))

/-- The counter tail at `0x1cee`: `_i += 1`, back to `k` unless it reached 255, else `fall`. -/
def gyTail (k : Nat) (fall : SFunc) : SFunc :=
  (.dest (.dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide))
    (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore) (.next
    (.reg (.dup 1)) (.next (.reg .eq) (.next (.reg .iszero) (.next (.push [0x1b, 0xd9] (by
    decide)) (.branchTo fall k))))))))))))))

/-- The stopping test of a Newton pass of the `y` loop (`0x1ca7`…), with exit `e`, tail `t`,
head `k`. -/
def gyHeadBr (e t k : Nat) (fall : SFunc) : SFunc :=
  (.branch (.next (.push [0x01] (by decide)) (.next (.push [0x04, 0x80] (by decide)) (.next (.reg
    .mload) (.next (.push [0x04, 0x60] (by decide)) (.next (.reg .mload) (vySubT 0x1c 0xab
    vyRevertT (.next (.reg .gt) (.next (.reg .iszero) (.next (.reg .iszero) (.next (.push [0x1c,
    0xbe] (by decide)) (.branch (.next (.push [0x1c, 0xff] (by decide)) (.jump e)) (.dest (.next
    (.push [0x1c, 0xee] (by decide)) (.jump t)))))))))))))) (.dest (.next (.push [0x01] (by
    decide)) (.next (.push [0x04, 0x60] (by decide)) (.next (.reg .mload) (.next (.push [0x04,
    0x80] (by decide)) (.next (.reg .mload) (vySubT 0x1c 0xda vyRevertT (.next (.reg .gt) (.next
    (.reg .iszero) (.next (.reg .iszero) (.next (.push [0x1c, 0xed] (by decide)) (.branch (.next
    (.push [0x1c, 0xff] (by decide)) (.jump e)) (.dest (gyTail k fall)))))))))))))))

/-- One Newton pass of the `y` loop at `0x1bd9`, with exit `e`, tail `t`, head `k`. -/
def gyHead (e t k : Nat) (fall : SFunc) : SFunc :=
  (.dest (.next (.push [0x04, 0x80] (by decide)) (.next (.reg .mload) (.next (.push [0x04, 0x60]
    (by decide)) (.next (.reg .mstore) (.next (.push [0x04, 0x80] (by decide)) (.next (.reg
    .mload) (.next (.push [0x04, 0x80] (by decide)) (.next (.reg .mload) (vyMulT 0x1b 0xfd
    vyRevertT (.next (.push [0x03, 0xa0] (by decide)) (.next (.reg .mload) (vyAddT 0x1c 0x17
    vyRevertT (.next (.push [0x02] (by decide)) (.next (.push [0x04, 0x80] (by decide)) (.next
    (.reg .mload) (vyMulT 0x1c 0x38 vyRevertT (.next (.push [0x04, 0x40] (by decide)) (.next
    (.reg .mload) (vyAddT 0x1c 0x52 vyRevertT (.next (.push [0x02, 0x80] (by decide)) (.next
    (.reg .mload) (vySubT 0x1c 0x6a vyRevertT (vyDivT 0x1c 0x7c vyRevertT (.next (.push [0x04,
    0x80] (by decide)) (.next (.reg .mstore) (.next (.push [0x04, 0x60] (by decide)) (.next (.reg
    .mload) (.next (.push [0x04, 0x80] (by decide)) (.next (.reg .mload) (.next (.reg .gt) (.next
    (.reg .iszero) (.next (.push [0x1c, 0xc3] (by decide)) (gyHeadBr e t k
    fall))))))))))))))))))))))))))))))))))

/-- After the restore of `get_D`'s call (`0x1a03`): `D`, `c = D`, `S_ = 0`, `Ann`, `_x = 0`,
the coin-loop counter. -/
def gyMid (rest : SFunc) : SFunc :=
  (.dest (.next (.push [0x03, 0x80] (by decide)) (.next (.reg .mload) (.next (.push [0x02, 0x80]
    (by decide)) (.next (.reg .mstore) (.next (.push [0x02, 0x80] (by decide)) (.next (.reg
    .mload) (.next (.push [0x03, 0xa0] (by decide)) (.next (.reg .mstore) (.next (.push [0x00]
    (by decide)) (.next (.push [0x03, 0xc0] (by decide)) (.next (.reg .mstore) (.next (.push
    [0x02, 0x20] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (vyMulT 0x1a
    0x33 vyRevertT (.next (.push [0x03, 0xe0] (by decide)) (.next (.reg .mstore) (.next (.push
    [0x00] (by decide)) (.next (.push [0x04, 0x00] (by decide)) (.next (.reg .mstore) (.next
    (.push [0x04, 0x20] (by decide)) (.next (.push [0x00] (by decide)) (.next (.push [0x03] (by
    decide)) (.next (.reg (.dup 1)) (.next (.reg (.dup 3)) (.next (.reg .mstore) (.next (.reg
    .add) rest))))))))))))))))))))))))))))

/-- The coin-loop test at `0x1a50`: coin `i` loads `_x = x` (on to `k1`); coin `j` is skipped
(on to `k3`); else `_x = xp[_i]` (on to `k2`). -/
def gyTest (k1 k2 k3 : Nat) : SFunc :=
  (.dest (.next (.push [0x01, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x04, 0x20]
    (by decide)) (.next (.reg .mload) (.next (.reg .eq) (.next (.reg .iszero) (.next (.push
    [0x1a, 0x6b] (by decide)) (.branch (.next (.push [0x01, 0x80] (by decide)) (.next (.reg
    .mload) (.next (.push [0x04, 0x00] (by decide)) (.next (.reg .mstore) (.next (.push [0x1a,
    0xa1] (by decide)) (.jump k1)))))) (.dest (.next (.push [0x01, 0x60] (by decide)) (.next
    (.reg .mload) (.next (.push [0x04, 0x20] (by decide)) (.next (.reg .mload) (.next (.reg .xor)
    (.next (.reg .iszero) (.next (.push [0x1a, 0x9b] (by decide)) (.branch (.next (.push [0x01,
    0xa0] (by decide)) (.next (.push [0x04, 0x20] (by decide)) (.next (.reg .mload) (.next (.push
    [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x1a, 0x8d] (by
    decide)) (.branch .undefined (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul)
    (.next (.reg .add) (.next (.reg .mload) (.next (.push [0x04, 0x00] (by decide)) (.next (.reg
    .mstore) (.next (.push [0x1a, 0xa0] (by decide)) (.jump k2))))))))))))))))) (.dest (.next
    (.push [0x1b, 0x1d] (by decide)) (.jump k3)))))))))))))))))))))

/-- The coin-loop counter tail at `0x1b1d`, ending in the `JUMPI` node `jmp`. -/
def gyCoinTail (jmp : SFunc) : SFunc :=
  (.dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide)) (.next
    (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore) (.next (.reg
    (.dup 1)) (.next (.reg .eq) (.next (.reg .iszero) (.next (.push [0x1a, 0x50] (by decide))
    jmp))))))))))))

/-- The coin-loop accumulation at `0x1aa1`: `S_ += _x; c = c * D / (_x * N_COINS)`. -/
def gyAcc (tail : SFunc) : SFunc :=
  (.dest (.next (.push [0x03, 0xc0] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .mload)
    (.next (.push [0x04, 0x00] (by decide)) (.next (.reg .mload) (vyAddT 0x1a 0xb9 vyRevertT
    (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.reg .pop) (.next (.push [0x03, 0xa0]
    (by decide)) (.next (.reg .mload) (.next (.push [0x02, 0x80] (by decide)) (.next (.reg
    .mload) (vyMulT 0x1a 0xdf vyRevertT (.next (.push [0x04, 0x00] (by decide)) (.next (.reg
    .mload) (.next (.push [0x03] (by decide)) (vyMulT 0x1b 0x00 vyRevertT (vyDivT 0x1b 0x12
    vyRevertT (.next (.push [0x03, 0xa0] (by decide)) (.next (.reg .mstore)
    tail))))))))))))))))))))))

/-- After the coin loop (`0x1b2d`): `c = c * D / (Ann * N_COINS)`, `b = S_ + D / Ann`,
`y_prev = 0`, `y = D`, the `y`-loop counter. -/
def gyPost (head : SFunc) : SFunc :=
  (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x03, 0xa0] (by decide)) (.next
    (.reg .mload) (.next (.push [0x02, 0x80] (by decide)) (.next (.reg .mload) (vyMulT 0x1b 0x4b
    vyRevertT (.next (.push [0x03, 0xe0] (by decide)) (.next (.reg .mload) (.next (.push [0x03]
    (by decide)) (vyMulT 0x1b 0x6c vyRevertT (vyDivT 0x1b 0x7e vyRevertT (.next (.push [0x03,
    0xa0] (by decide)) (.next (.reg .mstore) (.next (.push [0x03, 0xc0] (by decide)) (.next (.reg
    .mload) (.next (.push [0x02, 0x80] (by decide)) (.next (.reg .mload) (.next (.push [0x03,
    0xe0] (by decide)) (.next (.reg .mload) (vyDivT 0x1b 0x9f vyRevertT (vyAddT 0x1b 0xb4
    vyRevertT (.next (.push [0x04, 0x40] (by decide)) (.next (.reg .mstore) (.next (.push [0x00]
    (by decide)) (.next (.push [0x04, 0x60] (by decide)) (.next (.reg .mstore) (.next (.push
    [0x02, 0x80] (by decide)) (.next (.reg .mload) (.next (.push [0x04, 0x80] (by decide)) (.next
    (.reg .mstore) (.next (.push [0x04, 0xa0] (by decide)) (.next (.push [0x00] (by decide))
    (.next (.push [0xff] (by decide)) (.next (.reg (.dup 1)) (.next (.reg (.dup 3)) (.next (.reg
    .mstore) (.next (.reg .add) head)))))))))))))))))))))))))))))))))))))))

/-- The post-loop with the first `y` pass inline (entries 115 … 117). -/
abbrev gyPost0 : SFunc := gyPost (gyHead 136 137 138 .undefined)

/-! ## The certificate's entries, by shape -/

theorem progGY_559 : progYD[559]? = some (gyAcc (gyCoinTail (.branchTo .undefined 44))) := by decide +kernel

theorem progGY_560 : progYD[560]? = some (.dest (gyAcc (gyCoinTail (.branchTo .undefined 44)))) := by decide +kernel

theorem progGY_9 : progYD[9]? = some (gyCoinTail (.branchTo .undefined 44)) := by decide +kernel

theorem progGY_44 : progYD[44]? = some (gyTest 70 71 72) := by decide +kernel

theorem progGY_70 : progYD[70]? = some (gyAcc (gyCoinTail (.branchTo .undefined 95))) := by decide +kernel

theorem progGY_71 : progYD[71]? = some (.dest (gyAcc (gyCoinTail (.branchTo .undefined 95)))) := by decide +kernel

theorem progGY_72 : progYD[72]? = some (gyCoinTail (.branchTo .undefined 95)) := by decide +kernel

theorem progGY_95 : progYD[95]? = some (gyTest 115 116 117) := by decide +kernel

theorem progGY_115 : progYD[115]? = some (gyAcc (gyCoinTail (.branch gyPost0 .undefined))) := by decide +kernel

theorem progGY_116 : progYD[116]? = some (.dest (gyAcc (gyCoinTail (.branch gyPost0 .undefined)))) := by decide +kernel

theorem progGY_117 : progYD[117]? = some (gyCoinTail (.branch gyPost0 .undefined)) := by decide +kernel

theorem progGY_136 : progYD[136]? = some (gyExit) := by decide +kernel

theorem progGY_158 : progYD[158]? = some (gyExit) := by decide +kernel

theorem progGY_180 : progYD[180]? = some (gyExit) := by decide +kernel

theorem progGY_137 : progYD[137]? = some (gyTail 138 .undefined) := by decide +kernel

theorem progGY_159 : progYD[159]? = some (gyTail 160 .undefined) := by decide +kernel

theorem progGY_181 : progYD[181]? = some (gyTail 182 .undefined) := by decide +kernel

theorem progGY_200 : progYD[200]? = some (gyTail 201 gyExit) := by decide +kernel

theorem progGY_138 : progYD[138]? = some (gyHead 158 159 160 .undefined) := by decide +kernel

theorem progGY_160 : progYD[160]? = some (gyHead 180 181 182 .undefined) := by decide +kernel

theorem progGY_182 : progYD[182]? = some (gyHead 180 200 201 .undefined) := by decide +kernel

theorem progGY_201 : progYD[201]? = some (gyHead 180 200 201 gyExit) := by decide +kernel

theorem t_1a03_c547_eq : t_1a03_c547 = gyMid (gyTest 559 560 9) := by decide +kernel

end Blanc.Lift.Curve3Pool
