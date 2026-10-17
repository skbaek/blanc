import Blanc.Lift.Curve3Pool.Callee.GetYDTrees

/-!
# `get_D`'s lifted trees, by shape

`get_D` (pc `0x4c9`, entry 417) lifts to thirteen entries: the prologue and the `S` loop
(`for _x in xp: S += _x`, `0x4ef`, unrolled over 417, 431, 445), the set-up after it, and the
Newton loop at `0x58c` with the nested `D_P` loop at `0x5a0`, duplicated by the certificate's
entry cap: the first pass inline in 445 (inner iterations 445, 459, 473), the peeled second
pass 489 (489, 503, 517) and the steady head 533 (533, then 517 twice through its self-loop),
with counter tails at `0x78a` (488, 532) and exits at `0x79b` (487, 531).

Each distinct shape is one definition here; every certificate entry of the closure is one
kernel equation between its lookup and its shape.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune


/-- The exit at `0x79b`: `return D` (through scratch word 0 and the return slot `0x1c0`). -/
def gdExit : SFunc :=
  (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x02, 0x80] (by decide)) (.next
    (.reg .mload) (.next (.push [0x00] (by decide)) (.next (.reg .mstore) (.next (.push [0x00]
    (by decide)) (.next (.reg .mload) (.next (.push [0x01, 0xc0] (by decide)) (.next (.reg
    .mload) .ret)))))))))))

/-- The outer counter tail at `0x78a`: `_i += 1`, back to `k` unless it reached 255, else `fall`. -/
def gdTail (k : Nat) (fall : SFunc) : SFunc :=
  (.dest (.dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide))
    (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore) (.next
    (.reg (.dup 1)) (.next (.reg .eq) (.next (.reg .iszero) (.next (.push [0x05, 0x8c] (by
    decide)) (.branchTo fall k))))))))))))))

/-- One iteration of the inner `D_P` loop at `0x5a0` (`D_P = D_P * D / (_x * N_COINS)`), ending
in the `JUMPI` node `jmp`. -/
def gdInner (jmp : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.push [0x03, 0x20] (by decide)) (.next (.reg
    .mload) (.next (.reg .mul) (.next (.push [0x01, 0x40] (by decide)) (.next (.reg .add) (.next
    (.reg .mload) (.next (.push [0x03, 0x00] (by decide)) (.next (.reg .mstore) (.next (.push
    [0x02, 0xe0] (by decide)) (.next (.reg .mload) (.next (.push [0x02, 0x80] (by decide)) (.next
    (.reg .mload) (vyMulT 0x05 0xcc vyRevertT (.next (.push [0x03, 0x00] (by decide)) (.next
    (.reg .mload) (.next (.push [0x03] (by decide)) (vyMulT 0x05 0xed vyRevertT (vyDivT 0x05 0xff
    vyRevertT (.next (.push [0x02, 0xe0] (by decide)) (.next (.reg .mstore) (.dest (.next (.reg
    (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide)) (.next (.reg .add) (.next
    (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore) (.next (.reg (.dup 1)) (.next
    (.reg .eq) (.next (.reg .iszero) (.next (.push [0x05, 0xa0] (by decide))
    jmp))))))))))))))))))))))))))))))))))

/-- The stopping test of a Newton pass of the `D` loop (`0x74b`…), with exit `e`, tail `t`,
head `k`. -/
def gdRestBr (e t k : Nat) (fall : SFunc) : SFunc :=
  (.branch (.next (.push [0x01] (by decide)) (.next (.push [0x02, 0x80] (by decide)) (.next (.reg
    .mload) (.next (.push [0x02, 0x60] (by decide)) (.next (.reg .mload) (vySubT 0x07 0x47
    vyRevertT (.next (.reg .gt) (.next (.reg .iszero) (.next (.reg .iszero) (.next (.push [0x07,
    0x5a] (by decide)) (.branch (.next (.push [0x07, 0x9b] (by decide)) (.jump e)) (.dest (.next
    (.push [0x07, 0x8a] (by decide)) (.jump t)))))))))))))) (.dest (.next (.push [0x01] (by
    decide)) (.next (.push [0x02, 0x60] (by decide)) (.next (.reg .mload) (.next (.push [0x02,
    0x80] (by decide)) (.next (.reg .mload) (vySubT 0x07 0x76 vyRevertT (.next (.reg .gt) (.next
    (.reg .iszero) (.next (.reg .iszero) (.next (.push [0x07, 0x89] (by decide)) (.branch (.next
    (.push [0x07, 0x9b] (by decide)) (.jump e)) (.dest (gdTail k fall)))))))))))))))

/-- The rest of a Newton pass after the inner loop (`0x5bb`…): the body of line 210, the stopping
test, exit `e`, tail `t`, head `k`. -/
def gdRest (e t k : Nat) (fall : SFunc) : SFunc :=
  (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x02, 0x80] (by decide)) (.next
    (.reg .mload) (.next (.push [0x02, 0x60] (by decide)) (.next (.reg .mstore) (.next (.push
    [0x02, 0xa0] (by decide)) (.next (.reg .mload) (.next (.push [0x01, 0xe0] (by decide)) (.next
    (.reg .mload) (vyMulT 0x06 0x40 vyRevertT (.next (.push [0x02, 0xe0] (by decide)) (.next
    (.reg .mload) (.next (.push [0x03] (by decide)) (vyMulT 0x06 0x61 vyRevertT (vyAddT 0x06 0x77
    vyRevertT (.next (.push [0x02, 0x80] (by decide)) (.next (.reg .mload) (vyMulT 0x06 0x96
    vyRevertT (.next (.push [0x02, 0xa0] (by decide)) (.next (.reg .mload) (.next (.push [0x01]
    (by decide)) (vySubT 0x06 0xb0 vyRevertT (.next (.push [0x02, 0x80] (by decide)) (.next (.reg
    .mload) (vyMulT 0x06 0xcf vyRevertT (.next (.push [0x04] (by decide)) (.next (.push [0x02,
    0xe0] (by decide)) (.next (.reg .mload) (vyMulT 0x06 0xf0 vyRevertT (vyAddT 0x07 0x06
    vyRevertT (vyDivT 0x07 0x18 vyRevertT (.next (.push [0x02, 0x80] (by decide)) (.next (.reg
    .mstore) (.next (.push [0x02, 0x60] (by decide)) (.next (.reg .mload) (.next (.push [0x02,
    0x80] (by decide)) (.next (.reg .mload) (.next (.reg .gt) (.next (.reg .iszero) (.next (.push
    [0x07, 0x5f] (by decide)) (gdRestBr e t k fall)))))))))))))))))))))))))))))))))))))))))))

/-- The outer head at `0x58c`: `D_P = D`, the inner counter, then the first inner iteration. -/
def gdHead (jmp : SFunc) : SFunc :=
  (.dest (.next (.push [0x02, 0x80] (by decide)) (.next (.reg .mload) (.next (.push [0x02, 0xe0]
    (by decide)) (.next (.reg .mstore) (.next (.push [0x03, 0x20] (by decide)) (.next (.push
    [0x00] (by decide)) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg
    (.dup 3)) (.next (.reg .mstore) (.next (.reg .add) (gdInner jmp)))))))))))))

/-- One iteration of the `S` loop at `0x4ef` (`S += _x`), ending in the `JUMPI` node `jmp`. -/
def gdSIter (jmp : SFunc) : SFunc :=
  (.dest (.next (.push [0x20] (by decide)) (.next (.push [0x02, 0x20] (by decide)) (.next (.reg
    .mload) (.next (.reg .mul) (.next (.push [0x01, 0x40] (by decide)) (.next (.reg .add) (.next
    (.reg .mload) (.next (.push [0x02, 0x00] (by decide)) (.next (.reg .mstore) (.next (.push
    [0x01, 0xe0] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .mload) (.next (.push [0x02,
    0x00] (by decide)) (.next (.reg .mload) (vyAddT 0x05 0x17 vyRevertT (.next (.reg (.dup 1))
    (.next (.reg .mstore) (.next (.reg .pop) (.dest (.next (.reg (.dup 1)) (.next (.reg .mload)
    (.next (.push [0x01] (by decide)) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg
    (.dup 3)) (.next (.reg .mstore) (.next (.reg (.dup 1)) (.next (.reg .eq) (.next (.reg
    .iszero) (.next (.push [0x04, 0xef] (by decide)) jmp)))))))))))))))))))))))))))))))

/-- After the `S` loop: `S == 0` returns `0`; else `Dprev`, `D = S`, `Ann`, the outer counter, and the
head `head`. -/
def gdSPost (head : SFunc) : SFunc :=
  (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x01, 0xe0] (by decide)) (.next
    (.reg .mload) (.next (.reg .iszero) (.next (.reg .iszero) (.next (.push [0x05, 0x4d] (by
    decide)) (.branch (.next (.push [0x00] (by decide)) (.next (.push [0x00] (by decide)) (.next
    (.reg .mstore) (.next (.push [0x00] (by decide)) (.next (.reg .mload) (.next (.push [0x01,
    0xc0] (by decide)) (.next (.reg .mload) .ret))))))) (.dest (.next (.push [0x00] (by decide))
    (.next (.push [0x02, 0x60] (by decide)) (.next (.reg .mstore) (.next (.push [0x01, 0xe0] (by
    decide)) (.next (.reg .mload) (.next (.push [0x02, 0x80] (by decide)) (.next (.reg .mstore)
    (.next (.push [0x01, 0xa0] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by
    decide)) (vyMulT 0x05 0x75 vyRevertT (.next (.push [0x02, 0xa0] (by decide)) (.next (.reg
    .mstore) (.next (.push [0x02, 0xc0] (by decide)) (.next (.push [0x00] (by decide)) (.next
    (.push [0xff] (by decide)) (.next (.reg (.dup 1)) (.next (.reg (.dup 3)) (.next (.reg
    .mstore) (.next (.reg .add) head))))))))))))))))))))))))))))))

/-- The prologue: arguments into the frame, `S = 0`, the `S`-loop counter. -/
def gdEntry (rest : SFunc) : SFunc :=
  (.dest (.next (.push [0x01, 0xc0] (by decide)) (.next (.reg .mstore) (.next (.push [0x01, 0x40]
    (by decide)) (.next (.reg .mstore) (.next (.push [0x01, 0x60] (by decide)) (.next (.reg
    .mstore) (.next (.push [0x01, 0x80] (by decide)) (.next (.reg .mstore) (.next (.push [0x01,
    0xa0] (by decide)) (.next (.reg .mstore) (.next (.push [0x00] (by decide)) (.next (.push
    [0x01, 0xe0] (by decide)) (.next (.reg .mstore) (.next (.push [0x02, 0x20] (by decide))
    (.next (.push [0x00] (by decide)) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1))
    (.next (.reg (.dup 3)) (.next (.reg .mstore) (.next (.reg .add) rest)))))))))))))))))))))

/-! ## The certificate's entries, by shape -/

theorem progGD_417 : progYD[417]? = some (gdEntry (gdSIter (.branchTo .undefined 431))) := by decide +kernel

theorem progGD_431 : progYD[431]? = some (gdSIter (.branchTo .undefined 445)) := by decide +kernel

theorem progGD_445 : progYD[445]? = some (gdSIter (.branch (gdSPost (gdHead (.branchTo .undefined 459))) .undefined)) := by decide +kernel

theorem progGD_459 : progYD[459]? = some (gdInner (.branchTo .undefined 473)) := by decide +kernel

theorem progGD_473 : progYD[473]? = some (gdInner (.branch (gdRest 487 488 489 .undefined) .undefined)) := by decide +kernel

theorem progGD_487 : progYD[487]? = some (gdExit) := by decide +kernel

theorem progGD_531 : progYD[531]? = some (gdExit) := by decide +kernel

theorem progGD_488 : progYD[488]? = some (gdTail 489 .undefined) := by decide +kernel

theorem progGD_532 : progYD[532]? = some (gdTail 533 gdExit) := by decide +kernel

theorem progGD_489 : progYD[489]? = some (gdHead (.branchTo .undefined 503)) := by decide +kernel

theorem progGD_503 : progYD[503]? = some (gdInner (.branchTo .undefined 517)) := by decide +kernel

theorem progGD_517 : progYD[517]? = some (gdInner (.branchTo (gdRest 531 532 533 gdExit) 517)) := by decide +kernel

theorem progGD_533 : progYD[533]? = some (gdHead (.branchTo .undefined 517)) := by decide +kernel

theorem progGD_417_t : progYD[417]? = some t_04c9_c417 := by decide +kernel

end Blanc.Lift.Curve3Pool
