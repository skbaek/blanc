import Blanc.Lift.InvWalk
import Blanc.Lift.ExactWalkOps
import Blanc.Lift.CopyLoop
import Blanc.Lift.Silent
import Blanc.Lift.WalkInvKit
import Blanc.Lift.InvWalkOps

/-!
# Inversion step lemmas for stack, environment and memory operations

Companions to `Blanc/Lift/ExactWalk.lean` and `Blanc/Lift/ExactWalkOps.lean` for
inverting successful single-step execution: binary operations (`SUB`, `GT`, `MUL`,
`DIV`, `MOD`, `OR`, `XOR`, `EXP`, `SHL`, `SHR`, `BYTE`), unary `NOT`, environment pushes
(`CALLVALUE`, `CALLDATASIZE`, `RETURNDATASIZE`, `GAS`, `CALLDATALOAD`), and
memory operations (`MLOAD`, `MSTORE`, `MSTORE8`, `CALLDATACOPY`, `RETURNDATACOPY`, `CODECOPY`, with
numeral-offset forms), `ri_val` to name a successor's top word, the solc word-copy loop
inverted (`ric_copy_step`, `ric_copy_exit`), and the comparison-flag facts a failed guard
leaves (`toNat_le_of_gtCheck_eq_zero`, `toNat_ge_of_ltCheck_eq_zero`,
`eq_zero_of_iszero_ne_zero`).

Each lemma pairs with its forward counterpart: from a successful synthetic run of a
node at an `St b S M G` state, the successor is again an `St` over the base `b`.
-/

namespace Blanc.Lift

open Jaune

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-! ## Binary operations -/

/-- `BYTE`, inverted. -/
theorem ri_byte {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .byte) d) :
    ∃ G', d = St b ((List.getD y.toBytes x.toNat 0).toB256 :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := fun x y => (List.getD y.toBytes x.toNat 0).toB256) (Devm.diffBurn_of_applyBinary run)

/-! ## Unary operations -/

/-! ## Environment pushes -/

/-! ## Memory operations -/

/-! ## Naming a successor's top word -/

end Steps

/-! ## The solc word-copy loop, inverted -/

section CopyLoop

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 : UInt8} {k : Nat} {exit T : SFunc}

end CopyLoop

/-! ## Comparison flags -/

end Blanc.Lift

