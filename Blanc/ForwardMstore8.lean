import Blanc.Forward

/-!
# Forward rules for `MSTORE8`

Contract-neutral construction-direction rules for the byte-width memory store.
The payload is the EVM instruction's actual low `UInt8`, and the memory charge
is left explicit so callers can prove covered writes without hiding expansion.
-/

namespace Blanc

open Jaune

/-- `MSTORE8`, evaluated forward with its exact one-byte memory window. -/
lemma Rinst.runCore_mstore8_eq_ok {pc : Nat} {devm : Devm} {sevm : Sevm}
    {i v : B256} {s : List B256} (h_stk : devm.stack = i :: v :: s)
    (h_gas : gVerylow + devm.extCost [⟨i.toNat, 1⟩] ≤ devm.gasLeft) :
    Rinst.runCore pc devm sevm .mstore8 =
      .ok ((devm.setMach ⟨s, devm.memory,
              devm.gasLeft - (gVerylow + devm.extCost [⟨i.toNat, 1⟩])⟩).memWrite
        i.toNat [v.2.2.toUInt8]) := by
  show (devm.popToNat >>= fun p => p.2.pop >>= fun q =>
    chargeGas (gVerylow + q.2.extCost [⟨p.1, 1⟩]) q.2 >>= fun d =>
      Except.ok (d.memWrite p.1 [q.1.2.2.toUInt8])) = _
  rw [Devm.popToNat_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.pop_eq_ok
    (devm := devm.setMach ⟨v :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  have h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨i.toNat, 1⟩] = devm.extCost [⟨i.toNat, 1⟩] := rfl
  rw [h_ext, chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach, Devm.stack_setMach]

/-- Compiled `MSTORE8`, retaining its exact dynamic expansion term. -/
lemma Ninst.runCompiled_mstore8 {sevm : Sevm} {devm : Devm} {i v : B256}
    {s : List B256} {G : Nat} {M : Mem} (h_stk : devm.stack = i :: v :: s)
    (h_gas : devm.gasLeft = G +
      (gVerylow + devm.extCost [⟨i.toNat, 1⟩]))
    (h_write : devm.memory.write i.toNat [v.2.2.toUInt8] = M) :
    Ninst.RunCompiled sevm devm (.reg .mstore8)
      (devm.setMach ⟨s, M, G⟩) := by
  subst h_write
  have h_eq :
      devm.gasLeft - (gVerylow + devm.extCost [⟨i.toNat, 1⟩]) = G := by
    omega
  refine Ninst.runCompiled_reg (by rintro ⟨⟩) ?_
  rw [Rinst.runCore_mstore8_eq_ok h_stk (by omega), h_eq]
  rfl

/-- Compiled `MSTORE8` with its expansion charge named separately. -/
lemma Ninst.runCompiled_mstore8_of {sevm : Sevm} {devm : Devm} {i v : B256}
    {s : List B256} {G e : Nat} {M : Mem}
    (h_stk : devm.stack = i :: v :: s)
    (h_ext : devm.extCost [⟨i.toNat, 1⟩] = e)
    (h_gas : devm.gasLeft = G + (gVerylow + e))
    (h_write : devm.memory.write i.toNat [v.2.2.toUInt8] = M) :
    Ninst.RunCompiled sevm devm (.reg .mstore8)
      (devm.setMach ⟨s, M, G⟩) := by
  subst h_ext
  exact Ninst.runCompiled_mstore8 h_stk h_gas h_write

end Blanc
