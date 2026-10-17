import Blanc.Lift.Check

/-!
# C1 control: a `CALL` node at a `DELEGATECALL` site is rejected

The lift checker reads each node's bytes from the code, so a certificate cannot claim the
semantics of `CALL` (`0xf1`) where the code holds `DELEGATECALL` (`0xf4`).
-/

namespace Blanc.Lift

open Jaune Blanc

/-- **C1 control, checker**: a certificate node claiming `CALL` where the code holds
`DELEGATECALL` (`0xf4`) is rejected. -/
theorem checkNode_call_at_delegatecall {code : ByteArray} {es : List Entry} {m pc : Nat}
    {a : List AVal} {f : SFunc} (byte : byteAt code pc = some 0xf4) :
    checkNode code es m pc a (.next (.exec .call) f) = false := by
  have hbytes : bytesAt code pc (Ninst.toBytes (.exec .call)) = false := by
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp byte
    unfold bytesAt
    rw [List.drop_eq_getElem_cons hlt, hget]
    rfl
  simp only [checkNode, hbytes, Bool.false_and]

end Blanc.Lift
