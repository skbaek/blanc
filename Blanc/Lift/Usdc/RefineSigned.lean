import Blanc.Lift.StaticOnlyPrefix
import Blanc.Lift.Usdc.RefineShape
import Blanc.Lift.Usdc.Lib.Check

/-!
# The signed family's library: `SignatureChecker` is quiet (U6e)

`lib_quiet`: a successful frame running the 1,741-byte `SignatureChecker` runtime `Lib.code` keeps
its storage owner's storage at every node of its own chain and has only static descendants
(`LibQuiet`).  Both halves come from the library's certificate and bytes alone:

* the certificate executes no external instruction but `STATICCALL` (`libCert_staticcallOnly`, a
  kernel check over `Lib.cert`), so every spawning node of the chain is a `STATICCALL`
  (`parentPrefix_exec_staticcall_of_cert`);
* no position of the runtime decodes `SSTORE` (`lib_no_sstore`: the byte `0x55` does not occur in
  `Lib.code`, a kernel check).

`Exec.Deriv.ParentPrefix.getStor_of_quiet` and `Exec.descendantFrames_isStatic_of_staticOnly`
(`Blanc/Lift/StaticOnlyPrefix.lean`) turn these into the two halves.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- The library's certificate executes no external instruction but `STATICCALL`. -/
theorem libCert_staticcallOnly :
    ∀ f ∈ Lib.cert.prog, f.execsSatisfy Xinst.isStaticcall = true := by
  decide +kernel

/-- No position of the library runtime decodes `SSTORE`: the byte `0x55` does not occur in it. -/
theorem lib_no_sstore : ∀ pc, ¬ Ninst.At Lib.code pc (.reg .sstore) := by
  have absent : (0x55 : UInt8) ∉ Lib.code.data.toList := by decide +kernel
  exact fun _ hat => absent (ByteArray.sstore_mem_of_getInst hat)

/-- **`LibQuiet`** (U6e): a successful library frame keeps its storage owner's storage along its
own chain and spawns only static frames. -/
theorem lib_quiet : LibQuiet := by
  intro sevm pre post run codeEq fork
  let root : Exec.Deriv := ⟨0, sevm, pre, .ok post, run⟩
  have onlyStatic : ∀ {node : Exec.Deriv} {x : Xinst}, Exec.Deriv.ParentPrefix root node →
      Ninst.At node.sevm.code node.pc (.exec x) → x = .staticcall := fun chain hat =>
    parentPrefix_exec_staticcall_of_cert Lib.cert_check libCert_staticcallOnly
      (root := root) rfl codeEq fork chain hat
  refine ⟨fun N chain => ?_, fun f member =>
    Exec.descendantFrames_isStatic_of_staticOnly root onlyStatic run (.refl _) f member⟩
  have keep := Exec.Deriv.ParentPrefix.getStor_of_quiet chain fork
    (by rw [show root.sevm.code = Lib.code from codeEq]; exact lib_no_sstore) onlyStatic
  exact congrFun keep sevm.currentTarget

end Blanc.Lift.Usdc
