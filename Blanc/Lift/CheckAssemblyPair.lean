import Blanc.Lift.Check
import Blanc.Lift.Exact

/-! Shared assembly of a checked two-entry lift certificate (the `two` counterpart of
`Cert.check_singleton`/`Cert.check_seven` in `Blanc/Lift/CheckAssembly.lean`, kept in its own
module so that adding it rebuilds no existing certificate). -/

namespace Blanc.Lift

open Jaune

/-- Assemble a two-entry non-memory certificate from its two node checks and its startup
condition. The entries stay implicit: each node check unifies them against the certificate's own
entry list. The registered producer emits a call to this lemma in its opt-in `two` assembly mode,
so the per-certificate `cert_check` stays below the duplication floor instead of repeating the
generic conjunction. -/
theorem Cert.check_two {code : ByteArray} {e0 e1 : Entry} {f0 f1 : SFunc}
    (h0 : checkNode code [e0, e1] e0.rets e0.pc e0.frame f0 = true)
    (h1 : checkNode code [e0, e1] e1.rets e1.pc e1.frame f1 = true)
    (hstart : (e0.pc == 0 && e0.frame == []) = true) :
    Cert.check code [(e0, f0), (e1, f1)] = true := by
  unfold Cert.check
  simp only [Cert.entries, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
  rw [hstart, h0, h1]
  rfl

end Blanc.Lift
