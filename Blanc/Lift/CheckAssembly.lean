import Blanc.Lift.Check
import Blanc.Lift.Exact

/-! Shared assembly of a checked single-entry lift certificate. -/

namespace Blanc.Lift

open Jaune

/-- Assemble the unchanged checker from its startup condition and sole node check. -/
theorem Cert.check_singleton {code : ByteArray} {entry : Entry} {node : SFunc}
    (hstart : (entry.pc == 0 && entry.frame == []) = true)
    (hnode : checkNode code [entry] entry.rets entry.pc entry.frame node = true) :
    Cert.check code [(entry, node)] = true := by
  change ((entry.pc == 0 && entry.frame == []) &&
    (checkNode code [entry] entry.rets entry.pc entry.frame node && true)) = true
  rw [hstart, hnode]
  rfl

/-- Assemble a seven-entry non-memory certificate from its startup condition
and seven node checks. The entries stay implicit: each node check unifies them
against the certificate's own entry list, exactly as in `check_singleton`.
The registered producer emits a call to this lemma in its opt-in `seven`
assembly mode, so the per-certificate `cert_check` stays below the
duplication floor instead of repeating the generic conjunction. -/
theorem Cert.check_seven {code : ByteArray}
    {e0 e1 e2 e3 e4 e5 e6 : Entry} {f0 f1 f2 f3 f4 f5 f6 : SFunc}
    (h0 : checkNode code [e0, e1, e2, e3, e4, e5, e6] e0.rets e0.pc e0.frame f0 = true)
    (h1 : checkNode code [e0, e1, e2, e3, e4, e5, e6] e1.rets e1.pc e1.frame f1 = true)
    (h2 : checkNode code [e0, e1, e2, e3, e4, e5, e6] e2.rets e2.pc e2.frame f2 = true)
    (h3 : checkNode code [e0, e1, e2, e3, e4, e5, e6] e3.rets e3.pc e3.frame f3 = true)
    (h4 : checkNode code [e0, e1, e2, e3, e4, e5, e6] e4.rets e4.pc e4.frame f4 = true)
    (h5 : checkNode code [e0, e1, e2, e3, e4, e5, e6] e5.rets e5.pc e5.frame f5 = true)
    (h6 : checkNode code [e0, e1, e2, e3, e4, e5, e6] e6.rets e6.pc e6.frame f6 = true)
    (hstart : (e0.pc == 0 && e0.frame == []) = true) :
    Cert.check code
      [(e0, f0), (e1, f1), (e2, f2), (e3, f3), (e4, f4), (e5, f5), (e6, f6)] = true := by
  unfold Cert.check
  simp only [Cert.entries, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
  rw [hstart, h0, h1, h2, h3, h4, h5, h6]
  rfl

/-- Assemble a seven-entry jump certificate from its seven node checks, the
`jumpsOk` counterpart of `check_seven` for hand-written `Jumps` modules. -/
theorem Cert.jumpsOk_seven {code : ByteArray}
    {e0 e1 e2 e3 e4 e5 e6 : Entry} {f0 f1 f2 f3 f4 f5 f6 : SFunc}
    (h0 : jumpsOkNode code [e0, e1, e2, e3, e4, e5, e6] f0 e0.frame = true)
    (h1 : jumpsOkNode code [e0, e1, e2, e3, e4, e5, e6] f1 e1.frame = true)
    (h2 : jumpsOkNode code [e0, e1, e2, e3, e4, e5, e6] f2 e2.frame = true)
    (h3 : jumpsOkNode code [e0, e1, e2, e3, e4, e5, e6] f3 e3.frame = true)
    (h4 : jumpsOkNode code [e0, e1, e2, e3, e4, e5, e6] f4 e4.frame = true)
    (h5 : jumpsOkNode code [e0, e1, e2, e3, e4, e5, e6] f5 e5.frame = true)
    (h6 : jumpsOkNode code [e0, e1, e2, e3, e4, e5, e6] f6 e6.frame = true) :
    Cert.jumpsOk code
      [(e0, f0), (e1, f1), (e2, f2), (e3, f3), (e4, f4), (e5, f5), (e6, f6)] = true := by
  unfold Cert.jumpsOk
  simp only [Cert.entries, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
  rw [h0, h1, h2, h3, h4, h5, h6]
  rfl

end Blanc.Lift
