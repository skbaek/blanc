import Blanc.Lift.Exact

/-! Chain assembly of a long non-memory lift certificate from its per-entry decisions.

The default generated assembly of `Cert.check`/`Cert.jumpsOk` unfolds the certificate's entry
list with `simp` and splits the membership into one case per entry; at 180 entries (the USDC
implementation) that exceeds the default recursion depth.  The chain form instead walks the
tails `c.drop k` from the end, one `List.drop_eq_getElem_cons` step per entry, so no step sees
more than one entry.  The registered producer emits it in its opt-in `chain` assembly mode
(registry `check.assembly` / `jumps.assembly`); every other certificate regenerates
byte-identically.  These are the non-memory counterparts of `Cert.checkEntriesM_drop` and
`Cert.jumpsEntriesM_drop` (`Blanc/Lift/CheckFast.lean`). -/

namespace Blanc.Lift

open Jaune

/-- Every entry of the tail `c` checks against the entry list `es`: the second conjunct of
`Cert.check code c` at `es = c.entries`. -/
def Cert.checkAll (code : ByteArray) (es : List Entry) (c : Cert) : Bool :=
  c.all fun (e, f) => checkNode code es e.rets e.pc e.frame f

/-- Every entry of the tail `c` has its jumps checked against `es`: `Cert.jumpsOk code c` at
`es = c.entries`. -/
def Cert.jumpsAll (code : ByteArray) (es : List Entry) (c : Cert) : Bool :=
  c.all fun (e, f) => jumpsOkNode code es f e.frame

/-- One step of a chain proof of `Cert.checkAll` over the tails of a long certificate. -/
theorem Cert.checkAll_drop {code : ByteArray} {es : List Entry} (c : Cert) (k : Nat)
    (hk : k < c.length)
    (h : checkNode code es (c[k]'hk).1.rets (c[k]'hk).1.pc (c[k]'hk).1.frame (c[k]'hk).2 = true)
    (hrest : Cert.checkAll code es (c.drop (k + 1)) = true) :
    Cert.checkAll code es (c.drop k) = true := by
  rw [List.drop_eq_getElem_cons hk]
  simp only [Cert.checkAll, List.all_cons, Bool.and_eq_true]
  exact ⟨h, hrest⟩

/-- One step of a chain proof of `Cert.jumpsAll`. -/
theorem Cert.jumpsAll_drop {code : ByteArray} {es : List Entry} (c : Cert) (k : Nat)
    (hk : k < c.length) (h : jumpsOkNode code es (c[k]'hk).2 (c[k]'hk).1.frame = true)
    (hrest : Cert.jumpsAll code es (c.drop (k + 1)) = true) :
    Cert.jumpsAll code es (c.drop k) = true := by
  rw [List.drop_eq_getElem_cons hk]
  simp only [Cert.jumpsAll, List.all_cons, Bool.and_eq_true]
  exact ⟨h, hrest⟩

/-- The chain's end: past the last entry nothing is left to check. -/
theorem Cert.checkAll_drop_length {code : ByteArray} {es : List Entry} (c : Cert) :
    Cert.checkAll code es (c.drop c.length) = true := by
  rw [List.drop_length]
  rfl

/-- The jump chain's end. -/
theorem Cert.jumpsAll_drop_length {code : ByteArray} {es : List Entry} (c : Cert) :
    Cert.jumpsAll code es (c.drop c.length) = true := by
  rw [List.drop_length]
  rfl

/-- Assemble the unchanged checker from its startup condition and the chain. -/
theorem Cert.check_of_checkAll {code : ByteArray} {c : Cert}
    (hstart : (match c with
      | (e, _) :: _ => e.pc == 0 && e.frame == []
      | [] => false) = true)
    (hall : Cert.checkAll code c.entries c = true) : Cert.check code c = true := by
  unfold Cert.check
  rw [Bool.and_eq_true]
  exact ⟨hstart, hall⟩

/-- Assemble the unchanged jump checker from the chain. -/
theorem Cert.jumpsOk_of_jumpsAll {code : ByteArray} {c : Cert}
    (hall : Cert.jumpsAll code c.entries c = true) : Cert.jumpsOk code c = true := hall

end Blanc.Lift
