import Blanc.Lift.FreePtr

/-! Range assembly of an annotated certificate check from range decisions
(contract-neutral).

The annotated counterpart of `Cert.rangeOk` (`Blanc/Lift/CheckRange.lean`), generic over the
per-entry check: a long certificate's annotated check (`fpCert`, and the write-site checker's
`wsCert` in `Blanc/Lift/WriteSiteChain.lean`) is decided one contiguous range of entries at a time
(`chainRange`, one kernel `decide` each, generated in split modules), and `chainFrom_range` chains
the ranges over the tails `(c.zip ann).drop k`. -/

namespace Blanc.Lift

/-- Every entry from `k` on passes `chk` under its annotation. -/
def chainFrom {α β : Type} (chk : α → β → Bool) (c : List α) (ann : List β) (k : Nat) : Bool :=
  ((c.zip ann).drop k).all fun p => chk p.1 p.2

/-- The entries `k .. k + n - 1` (those that exist) pass `chk` under their annotations. -/
def chainRange {α β : Type} (chk : α → β → Bool) (c : List α) (ann : List β) (k n : Nat) :
    Bool :=
  (((c.zip ann).drop k).take n).all fun p => chk p.1 p.2

/-- One link of the chain: a range and the tail after it give the tail from its start. -/
theorem chainFrom_range {α β : Type} {chk : α → β → Bool} {c : List α} {ann : List β}
    (k n : Nat) (h : chainRange chk c ann k n = true)
    (hrest : chainFrom chk c ann (k + n) = true) : chainFrom chk c ann k = true := by
  unfold chainRange at h
  unfold chainFrom at hrest ⊢
  rw [← List.take_append_drop n ((c.zip ann).drop k), List.all_append, h, List.drop_drop, hrest]
  rfl

/-- The chain's end: past the last entry nothing is left to check. -/
theorem chainFrom_of_le {α β : Type} {chk : α → β → Bool} {c : List α} {ann : List β} {k : Nat}
    (h : c.length ≤ k) : chainFrom chk c ann k = true := by
  unfold chainFrom
  rw [List.drop_eq_nil_of_le
    (by simp only [List.length_zip]; exact Nat.le_trans (Nat.min_le_left _ _) h)]
  rfl

end Blanc.Lift

namespace Blanc.Lift.FreePtr

open Jaune

/-- The free-pointer walk of one certificate entry under its annotation. -/
def fpChk (c : Cert) (ann : List Ann) (p : Entry × SFunc) (A : Ann) : Bool :=
  fpNode c.entries ann A.ret p.1.frame A.entry p.2

/-- Every entry from `k` on passes: the third conjunct of `fpCert c ann` at `k = 0`. -/
def fpFrom (c : Cert) (ann : List Ann) (k : Nat) : Bool := chainFrom (fpChk c ann) c ann k

/-- The entries `k .. k + n - 1` pass the free-pointer walk: one generated kernel decision. -/
def fpRange (c : Cert) (ann : List Ann) (k n : Nat) : Bool := chainRange (fpChk c ann) c ann k n

/-- One link of the chain. -/
theorem fpFrom_range {c : Cert} {ann : List Ann} (k n : Nat) (h : fpRange c ann k n = true)
    (hrest : fpFrom c ann (k + n) = true) : fpFrom c ann k = true :=
  chainFrom_range k n h hrest

/-- The chain's end: past the last entry nothing is left to check. -/
theorem fpFrom_of_le {c : Cert} {ann : List Ann} {k : Nat} (h : c.length ≤ k) :
    fpFrom c ann k = true :=
  chainFrom_of_le h

/-- Assemble `fpCert` from its head conditions and the chain. -/
theorem fpCert_of_fpFrom {c : Cert} {ann : List Ann}
    (hhead : (ann.length == c.length && (ann[0]?.map Ann.entry) == some FSt.init) = true)
    (h : fpFrom c ann 0 = true) : fpCert c ann = true := by
  unfold fpCert
  unfold fpFrom chainFrom at h
  rw [List.drop_zero] at h
  rw [hhead]
  exact h

end Blanc.Lift.FreePtr
