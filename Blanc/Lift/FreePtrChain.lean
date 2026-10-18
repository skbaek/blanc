import Blanc.Lift.FreePtr

/-! Chain assembly of `fpCert` from per-entry decisions (contract-neutral).

The free-pointer counterpart of `Blanc/Lift/CheckChain.lean`: a long certificate's
`fpCert` is decided one entry at a time (`fpEntry`, one kernel `decide` each, generated in
split modules), and the tails `(c.zip ann).drop k` are walked from the end, one step per
entry, so no step sees more than one entry. -/

namespace Blanc.Lift.FreePtr

open Jaune

/-- Entry `k` passes the free-pointer walk under its annotation (`false` past either end). -/
def fpEntry (c : Cert) (ann : List Ann) (k : Nat) : Bool :=
  match c[k]?, ann[k]? with
  | some p, some A => fpNode c.entries ann A.ret p.1.frame A.entry p.2
  | _, _ => false

/-- Every entry from `k` on passes: the third conjunct of `fpCert c ann` at `k = 0`. -/
def fpFrom (c : Cert) (ann : List Ann) (k : Nat) : Bool :=
  ((c.zip ann).drop k).all fun p => fpNode c.entries ann p.2.ret p.1.1.frame p.2.entry p.1.2

/-- One step of the chain. -/
theorem fpFrom_step {c : Cert} {ann : List Ann} (k : Nat) (h : fpEntry c ann k = true)
    (hrest : fpFrom c ann (k + 1) = true) : fpFrom c ann k = true := by
  unfold fpEntry at h
  split at h
  · rename_i p A hp hA
    have hz : (c.zip ann)[k]? = some (p, A) := List.getElem?_zip_eq_some.mpr ⟨hp, hA⟩
    have hk : k < (c.zip ann).length := (List.getElem?_eq_some_iff.mp hz).1
    have hget : (c.zip ann)[k] = (p, A) := (List.getElem?_eq_some_iff.mp hz).2
    unfold fpFrom at hrest ⊢
    rw [List.drop_eq_getElem_cons hk, hget, List.all_cons, h, hrest]
    rfl
  · exact absurd h Bool.false_ne_true

/-- The chain's end: past the last entry nothing is left to check. -/
theorem fpFrom_of_le {c : Cert} {ann : List Ann} {k : Nat} (h : c.length ≤ k) :
    fpFrom c ann k = true := by
  unfold fpFrom
  rw [List.drop_eq_nil_of_le
    (by simp only [List.length_zip]; exact Nat.le_trans (Nat.min_le_left _ _) h)]
  rfl

/-- Assemble `fpCert` from its head conditions and the chain. -/
theorem fpCert_of_fpFrom {c : Cert} {ann : List Ann}
    (hhead : (ann.length == c.length && (ann[0]?.map Ann.entry) == some FSt.init) = true)
    (h : fpFrom c ann 0 = true) : fpCert c ann = true := by
  unfold fpCert
  unfold fpFrom at h
  rw [List.drop_zero] at h
  rw [hhead, h]
  rfl

end Blanc.Lift.FreePtr
