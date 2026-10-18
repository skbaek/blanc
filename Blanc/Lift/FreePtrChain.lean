import Blanc.Lift.FreePtr

/-! Chain assembly of an annotated certificate check from per-entry decisions
(contract-neutral).

The free-pointer counterpart of `Blanc/Lift/CheckChain.lean`, generic over the per-entry check:
a long certificate's annotated check (`fpCert`, and the write-site checker's `wsCert` in
`Blanc/Lift/WriteSiteChain.lean`) is decided one entry at a time (`chainEntry`, one kernel
`decide` each, generated in split modules), and the tails `(c.zip ann).drop k` are walked from
the end, one step per entry, so no step sees more than one entry. -/

namespace Blanc.Lift

/-- Entry `k` passes `chk` under its annotation (`false` past either end). -/
def chainEntry {α β : Type} (chk : α → β → Bool) (c : List α) (ann : List β) (k : Nat) : Bool :=
  match c[k]?, ann[k]? with
  | some p, some A => chk p A
  | _, _ => false

/-- Every entry from `k` on passes `chk` under its annotation. -/
def chainFrom {α β : Type} (chk : α → β → Bool) (c : List α) (ann : List β) (k : Nat) : Bool :=
  ((c.zip ann).drop k).all fun p => chk p.1 p.2

/-- One step of the chain. -/
theorem chainFrom_step {α β : Type} {chk : α → β → Bool} {c : List α} {ann : List β} (k : Nat)
    (h : chainEntry chk c ann k = true) (hrest : chainFrom chk c ann (k + 1) = true) :
    chainFrom chk c ann k = true := by
  unfold chainEntry at h
  split at h
  · rename_i p A hp hA
    have hz : (c.zip ann)[k]? = some (p, A) := List.getElem?_zip_eq_some.mpr ⟨hp, hA⟩
    have hk : k < (c.zip ann).length := (List.getElem?_eq_some_iff.mp hz).1
    have hget : (c.zip ann)[k] = (p, A) := (List.getElem?_eq_some_iff.mp hz).2
    unfold chainFrom at hrest ⊢
    rw [List.drop_eq_getElem_cons hk, hget, List.all_cons, h, hrest]
    rfl
  · exact absurd h Bool.false_ne_true

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

/-- Entry `k` passes the free-pointer walk under its annotation (`false` past either end). -/
def fpEntry (c : Cert) (ann : List Ann) (k : Nat) : Bool := chainEntry (fpChk c ann) c ann k

/-- Every entry from `k` on passes: the third conjunct of `fpCert c ann` at `k = 0`. -/
def fpFrom (c : Cert) (ann : List Ann) (k : Nat) : Bool := chainFrom (fpChk c ann) c ann k

/-- One step of the chain. -/
theorem fpFrom_step {c : Cert} {ann : List Ann} (k : Nat) (h : fpEntry c ann k = true)
    (hrest : fpFrom c ann (k + 1) = true) : fpFrom c ann k = true :=
  chainFrom_step k h hrest

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
