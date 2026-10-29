import Blanc.Lift.CheckFast

/-!
# Code tries checked in one linear pass

`LTrie.ofList` splits its list with `take`/`drop` at every level, so a kernel check that a
literal trie equals `LTrie.ofList d l` costs about `d` passes over `l`. `LTrie.build` builds
the same trie in one left-to-right pass and also returns the unread rest. A generated
`CheckTries` module checks `LTrie.build d l = (t, [])` once by kernel `rfl`; `build_eq` turns
that into the unchanged `t = LTrie.ofList d l` and the length bound `l.length ≤ 2 ^ d` that
`CodeTries.ofData` takes, so no separate length decision is needed.
-/

namespace Blanc.Lift

/-- The depth-`d` trie of a list in one left-to-right pass, with the unread rest. -/
def LTrie.build {α : Type} : Nat → List α → LTrie α × List α
  | 0, l => (.leaf l.head?, l.tail)
  | d + 1, l =>
    match LTrie.build d l with
    | (t₁, r₁) =>
      match LTrie.build d r₁ with
      | (t₂, r₂) => (.node t₁ t₂, r₂)

/-- `LTrie.ofList d` reads only the first `2 ^ d` positions. -/
theorem LTrie.ofList_take {α : Type} (d : Nat) (l : List α) :
    LTrie.ofList d (l.take (2 ^ d)) = LTrie.ofList d l := by
  induction d generalizing l with
  | zero => cases l <;> rfl
  | succ d ih =>
    simp only [LTrie.ofList, List.take_take, List.drop_take]
    rw [show min (2 ^ d) (2 ^ (d + 1)) = 2 ^ d by rw [Nat.pow_succ]; omega,
      show 2 ^ (d + 1) - 2 ^ d = 2 ^ d by rw [Nat.pow_succ]; omega, ih, ih]

/-- `LTrie.build` is `LTrie.ofList` with the positions past `2 ^ d` as the rest. -/
theorem LTrie.build_eq {α : Type} (d : Nat) (l : List α) :
    LTrie.build d l = (LTrie.ofList d l, l.drop (2 ^ d)) := by
  induction d generalizing l with
  | zero => cases l <;> rfl
  | succ d ih =>
    simp only [LTrie.build, ih, LTrie.ofList, LTrie.ofList_take, List.drop_drop]
    rw [show 2 ^ d + 2 ^ d = 2 ^ (d + 1) by rw [Nat.pow_succ]; omega]

/-- A trie `LTrie.build` produces is the trie `LTrie.ofList` produces. -/
theorem LTrie.eq_ofList_of_build {α : Type} {d : Nat} {l : List α} {t : LTrie α} {r : List α}
    (h : LTrie.build d l = (t, r)) : t = LTrie.ofList d l := by
  rw [LTrie.build_eq] at h
  exact (Prod.mk.inj h).1.symm

/-- A list `LTrie.build` reads to the end fits in depth `d`. -/
theorem LTrie.length_le_of_build {α : Type} {d : Nat} {l : List α} {t : LTrie α}
    (h : LTrie.build d l = (t, [])) : l.length ≤ 2 ^ d := by
  rw [LTrie.build_eq] at h
  exact List.drop_eq_nil_iff.mp (Prod.mk.inj h).2

end Blanc.Lift
