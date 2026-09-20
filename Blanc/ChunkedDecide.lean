/-
ChunkedDecide.lean : the one cut that keeps a closed `decide +kernel` over a
long list equality inside the Lean kernel's recursion budget.

A closed `decide +kernel` over a `List` equality is checked by unfolding
`List.decEq` once per element, so its cost is the list's *length* and nothing
else. Measured on Lean 4.34 by A/B over one committed artifact, every row
differing only in where the equality was cut: 3,813 elements pass and 4,200
elements fail with `(kernel) deep recursion detected`. Any Blanc artifact above
roughly 3,800 bytes therefore needs its identity cut before it is decided, and
anything below does not — which is why hundreds of modules carrying
`decide +kernel` sites are unaffected.

`eq_of_take_drop_eq` is that cut. It changes no statement, emits no byte, needs
no raised elaboration or kernel ceiling, and reaches for no compiler-evaluated
decision procedure: it splits one equality into a prefix and a suffix equality,
each of which is decided on its own by the kernel it already had to satisfy.
Chunk for margin rather than for the fewest cuts — Blanc's call sites use
2,200, roughly half the measured cliff, so a future toolchain step that tightens
the budget does not reopen them.

This module deliberately has no Blanc import. It states a fact about `List`
alone and sits below every consumer, so adding a user costs that user's rebuild
and nothing else. `Blanc/Basic.lean` is not the home: its own header records
that Blanc's generic list lemmas now live upstream in Jaune, and Jaune is a
pinned dependency.
-/

namespace Blanc

/-- Decide a list equality one bounded chunk at a time.

Given `l.take n = r.take n` and `l.drop n = r.drop n`, conclude `l = r`. Each
hypothesis is a strictly shorter list equality, so a closed `decide +kernel`
over an artifact too long for the kernel's recursion budget becomes two that
are not. Nest the lemma for more than two chunks. -/
theorem eq_of_take_drop_eq {α : Type _} (n : Nat) {l r : List α}
    (htake : l.take n = r.take n) (hdrop : l.drop n = r.drop n) : l = r :=
  (List.take_append_drop n l).symm.trans
    (by rw [htake, hdrop]; exact List.take_append_drop n r)

end Blanc
