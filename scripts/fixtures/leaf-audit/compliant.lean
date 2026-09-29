/-!
# Leaf-search fixture (compliant)

Elaborated by `python3 scripts/leaf_audit.py self-test` together with the byte-identical body of
`scripts/LeafCensus.lean`. It is deliberately compliant: with `compliant.leaves` the fixture has
exactly the leaves listed there, and every other theorem is used. Each control of the self-test is
a one-line change to this text and must move exactly the leaf set the control names.

* `headline_one`, `headline_two`, `headline_calls`, `Elsewhere.headline_open`, `fp_binder`, `dup`:
  leaves. (`fp_binder` carries the binder-name
  fingerprint control; `dup` shares its last component with `Sub.dup`, which is used.)
* `uses_gq`: a leaf. `gq_iff` (a non-`rfl` `@[simp]` iff lemma) is used by `uses_gq`'s `by simp`,
  whose proof term mentions the generated `gq_iff._simp_1`, never `gq_iff` itself: an auxiliary is
  a use of its parent, so `gq_iff` is not a leaf.
* `simp_nonrfl_fact` (`@[simp]`, proved by `omega`), `Pt.ext_fx` (`@[ext]`) and `instNonemptyPt`
  (an instance): used by no term. An attribute is a use only for an `rfl`-proved simp lemma, so
  these three are leaves.
* `base_fact`: used by `headline_one` (a plain term use), so not a leaf.
* `bound_fact`: used only inside the proof of the definition `picked` (a compiler-abstracted
  `picked._proof_N` auxiliary, attributed to its parent), so not a leaf.
* `simp_only_fact`: used by no term, but an `rfl`-proved `@[simp]` theorem, whose only possible use
  leaves no term trace (attribute-exempt), so not a leaf.
* The compiler-generated theorems of `Pt` and `Qt` (`Qt.mk.injEq`, `Qt.mk.inj`,
  `Qt.mk.sizeOf_spec`, ...) are auxiliaries attributed to their structure, not population, so
  they are not leaves (`Qt.mk.inj` is used by nothing and would be one if it counted).
* The `rfl_*` lemmas are proved by `rfl` and named only in a rewriting tactic call (`simp only`,
  `dsimp only`, `simpa`), in a tactic macro, or through an `open`ed namespace. `rfl` proofs
  leave no term in the calling proof, so the environment shows them as unused: the census lists
  them as leaves and the source scan removes them. (`rw` does leave one, so it is not listed.) `Sub.dup` is named through its own namespace.
-/
namespace LeafFixture

def step (n : Nat) : Nat := n + 1

theorem base_fact : 1 + 1 = 2 := rfl

theorem bound_fact : 2 < 3 := by decide

def picked : Fin 3 := ⟨2, Nat.lt_of_lt_of_le bound_fact (Nat.le_refl 3)⟩

@[simp] theorem simp_only_fact (n : Nat) : step n = n + 1 := rfl

@[simp] theorem simp_nonrfl_fact (n : Nat) : n + 0 + 0 = n := by omega

def gq (w : Nat) : Bool := decide (w = 1 ∨ w = 2)

@[simp] theorem gq_iff (w : Nat) : gq w = true ↔ w = 1 ∨ w = 2 := by simp [gq]

theorem uses_gq : gq 1 = true := by simp

structure Pt where
  x : Nat

structure Qt where
  a : Nat
  b : Nat

@[ext (iff := false)] theorem Pt.ext_fx {a b : Pt} (h : a.x = b.x) : a = b := by
  cases a; cases b; simp_all

instance : Nonempty Pt := ⟨⟨0⟩⟩

theorem rfl_simp_lemma : step 1 = 2 := rfl
theorem rfl_rw_lemma : step 2 = 3 := rfl
theorem rfl_dsimp_lemma : step 3 = 4 := rfl
theorem rfl_simpa_lemma : step 4 = 5 := rfl
theorem rfl_macro_lemma : step 5 = 6 := rfl
theorem rfl_macro2_lemma : step 8 = 9 := rfl
theorem rfl_open_lemma : step 6 = 7 := rfl

theorem dup : step 7 = 8 := rfl

theorem fp_binder (n : Nat) : n + 0 = n := rfl

macro "leaf_fixture_tac" : tactic => `(tactic| simp only [rfl_macro_lemma])

-- a macro nothing invokes: the lemma it names is used only by this text
macro "leaf_fixture_unused_tac" : tactic => `(tactic| exact rfl_macro2_lemma)

namespace Sub
theorem dup : step 7 = 8 := rfl

theorem uses_sub_dup : step 7 = 8 := by
  simp only [dup]
end Sub

theorem uses_simp : step 1 = 2 := by
  simp only [rfl_simp_lemma]

theorem uses_rw : step 2 = 3 := by
  rw [rfl_rw_lemma]

theorem uses_dsimp : step 3 = 4 := by
  dsimp only [rfl_dsimp_lemma]

theorem uses_simpa : step 4 = 5 := by
  simpa [rfl_simpa_lemma]

theorem uses_macro : step 5 = 6 := by
  leaf_fixture_tac

theorem headline_one : (1 + 1 = 2) ∧ True := ⟨base_fact, trivial⟩

theorem headline_calls : (step 1 = 2) ∧ (step 2 = 3) ∧ (step 3 = 4) ∧ (step 4 = 5) ∧
    (step 5 = 6) ∧ (step 7 = 8) :=
  ⟨uses_simp, uses_rw, uses_dsimp, uses_simpa, uses_macro, Sub.uses_sub_dup⟩

theorem headline_two : picked.val = 2 := rfl

end LeafFixture

namespace Elsewhere
open LeafFixture

theorem headline_open : step 6 = 7 := by
  simp only [rfl_open_lemma]
end Elsewhere
