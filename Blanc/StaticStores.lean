-- StaticStores.lean : a body that must write storage cannot run in a static frame.

import Blanc.CommonProofs

/-!
# Storing bodies and static frames

`SSTORE` halts in a static frame, so a `Func` every path of which either
reaches an `SSTORE` or cannot run at all is evidence that the frame it ran in
was not static. This turns a successful run into the `isStatic = false` side
condition a caller would otherwise have to assume.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

/-- A body every successful run of which passes an `SSTORE`. The `never` leaf
covers bodies that cannot run at all. -/
inductive StoresOrHalts (fs : List Func) : Func → Prop
  | store {f : Func} : StoresOrHalts fs (sstore ::: f)
  | next {i : Ninst} {f : Func} (h : StoresOrHalts fs f) :
      StoresOrHalts fs (i ::: f)
  | branch {f g : Func} (hf : StoresOrHalts fs f) (hg : StoresOrHalts fs g) :
      StoresOrHalts fs (Func.branch f g)
  | call {k : Nat} {f : Func} (hget : fs[k]? = some f)
      (h : StoresOrHalts fs f) : StoresOrHalts fs (Func.call k)
  | never {f : Func} (h : ∀ {e : Sevm} {s r : Devm}, ¬ Func.Run fs e s f r) :
      StoresOrHalts fs f

/-- A body that cannot avoid a storage write cannot run in a static frame. -/
theorem StoresOrHalts.isStatic_eq_false {fs : List Func} {f : Func}
    (h : StoresOrHalts fs f) :
    ∀ {e : Sevm} {s r : Devm}, Func.Run fs e s f r → e.isStatic = false := by
  induction h with
  | store =>
      intro e s r run
      cases run with
      | next hi _ => exact Blanc.of_run_sstore_not_static hi
  | next _ ih =>
      intro e s r run
      cases run with
      | next _ hf => exact ih hf
  | branch _ _ ihf ihg =>
      intro e s r run
      rcases of_run_branch run with ⟨_, _, hzero⟩ | ⟨_, _, _, _, _, _, hsucc⟩
      · exact ihf hzero
      · exact ihg hsucc
  | call hget _ ih =>
      intro e s r run
      cases run with
      | call hget' _ hbody =>
          rw [hget] at hget'
          cases Option.some.inj hget'
          exact ih hbody
  | never hnever =>
      intro e s r run
      exact absurd run hnever

/-- A named `Line` prefix does not change whether the body must store.

Passing the prefix explicitly keeps a long staging line out of structural
constructor search. -/
theorem StoresOrHalts.prepend {fs : List Func} (l : Line) {f : Func}
    (h : StoresOrHalts fs f) : StoresOrHalts fs (l +++ f) := by
  induction l with
  | nil => exact h
  | cons i l ih => exact StoresOrHalts.next ih

/-- Walk a `StoresOrHalts` goal through instruction and branch structure.
Supply `with tac` to discharge contract-specific calls. Long `Line` prefixes
must be named explicitly with `stores_line`; this tactic never searches for an
arbitrary prefix split. -/
syntax "stores_structure" (ppSpace "with" ppSpace tacticSeq)? : tactic
macro_rules
  | `(tactic| stores_structure) =>
    `(tactic| repeat' first
        | exact StoresOrHalts.store
        | exact StoresOrHalts.never not_run_revert
        | apply StoresOrHalts.next
        | apply StoresOrHalts.branch)
  | `(tactic| stores_structure with $d:tacticSeq) =>
    `(tactic| repeat' first
        | exact StoresOrHalts.store
        | exact StoresOrHalts.never not_run_revert
        | apply StoresOrHalts.next
        | apply StoresOrHalts.branch
        | ($d))

/-- Remove one explicitly supplied `Line` prefix from a `StoresOrHalts` goal. -/
syntax "stores_line" ppSpace term : tactic
macro_rules
  | `(tactic| stores_line $l:term) =>
    `(tactic| apply StoresOrHalts.prepend $l)

end Blanc
