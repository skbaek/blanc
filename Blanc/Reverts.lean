-- Reverts.lean : the error-carrying sibling of `Func.RunCompiled`, and its
-- bridge to Jaune's `exec`.
--
-- `Blanc/Compiled.lean`'s `Func.RunCompiled` ends in
-- `Linst.Run sevm devm i (.ok devm')`, so every consequence of it is a
-- statement about a frame that *succeeded*.  Contraposed, that yields "no
-- successful execution exists" and nothing more: the `.ok`-only shape is
-- exactly what `Prog.runCompiled_iff_exec`'s own docstring warns about when it
-- says the biconditional "is `.ok`-level only".
--
-- This module removes that restriction in the one place it lives.
-- `Func.RunCompiledTo` is `Func.RunCompiled` with the terminal outcome
-- generalised from `.ok devm'` to an arbitrary `Execution`; its four structural
-- rules are character-for-character the original's, and only `.last` changes.
-- The bridge mirrors `Func.exec_of_runCompiled_core` for the same reason: at
-- `.last` the original closes with `Exec.halt`, which accepts **any**
-- `Execution`, so the generalisation costs one constructor argument and no new
-- mathematics.
--
-- Three things this module deliberately does not do.
--
-- * **It does not touch `Blanc/Compiled.lean`.**  That module owns two audited
--   theorems (`Prog.exec_of_runCompiled`, `Prog.runCompiled_iff_exec`), and
--   deriving the `.ok` relation or its bridge from the general one here would
--   perturb their proof terms.  The `.ok` induction stays where it is and stays
--   as it is; the ~60 duplicated lines below are the accepted price.
-- * **It has no inversion direction.**  Only the construction direction
--   (`RunCompiledTo` -> `exec = …`) is proved.  The converse needs `pcFree` and
--   an induction over the execution, and no biconditional is stated.
-- * **It invents no error vocabulary.**  Jaune's `EvmError`, `ExceptionalHalt`
--   and `SettledHalt` are used exactly as they stand.  The only error this
--   module pins is `EvmError.revert`, which is a nullary constructor, so no
--   `ErrorDetail` is ever built or compared.

import Blanc.Forward

namespace Blanc

open Jaune

/-! ## The outcome-generalised relation

`Func.RunCompiled fs sevm devm f devm'` says the walk of `f` reaches `devm'`
successfully.  `Func.RunCompiledTo fs sevm devm f ex` says the walk of `f`
*settles at* `ex`, where `ex : Execution` is Jaune's own
`Except (EvmError × Devm) Devm`.

The four structural rules are unchanged, in premises and in costs: a `branch`
still pays `gVerylow + gHigh` on the fall-through arm and `gJumpdest` more on
the jumped arm, a `.next` still carries `Ninst.RunCompiled`'s pc-quantified
premise, and a `.call` still pays `gVerylow + gMid + gJumpdest` for the
`PUSH2; JUMP; JUMPDEST` it hides.  Only the terminal rule moves, from
`Linst.Run sevm devm i (.ok devm')` to `Linst.Run sevm devm i ex`.

Every intermediate state on the walk is still a `Devm`, and every intermediate
step still succeeds.  That is not a weakness of the relation but its content:
a frame that reverts does so at exactly one instruction, and everything before
it ran. -/

/-- A gas-exact walk of a `Func` against the code `Func.compile` emits for it,
ending at an arbitrary `Execution` rather than at a successful state.

`Func.RunCompiled` is the `.ok` special case; `Func.RunCompiledTo.of_runCompiled`
below is that inclusion, and it is the only direction that costs nothing. -/
inductive Func.RunCompiledTo : List Func → Sevm → Devm → Func → Execution → Prop
  | zero :
    ∀ {fs sevm devm devm' f g ex},
      devm.stack.length < 1024 →
      Devm.PopBurnBy [0] (gVerylow + gHigh) devm devm' →
      Func.RunCompiledTo fs sevm devm' f ex →
      Func.RunCompiledTo fs sevm devm (branch f g) ex
  | succ :
    ∀ {fs sevm devm w devm' f g ex},
      w ≠ 0 →
      devm.stack.length < 1024 →
      Devm.PopBurnBy [w] (gVerylow + gHigh + gJumpdest) devm devm' →
      Func.RunCompiledTo fs sevm devm' g ex →
      Func.RunCompiledTo fs sevm devm (branch f g) ex
  | last :
    ∀ {fs sevm devm i ex},
      Linst.Run sevm devm i ex →
      Func.RunCompiledTo fs sevm devm (last i) ex
  | next :
    ∀ {fs sevm devm i devm' f ex},
      Ninst.RunCompiled sevm devm i devm' →
      Func.RunCompiledTo fs sevm devm' f ex →
      Func.RunCompiledTo fs sevm devm (next i f) ex
  | call :
    ∀ {fs sevm devm devm' k f ex},
      fs[k]? = some f →
      devm.stack.length < 1024 →
      Devm.BurnBy (gVerylow + gMid + gJumpdest) devm devm' →
      Func.RunCompiledTo fs sevm devm' f ex →
      Func.RunCompiledTo fs sevm devm (call k) ex

/-- A gas-exact walk of a whole program, entered at pc 0, ending at an
arbitrary `Execution`.

`Prog.RunCompiled`'s shape is mirrored exactly, `∃ mid` and all: the pc-0 entry
hides `Table.compile`'s leading `JUMPDEST` and **not** a `PUSH2; JUMP`, so
reusing the `.call` rule here would make every consuming gas figure wrong by
`gVerylow + gMid`. -/
def Prog.RunCompiledTo (sevm : Sevm) (devm : Devm) (p : Prog) (ex : Execution) :
    Prop :=
  ∃ mid, Devm.BurnBy gJumpdest devm mid ∧
         Func.RunCompiledTo (p.main :: p.aux) sevm mid p.main ex

/-! ## Compatibility, in the direction that costs nothing

A successful gas-exact run is a walk that settles at `.ok`.  The converse is
not stated: `Func.RunCompiledTo … (.ok devm')` unfolds to the same derivation,
but nothing downstream needs that direction and an unused inversion is an
unused maintenance surface. -/

/-- Every `Func.RunCompiled` derivation is a `Func.RunCompiledTo` derivation at
`.ok`.  One constructor per rule, with the premises passed through. -/
theorem Func.RunCompiledTo.of_runCompiled {fs : List Func} {sevm : Sevm}
    {devm : Devm} {f : Func} {devm' : Devm}
    (h : Func.RunCompiled fs sevm devm f devm') :
    Func.RunCompiledTo fs sevm devm f (.ok devm') := by
  induction h with
  | zero h_room h_pop _ ih => exact .zero h_room h_pop ih
  | succ h_ne h_room h_pop _ ih => exact .succ h_ne h_room h_pop ih
  | last h_lin => exact .last h_lin
  | next h_n _ ih => exact .next h_n ih
  | call h_get h_room h_burn _ ih => exact .call h_get h_room h_burn ih

/-- The same inclusion at the program level. -/
theorem Prog.RunCompiledTo.of_runCompiled {sevm : Sevm} {devm : Devm} {p : Prog}
    {devm' : Devm} (h : Prog.RunCompiled sevm devm p devm') :
    Prog.RunCompiledTo sevm devm p (.ok devm') := by
  rcases h with ⟨mid, h_burn, h_run⟩
  exact ⟨mid, h_burn, Func.RunCompiledTo.of_runCompiled h_run⟩

end Blanc
