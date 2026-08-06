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

/-! ## The bridge

The mirror of `Blanc/Compiled.lean`'s `Func.exec_of_runCompiled_core`, with the
outcome generalised.  It is a near-copy on purpose, and the copy is deliberate
rather than reluctant: `Func.exec_of_runCompiled_core` is consumed by two
audited theorems, and making it a corollary of this one would rewrite their
proof terms for no gain (`~/plans/error-genre.md`, decision E5).

Four of the five cases transcribe with no change at all, because none of the
machinery they use ever mentions the outcome:

* `Evm.branch_zero_steps`, `Evm.branch_succ_steps` and `Evm.call_steps` produce
  `Evm.step … = .cont …` equations from the rule's gas frame, headroom and
  jumpability, and a step equation says nothing about where the frame ends;
* `Ninst.exec_of_stepRun` is *already* stated for a general `exn : Execution` —
  it consumes `Ninst.StepRun … (.ok devmMid)` for the instruction it steps over
  and passes the tail's outcome through untouched.

The fifth case, `.last`, is the whole difference, and it is one word wide:
`Exec.halt` takes `Evm.step ⟨pc, sevm, devm⟩ = .halt ex` for **any** `ex`, so
the same three tactics close it against `Linst.Run sevm devm i ex` that closed
it against `Linst.Run sevm devm i (.ok devm')`.

There is no `pcFree` hypothesis and no biconditional.  This is the construction
direction only: a PC-using program has no `RunCompiledTo` witness to begin with,
so nothing needs excluding, and the inversion direction — which would need
`pcFree` and an induction over the execution — is a named non-goal of the arc
this module belongs to. -/

theorem Func.exec_of_runCompiledTo_core :
    ∀ {f₀ : Func} {fs' : List Func} {sevm : Sevm} {FS : List Func}
      {devm : Devm} {p : Func} {ex : Execution},
      Func.RunCompiledTo FS sevm devm p ex →
      some sevm.code.toList = Prog.compile ⟨f₀, fs'⟩ →
      FS = f₀ :: fs' →
      ∀ pc,
        subcode sevm.code.toList pc (Func.compile (table 0 (f₀ :: fs')) pc p) →
        noPushBefore sevm.code pc 32 = true →
        Nonempty (Exec pc sevm devm ex) := by
  intro f₀ fs' sevm FS devm p ex h_run
  induction h_run with
  | zero h_room h_pop h_f ih =>
    intro h_eq hFS pc sub hb
    rcases subcode_compile_branch_jumpable sub hb with
      ⟨loc, h_loc_eq, h_loc, h_push, h_jumpi, h_subp, h_bp, h_jd, h_jp, h_subq, h_bq⟩
    rcases Evm.branch_zero_steps h_push h_jumpi h_loc h_room h_pop with ⟨h1, h2⟩
    obtain ⟨excf⟩ := ih h_eq hFS (pc + 4) h_subp h_bp
    exact ⟨Exec.cont h1 (Exec.cont h2 excf)⟩
  | succ h_ne h_room h_pop h_g ih =>
    intro h_eq hFS pc sub hb
    rcases subcode_compile_branch_jumpable sub hb with
      ⟨loc, h_loc_eq, h_loc, h_push, h_jumpi, h_subp, h_bp, h_jd, h_jp, h_subq, h_bq⟩
    rcases Evm.branch_succ_steps h_push h_jumpi h_jd h_jp h_loc h_ne h_room h_pop
      with ⟨h1, h2, h3⟩
    obtain ⟨excg⟩ := ih h_eq hFS (loc + 1) h_subq h_bq
    exact ⟨Exec.cont h1 (Exec.cont h2 (Exec.cont h3 excg))⟩
  | last h_lin =>
    intro h_eq hFS pc sub hb
    refine ⟨Exec.halt ?_⟩
    rw [Evm.step_last (Linst.at_of_slice sub)]
    exact congrArg Step.halt h_lin
  | next h_n h_f ih =>
    intro h_eq hFS pc sub hb
    rcases Func.noPushBefore_next sub hb with ⟨hb', sub'⟩
    rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩
    rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩
    simp [pure] at h_rw
    rw [← h_rw] at h_slice
    rcases h_n with ⟨xl, h_filled, h_step⟩
    exact Ninst.exec_of_stepRun (Ninst.at_of_slice (List.slice_prefix h_slice))
      h_filled (h_step pc) (ih h_eq hFS _ sub' hb')
  | call h_get h_room h_burn h_f ih =>
    intro h_eq hFS pc sub hb
    subst hFS
    rcases subcode_compile_call sub with ⟨loc, p₁, h_get_tab, h_loc, h_pushAt, h_jump⟩
    have h_pf := (Prog.get?_table (m := 0)).symm.trans
      (congrArg (Prod.snd <$> ·) h_get_tab)
    rw [h_get] at h_pf
    simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at h_pf
    subst h_pf
    rcases subcode_of_get?_eq_some h_eq h_get_tab with ⟨h_jd, h_subf⟩
    have h_jpb := Prog.jumpable_of_get?_table h_eq h_get_tab
    rcases h_pushAt with ⟨le, h_push⟩
    rcases Evm.call_steps (le := le) h_push h_jump h_jd h_jpb.1 h_loc h_room h_burn
      with ⟨h1, h2, h3⟩
    obtain ⟨excf⟩ := ih h_eq rfl (loc + 1) h_subf h_jpb.2
    exact ⟨Exec.cont h1 (Exec.cont h2 (Exec.cont h3 excf))⟩

/-- **The bridge.**  A gas-exact walk of a compiled program that settles at
`ex` *is* the total `exec`'s value at pc 0.

Instantiating `ex` is the whole point: at `.ok post` this is
`Blanc/Compiled.lean`'s `Prog.exec_of_runCompiled` (which is where it stays,
unchanged); at `.error (e, post)` it is the statement Blanc could not make
before — *this call settles with **this** error, on these bytes, from this
state*.

What it does **not** say, so that nothing downstream overreads it:

* **It is not exhaustiveness.**  A witness says these conditions produce this
  outcome.  It says nothing about which other conditions might produce it, and
  no consequence of it may be read as "only these conditions revert".
* **It is not a claim about a callee.**  Any walk crossing an external call
  carries the callee's derivation as an `Xlot.Filled` premise, exactly as the
  `.ok` bridge does, so every consequence stays conditional on callee
  behaviour there.
* **It is message-call altitude.**  Both sides live at the code frame:
  intrinsic gas, the 63/64 rule and transaction validity are a further layer.
* **There is no converse.**  Not a biconditional, by design. -/
theorem Prog.exec_of_runCompiledTo {sevm : Sevm} {pre : Devm} {p : Prog}
    {ex : Execution}
    (h : Prog.RunCompiledTo sevm pre p ex)
    (h_eq : some sevm.code.toList = p.compile) :
    exec ⟨0, sevm, pre⟩ = ex := by
  rcases h with ⟨mid, h_burn, h_run⟩
  have h_eq' : some sevm.code.toList = Prog.compile ⟨p.main, p.aux⟩ := h_eq
  have h_get : (table 0 (p.main :: p.aux))[0]? = some (0, p.main) := rfl
  rcases subcode_of_get?_eq_some h_eq' h_get with ⟨h_jd, h_sub⟩
  have h_npb : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table h_eq' h_get).2
  have h1 : Evm.step ⟨0, sevm, pre⟩ = .cont 1 mid :=
    Evm.jumpdest_cont h_jd h_burn
  obtain ⟨exc⟩ :=
    Func.exec_of_runCompiledTo_core h_run h_eq' rfl 1 h_sub h_npb
  rw [← exec_iff_exec_eq]
  exact ⟨Exec.cont h1 exc⟩

end Blanc
