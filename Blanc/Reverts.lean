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

/-! ## The constructor side

`Blanc/Forward.lean` wraps `Func.RunCompiled`'s three rules that need a frame
(`runCompiled_branch_zero`, `runCompiled_branch_succ`, `runCompiled_call'`) and
its program entry (`runCompiled_intro`) so that a construction applies one
lemma per node instead of a lemma plus a fourteen-field record.  The mirrors
are here, and they are here rather than in a later step because the relation is
this module's: a walk parameterised by "head constant plus four rule names"
needs those four names to exist, and they belong beside the relation they
build.

The premises, the costs and the additive gas convention are `Forward.lean`'s
unchanged; only the relation and the terminal outcome differ. -/

/-- The `.zero` arm of a `branch`: the `JUMPI` condition is `0`, the arm falls
through, and it pays `PUSH2` and `JUMPI` only. -/
lemma Func.runCompiledTo_branch_zero {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f g : Func} {ex : Execution} {s : List B256} {G : Nat}
    (h_stk : devm.stack = 0 :: s) (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gHigh))
    (h_arm : Func.RunCompiledTo fs sevm (devm.setMach ⟨s, devm.memory, G⟩) f ex) :
    Func.RunCompiledTo fs sevm devm (.branch f g) ex :=
  .zero h_room (Devm.popBurnBy_setMach h_stk h_gas) h_arm

/-- The `.succ` arm of a `branch`: the condition is nonzero, so the arm is
reached by a jump and pays the target's `JUMPDEST` on top. -/
lemma Func.runCompiledTo_branch_succ {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f g : Func} {ex : Execution} {w : B256} {s : List B256} {G : Nat}
    (h_ne : w ≠ 0) (h_stk : devm.stack = w :: s)
    (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gHigh + gJumpdest))
    (h_arm : Func.RunCompiledTo fs sevm (devm.setMach ⟨s, devm.memory, G⟩) g ex) :
    Func.RunCompiledTo fs sevm devm (.branch f g) ex :=
  .succ h_ne h_room (Devm.popBurnBy_setMach h_stk h_gas) h_arm

/-- An internal `.call`: a tail jump into the flat table.  It is **not** an
external call — it carries no `Xlot` obligation at all, only the table lookup,
the headroom and `PUSH2; JUMP; JUMPDEST`'s gas. -/
lemma Func.runCompiledTo_call' {fs : List Func} {sevm : Sevm} {devm : Devm}
    {k : Nat} {f : Func} {ex : Execution} {G : Nat} (h_get : fs[k]? = some f)
    (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gMid + gJumpdest))
    (h_body : Func.RunCompiledTo fs sevm
      (devm.setMach ⟨devm.stack, devm.memory, G⟩) f ex) :
    Func.RunCompiledTo fs sevm devm (.call k) ex :=
  .call h_get h_room (Devm.burnBy_setMach_gas h_gas) h_body

/-- The program entry: `Table.compile`'s leading `JUMPDEST` and nothing else,
mirroring `Prog.runCompiled_intro`.  Reusing the `.call` rule here would charge
`gVerylow + gMid` for a `PUSH2; JUMP` the entry never emits. -/
lemma Prog.runCompiledTo_intro {sevm : Sevm} {devm mid : Devm} {p : Prog}
    {ex : Execution} {G : Nat} (h_gas : devm.gasLeft = G + gJumpdest)
    (h_mid : mid = devm.setMach ⟨devm.stack, devm.memory, G⟩)
    (h_main : Func.RunCompiledTo (p.main :: p.aux) sevm mid p.main ex) :
    Prog.RunCompiledTo sevm devm p ex := by
  subst h_mid
  exact ⟨_, Devm.burnBy_setMach_gas h_gas, h_main⟩

/-! ## The terminal instruction that reverts

`Blanc/Forward.lean` evaluates `Linst.run` forward on `.ret` only, and says why:
`.stop` needs nothing, and `.rev` and `.dest` do not end in `.ok`.  With the
relation generalised, `.rev` becomes statable, and it is the terminal
instruction this whole genre ends at.

`Linst.run … .rev` and `Linst.run … .ret` are the *same five steps* — pop the
offset, pop the size, charge the window's expansion, read it back, attach it as
output — differing only in the constructor they wrap the result in.  So the
lemma below is `Linst.run_ret_eq_ok`'s proof verbatim with `.error ⟨.revert, ·⟩`
in place of `.ok`.  That symmetry is worth naming, because it is also the
reason nothing about error *taxonomy* appears here: `EvmError.revert` is a
nullary constructor with no `ErrorDetail`, so there is nothing to pin beyond
the constructor itself. -/

/-- `Linst.run` on a `REVERT`, evaluated forward. -/
lemma Linst.run_rev_eq_error {sevm : Sevm} {devm : Devm} {i sz : B256}
    {s : List B256} {out : Bytes} {d' : Devm}
    (h_stk : devm.stack = i :: sz :: s)
    (h_gas : devm.extCost [⟨i.toNat, sz.toNat⟩] ≤ devm.gasLeft)
    (h_read : (devm.setMach ⟨s, devm.memory,
        devm.gasLeft - devm.extCost [⟨i.toNat, sz.toNat⟩]⟩).memRead
          i.toNat sz.toNat = ⟨out, d'⟩) :
    Linst.run sevm devm .rev = .error ⟨.revert, d'.withOutput out⟩ := by
  show (do
    let ⟨index, d⟩ ← devm.popToNat
    let ⟨size, d⟩ ← d.popToNat
    let cost := d.extCost [⟨index, size⟩]
    let d ← chargeGas cost d
    let ⟨output, d⟩ := d.memRead index size
    let d := d.withOutput output
    Except.error ⟨.revert, d⟩) = _
  rw [Devm.popToNat_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨sz :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  have h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨i.toNat, sz.toNat⟩] = devm.extCost [⟨i.toNat, sz.toNat⟩] := rfl
  rw [h_ext, chargeGas_eq_ok
    (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
    Devm.stack_setMach]
  rw [h_read]

/-- `REVERT`, at the relation's altitude.  The memory read is handed in rather
than written out, for the reason `Func.runCompiled_ret`'s docstring gives and
`Devm.memRead_word_fst`'s explains at length: writing a memory image into a
conclusion makes the unifier reduce `Devm.memory devm` to weak head normal
form. -/
lemma Func.runCompiledTo_rev {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i sz : B256} {s : List B256} {out : Bytes} {d' : Devm} {G : Nat}
    (h_stk : devm.stack = i :: sz :: s)
    (h_gas : devm.gasLeft = G + devm.extCost [⟨i.toNat, sz.toNat⟩])
    (h_read : (devm.setMach ⟨s, devm.memory, G⟩).memRead i.toNat sz.toNat
      = ⟨out, d'⟩) :
    Func.RunCompiledTo fs sevm devm (.last .rev)
      (.error (.revert, d'.withOutput out)) := by
  have h_eq : devm.gasLeft - devm.extCost [⟨i.toNat, sz.toNat⟩] = G := by omega
  refine Func.RunCompiledTo.last ?_
  show Linst.run sevm devm .rev = _
  exact Linst.run_rev_eq_error (out := out) (d' := d') h_stk (by omega)
    (by rw [h_eq]; exact h_read)

/-- `REVERT` with the window's expansion charge named, for the same reason
`Func.runCompiled_ret_of` exists: a generator cannot name the successor's gas
account until the charge is a number. -/
lemma Func.runCompiledTo_rev_of {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i sz : B256} {s : List B256} {out : Bytes} {d' : Devm} {G e : Nat}
    (h_stk : devm.stack = i :: sz :: s)
    (h_ext : devm.extCost [⟨i.toNat, sz.toNat⟩] = e)
    (h_gas : devm.gasLeft = G + e)
    (h_read : (devm.setMach ⟨s, devm.memory, G⟩).memRead i.toNat sz.toNat
      = ⟨out, d'⟩) :
    Func.RunCompiledTo fs sevm devm (.last .rev)
      (.error (.revert, d'.withOutput out)) := by
  subst h_ext
  exact Func.runCompiledTo_rev h_stk h_gas h_read

/-! ## The empty window, and `Func.rev`

`Blanc/CommonCore.lean`'s `Func.rev` is `PUSH0; PUSH0; REVERT`, and its
docstring says why the two `PUSH0`s are there: a bare `.last .rev` reverts with
whatever two words happen to be on the stack, which is an arbitrary window of
frame memory as revert data, a stack underflow, or an out-of-gas halt from the
expansion a garbage size implies.  With `(0, 0)` all three go away.

Both facts the window needs are unconditional in the offset, so neither
constrains the frame's memory:

* `memExtSize` returns the current size unchanged whenever the access size is
  `0`, so `extCost` is a difference of a number with itself;
* `Mem.read` at size `0` returns `[]` and `Mem.extend`'s size arithmetic is
  again the identity.

That is what makes the composite below take a gas premise of exactly
`gBase + gBase` — the `REVERT` itself is free — and what pins the reverting
frame's `output` to `[]`. -/

/-- An empty access window costs no memory expansion, whatever the offset and
whatever is already in memory. -/
lemma Devm.extCost_empty_window {devm : Devm} {i : Nat} :
    devm.extCost [⟨i, 0⟩] = 0 := by
  simp [Devm.extCost, memExtsSize, memExtSize]

/-- Reading an empty window yields no bytes and moves nothing. -/
lemma Devm.memRead_zero {devm : Devm} {i : Nat} :
    devm.memRead i 0 = ⟨[], devm⟩ := rfl

/-- **The `Func.rev` composite.**  `PUSH0; PUSH0; REVERT` from a state with the
gas for two `gBase` pushes, ending at `.error (.revert, …)` with the output
pinned to `[]`.

Every target in the `error-genre` arc ends here, so this is the lemma a walk
hands its deferred `.last` goal to.

Two premises, and both are tight:

* **`h_gas`** is the relation's additive form, and `gBase + gBase` is the whole
  cost — `pushCost_zero` gives each `PUSH0` `gBase`, and the `REVERT`'s empty
  window is free by `Devm.extCost_empty_window`.  A `PUSH0` is not
  syntactically a zero and `pushCost` is the right test; that is a
  `forward-witness` finding and is not re-derived here.
* **`h_room`** is `< 1023`, not `< 1024`: the *second* `PUSH0` pushes onto a
  stack that already carries the first, and `Devm.push` guards headroom on the
  stack it is pushing onto.  It implies the first push's `< 1024`.

The post-state's gas account is `G` — the frame reverts with its remaining gas
intact at this altitude. This says nothing about a *transaction*'s gas: refunds
and the 63/64 rule are a further layer. -/
lemma Func.runCompiledTo_rev_func {fs : List Func} {sevm : Sevm} {devm : Devm}
    {G : Nat} (h_gas : devm.gasLeft = G + (gBase + gBase))
    (h_room : devm.stack.length < 1023) :
    Func.RunCompiledTo fs sevm devm Func.rev
      (.error (.revert,
        (devm.setMach ⟨devm.stack, devm.memory, G⟩).withOutput [])) := by
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 pushCost_zero (G := G + gBase) (by omega)
      (by omega)) ?_
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (devm := devm.setMach
        ⟨(0 : B256) :: devm.stack, devm.memory, G + gBase⟩)
      pushCost_zero (G := G) rfl
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_rev_of (i := 0) (sz := 0) (s := devm.stack)
    rfl Devm.extCost_empty_window rfl Devm.memRead_zero

end Blanc
