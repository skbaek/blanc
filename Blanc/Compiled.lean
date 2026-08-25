-- Compiled.lean : a gas-exact sibling of `Func.Run`, tied to the bytes
-- `Func.compile` actually emits.
--
-- `Func.Run` (Blanc/Semantics.lean) relates a `Func` to a `Devm` transition
-- with `Devm.Burn`'s `(· ≥ ·)` on `gasLeft` in three of its five rules, so a
-- `Func.Run` derivation constrains gas only from above.  That is the right
-- shape for safety -- every Blanc safety theorem takes a run as a *hypothesis*,
-- and a weaker hypothesis is a stronger theorem -- but it makes the relation
-- useless in goal position: a two-instruction program has a `Func.Run`
-- derivation whose gas account no EVM execution could realize.
--
-- `Func.RunCompiled` below pins each hidden instruction's cost exactly, as
-- Jaune's gas symbols rather than numerals, and adds the stack-headroom side
-- condition that the `PUSH2` in each emitted jump needs.  The price, recorded
-- and accepted, is that this is a semantics of *the compiler's output shape*:
-- a `PUSH1` peephole, a shared-`JUMPDEST` optimisation or a flipped branch
-- polarity would leave `Func.Run` and its ~76 consuming declarations untouched
-- while invalidating every rule here.  The name says so.
--
-- Nothing in this module is a liveness result.  It is the relation and the
-- forgetful bridge only; the two directions relating it to Jaune's `exec` are
-- the rest of the arc.

import Blanc.CommonCore

namespace Blanc

open Jaune

/-! ## Exact-gas frames

`Devm.Burn` and `Devm.PopBurn` relate two dynamic states with `gasLeft`
weakened to `(· ≥ ·)`.  These two are the same frames with the inequality
replaced by the exact decrement.

`a = b + cost` over `Nat` already carries `cost ≤ a`, which is exactly the
`safeSub` guard inside `chargeGas`, so no separate `gasLeft ≥ cost`
precondition is needed anywhere below. -/

/-- `Devm.Burn` with the gas decrement pinned to `cost`. -/
def Devm.BurnBy (cost : Nat) : Devm → Devm → Prop :=
  Rel {
    Rels.eq with
    gasLeft := λ a b => a = b + cost
  }

/-- `Devm.PopBurn` with the gas decrement pinned to `cost`. -/
def Devm.PopBurnBy (xs : List B256) (cost : Nat) : Devm → Devm → Prop :=
  Rel {
    Rels.eq with
    stack := Stack.Pop xs
    gasLeft := λ a b => a = b + cost
  }

/-! ## The instruction premise

The strong form: the child-execution witness is chosen once, *outside* the
quantifier over the program counter, and the step then runs to the same result
at every pc.  `∀ pc` reads as "pc-independent **and** succeeds"; it is
unsatisfiable for `Ninst.reg Rinst.pc`, which is what keeps the liveness
direction free of any side condition. -/

/-- `Ninst.Run` with the pc universally quantified inside a single choice of
child-execution slot. -/
def Ninst.RunCompiled (sevm : Sevm) (devm : Devm) (n : Ninst) (devm' : Devm) : Prop :=
  ∃ xl : Xlot, xl.Filled ∧ ∀ pc, Ninst.StepRun pc sevm devm n xl (.ok devm')

/-! ## The relation

The costs are exactly the instructions `Func.compile` emits and `Func.Run`
hides.  Derivations, against `Func.compile`:

* `.branch f g` emits `PUSH2 loc; JUMPI; <f>; JUMPDEST; <g>`.  Both arms pay
  `gVerylow` for the `PUSH2` and `gHigh` for the `JUMPI`.  The `.zero` arm --
  which is the **first** arm `f` -- falls through and pays nothing more.  The
  `.succ` arm jumps to the `JUMPDEST` in front of the **second** arm `g` and
  pays `gJumpdest` on top.
* `.call k` emits `PUSH2 loc; JUMP` and lands on the `JUMPDEST` that
  `Table.compile` puts in front of every table entry: `gVerylow + gMid +
  gJumpdest`.

Every side condition is on that rule's **pre**-state, because `Mach.push`
guards `stack.length < 1024` on the stack it is pushing onto.  On the post-pop
state the bound would be `< 1023`.  `.call` carries it too: its `PUSH2` needs
the headroom whether or not the `JUMP` pops the value straight back off. -/

/-- A gas-exact run of a `Func` against the code `Func.compile` emits for it.

Unlike `Func.Run`, a derivation here fixes `gasLeft` at every step and asserts
the stack headroom each emitted `PUSH2` requires. -/
inductive Func.RunCompiled : List Func → Sevm → Devm → Func → Devm → Prop
  | zero :
    ∀ {fs sevm devm devm' f g devm''},
      devm.stack.length < 1024 →
      Devm.PopBurnBy [0] (gVerylow + gHigh) devm devm' →
      Func.RunCompiled fs sevm devm' f devm'' →
      Func.RunCompiled fs sevm devm (branch f g) devm''
  | succ :
    ∀ {fs sevm devm w devm' f g devm''},
      w ≠ 0 →
      devm.stack.length < 1024 →
      Devm.PopBurnBy [w] (gVerylow + gHigh + gJumpdest) devm devm' →
      Func.RunCompiled fs sevm devm' g devm'' →
      Func.RunCompiled fs sevm devm (branch f g) devm''
  | last :
    ∀ {fs sevm devm i devm'},
      Linst.Run sevm devm i (.ok devm') →
      Func.RunCompiled fs sevm devm (last i) devm'
  | next :
    ∀ {fs sevm devm i devm' f devm''},
      Ninst.RunCompiled sevm devm i devm' →
      Func.RunCompiled fs sevm devm' f devm'' →
      Func.RunCompiled fs sevm devm (next i f) devm''
  | call :
    ∀ {fs sevm devm devm' k f devm''},
      fs[k]? = some f →
      devm.stack.length < 1024 →
      Devm.BurnBy (gVerylow + gMid + gJumpdest) devm devm' →
      Func.RunCompiled fs sevm devm' f devm'' →
      Func.RunCompiled fs sevm devm (call k) devm''

/-- A gas-exact run of a whole program, entered at pc 0.

`Prog.Run`'s `Func.Run … (.call 0)` shortcut is deliberately **not** reused: an
internal `.call` hides `PUSH2; JUMP; JUMPDEST` and the pc-0 entry hides only
`Table.compile`'s leading `JUMPDEST`, and no relation over `Devm` fields has a
channel that could tell them apart.  Reusing the constructor would make the
entry cost wrong by `gVerylow + gMid`. -/
def Prog.RunCompiled (sevm : Sevm) (devm : Devm) (p : Prog) (devm' : Devm) : Prop :=
  ∃ mid, Devm.BurnBy gJumpdest devm mid ∧
         Func.RunCompiled (p.main :: p.aux) sevm mid p.main devm'

/-! ## pc-freedom

`Ninst.reg Rinst.pc` is the only instruction whose observed outcome depends on
the program counter, and `Ninst.RunCompiled`'s `∀ pc` is unsatisfiable for it.
The liveness direction therefore needs no side condition -- a PC-using program
simply has no witness -- but the forward direction does: `⟨.next .pc (.last
.stop), []⟩` compiles to code that runs fine and has no `RunCompiled`
derivation, so `runCompiled_of_exec` is false for it without this hypothesis.

`Bool`-valued and structural on purpose.  `Rinst` is the only one of Jaune's
four instruction inductives without `deriving DecidableEq`, so an
inequality-shaped predicate would not be `decide`-dischargeable, while a
pattern-matching `Bool` function needs no instance at all. -/

/-- The single instruction whose result reads the program counter. -/
def Ninst.pcFree : Ninst → Bool
  | .reg .pc => false
  | _ => true

/-- pc-freedom of one `Func` body, not following `.call` edges.

`.call` is not followed here because recursion into `fs[k]` is not
well-founded: a table entry may call itself.  `Func.pcFree` closes over the
context by quantifying over the whole table instead, which is the
over-approximation the `.call` case of any proof wants anyway. -/
def Func.pcFreeBody : Func → Bool
  | .branch f g => f.pcFreeBody && g.pcFreeBody
  | .last _ => true
  | .next n f => Ninst.pcFree n && f.pcFreeBody
  | .call _ => true

/-- pc-freedom of a `Func` in a context: the body itself and every entry it
could reach through a `.call`. -/
def Func.pcFree (fs : List Func) (f : Func) : Bool :=
  f.pcFreeBody && fs.all Func.pcFreeBody

/-- pc-freedom of a whole program. -/
def Prog.pcFree (p : Prog) : Bool :=
  Func.pcFree (p.main :: p.aux) p.main

/-! ## The forgetful bridge

Every exact frame implies the loose one, so a `RunCompiled` derivation is a
`Run` derivation.  This is what keeps the existing safety surface reachable
from anything proved about the new relation.

It does **not** subsume `correct`: the forward direction of this arc needs
`Prog.pcFree`, so only `correct` restricted to pc-free programs would be a
corollary.  The unrestricted `correct` stays as it is. -/

lemma Devm.Burn.refl {devm : Devm} : Devm.Burn devm devm :=
  { stack := rfl, memory := rfl, gasLeft := Nat.le_refl _, logs := rfl,
    refundCounter := rfl, output := rfl, accountsToDelete := rfl,
    returnData := rfl, error := rfl, accessedAddresses := rfl,
    accessedStorageKeys := rfl, state := rfl, createdAccounts := rfl,
    transientStorage := rfl }

lemma Devm.Burn.of_burnBy {cost : Nat} {devm devm' : Devm}
    (h : Devm.BurnBy cost devm devm') : Devm.Burn devm devm' :=
  { stack := h.stack, memory := h.memory,
    gasLeft := by have := h.gasLeft; omega,
    logs := h.logs, refundCounter := h.refundCounter, output := h.output,
    accountsToDelete := h.accountsToDelete, returnData := h.returnData,
    error := h.error, accessedAddresses := h.accessedAddresses,
    accessedStorageKeys := h.accessedStorageKeys, state := h.state,
    createdAccounts := h.createdAccounts,
    transientStorage := h.transientStorage }

lemma Devm.PopBurn.of_popBurnBy {xs : List B256} {cost : Nat} {devm devm' : Devm}
    (h : Devm.PopBurnBy xs cost devm devm') : Devm.PopBurn xs devm devm' :=
  { stack := h.stack, memory := h.memory,
    gasLeft := by have := h.gasLeft; omega,
    logs := h.logs, refundCounter := h.refundCounter, output := h.output,
    accountsToDelete := h.accountsToDelete, returnData := h.returnData,
    error := h.error, accessedAddresses := h.accessedAddresses,
    accessedStorageKeys := h.accessedStorageKeys, state := h.state,
    createdAccounts := h.createdAccounts,
    transientStorage := h.transientStorage }

lemma Ninst.Run.of_runCompiled {sevm : Sevm} {devm : Devm} {n : Ninst} {devm' : Devm}
    (h : Ninst.RunCompiled sevm devm n devm') : Ninst.Run sevm devm n devm' := by
  rcases h with ⟨xl, h_filled, h_step⟩
  exact ⟨xl, h_filled, 0, h_step 0⟩

/-- The forgetful lemma: a gas-exact run is a run. -/
theorem Func.Run.of_runCompiled {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f : Func} {devm' : Devm} (h : Func.RunCompiled fs sevm devm f devm') :
    Func.Run fs sevm devm f devm' := by
  induction h with
  | zero _ h_pop _ ih => exact .zero (Devm.PopBurn.of_popBurnBy h_pop) ih
  | succ h_ne _ h_pop _ ih =>
    exact .succ h_ne (Devm.PopBurn.of_popBurnBy h_pop) Devm.Burn.refl ih
  | last h => exact .last h
  | next h_n _ ih => exact .next (Ninst.Run.of_runCompiled h_n) ih
  | call h_get _ h_burn _ ih => exact .call h_get (Devm.Burn.of_burnBy h_burn) ih

/-- The forgetful lemma at the program level. -/
theorem Prog.Run.of_runCompiled {sevm : Sevm} {devm : Devm} {p : Prog} {devm' : Devm}
    (h : Prog.RunCompiled sevm devm p devm') : Prog.Run sevm devm p devm' := by
  rcases h with ⟨mid, h_burn, h_run⟩
  exact Func.Run.call rfl (Devm.Burn.of_burnBy h_burn) (Func.Run.of_runCompiled h_run)

/-! ## Non-vacuity

The cheapest available check that the definition is not self-contradictory: a
concrete program with a concrete derivation.  `⟨.last .stop, []⟩` is the
proposal's counterexample program -- it compiles to `[JUMPDEST, STOP]`, whose
one hidden instruction is exactly the entry `JUMPDEST` the `Prog` rule charges
-- run here with enough gas to pay for it.

If a wrong constant or a mis-stated side condition made the relation empty at
some rule, this would not be provable. -/

/-- Burning `cost` off a state with at least that much gas is an exact burn. -/
lemma Devm.burnBy_setMach {cost : Nat} {devm : Devm} (h : cost ≤ devm.gasLeft) :
    Devm.BurnBy cost devm (devm.setMach {devm.mach with gasLeft := devm.gasLeft - cost}) :=
  { stack := rfl, memory := rfl, gasLeft := (Nat.sub_add_cancel h).symm,
    logs := rfl, refundCounter := rfl, output := rfl, accountsToDelete := rfl,
    returnData := rfl, error := rfl, accessedAddresses := rfl,
    accessedStorageKeys := rfl, state := rfl, createdAccounts := rfl,
    transientStorage := rfl }

/-- The two-instruction program `[JUMPDEST, STOP]` has a gas-exact run
whenever it can pay for its entry `JUMPDEST`. -/
theorem Prog.runCompiled_stop {sevm : Sevm} {devm : Devm}
    (h : gJumpdest ≤ devm.gasLeft) :
    Prog.RunCompiled sevm devm ⟨.last .stop, []⟩
      (devm.setMach {devm.mach with gasLeft := devm.gasLeft - gJumpdest}) :=
  ⟨_, Devm.burnBy_setMach h, .last rfl⟩

/-! ## Exact-gas inversion

`Blanc/CommonCore.lean`'s inversion lemmas already pin every `Devm` field but
`gasLeft`, which they weaken to `(· ≥ ·)`.  All of that structural work is
reused verbatim below; the only thing the forward direction of this arc has to
add is the gas *equation* the loose frame throws away, plus the stack headroom
each emitted `PUSH2` needs.

So the two lemmas here take a loose frame and an exact gas equation and return
the exact frame.  That keeps `runCompiled_of_exec_core` a thin accounting layer
over `correct_core`'s structure instead of a second copy of it. -/

/-- Upgrade a `Devm.Burn` to a `Devm.BurnBy` with the measured decrement. -/
lemma Devm.BurnBy.of_burn {cost : Nat} {devm devm' : Devm}
    (h : Devm.Burn devm devm') (hg : devm.gasLeft = devm'.gasLeft + cost) :
    Devm.BurnBy cost devm devm' :=
  { stack := h.stack, memory := h.memory, gasLeft := hg, logs := h.logs,
    refundCounter := h.refundCounter, output := h.output,
    accountsToDelete := h.accountsToDelete, returnData := h.returnData,
    error := h.error, accessedAddresses := h.accessedAddresses,
    accessedStorageKeys := h.accessedStorageKeys, state := h.state,
    createdAccounts := h.createdAccounts,
    transientStorage := h.transientStorage }

/-- Upgrade a `Devm.PopBurn` to a `Devm.PopBurnBy` with the measured
decrement. -/
lemma Devm.PopBurnBy.of_popBurn {xs : List B256} {cost : Nat} {devm devm' : Devm}
    (h : Devm.PopBurn xs devm devm') (hg : devm.gasLeft = devm'.gasLeft + cost) :
    Devm.PopBurnBy xs cost devm devm' :=
  { stack := h.stack, memory := h.memory, gasLeft := hg, logs := h.logs,
    refundCounter := h.refundCounter, output := h.output,
    accountsToDelete := h.accountsToDelete, returnData := h.returnData,
    error := h.error, accessedAddresses := h.accessedAddresses,
    accessedStorageKeys := h.accessedStorageKeys, state := h.state,
    createdAccounts := h.createdAccounts,
    transientStorage := h.transientStorage }

/-- `chargeGas`'s gas equation, kept exact.  `Devm.burn_of_chargeGas` is the
same fact with `(· ≥ ·)` in place of the equation. -/
lemma Devm.gasLeft_of_chargeGas {cost : Nat} {devm devm' : Devm}
    (h : chargeGas cost devm = .ok devm') :
    devm.gasLeft = devm'.gasLeft + cost := by
  simp only [chargeGas_def] at h
  cases hs : safeSub devm.gasLeft cost with
  | none => rw [hs] at h; cases h
  | some gas =>
    rw [hs] at h
    injection h with h'
    rw [← h']
    show devm.gasLeft = gas + cost
    revert hs
    unfold safeSub
    split
    · rename_i hle
      intro hs
      injection hs with hs
      omega
    · intro hs; cases hs

/-- Popping does not touch the gas account. -/
lemma Devm.gasLeft_of_pop {x : B256} {devm devm' : Devm}
    (h : Devm.pop devm = .ok ⟨x, devm'⟩) : devm.gasLeft = devm'.gasLeft :=
  (Devm.pop_of_pop h).gasLeft

/-! ### The three `Jinst` costs

Read off `Jinst.runCore`: `.jumpdest` charges `gJumpdest`, `.jump` pops once and
charges `gMid`, `.jumpi` pops twice and charges `gHigh`.  Neither pop moves
`gasLeft`, so each instruction's whole account is its single `chargeGas`. -/

lemma Devm.gasLeft_of_jumpdest_run {pc sevm pre pc' inter}
    (run : Jinst.Run ⟨pc, sevm, pre⟩ .jumpdest (.ok ⟨pc', inter⟩)) :
    pre.gasLeft = inter.gasLeft + gJumpdest := by
  rcases Except.bind_eq_ok run with ⟨devm, eq_charge, eq_ok⟩
  injection eq_ok with eq
  injection eq with eq_pc eq_devm
  cases eq_devm
  exact Devm.gasLeft_of_chargeGas eq_charge

lemma Devm.gasLeft_of_jump_run {pc sevm pre pc' inter}
    (run : Jinst.Run ⟨pc, sevm, pre⟩ .jump (.ok ⟨pc', inter⟩)) :
    pre.gasLeft = inter.gasLeft + gMid := by
  rcases Except.bind_eq_ok run with ⟨⟨x, devm1⟩, eq1, run⟩
  rcases Except.bind_eq_ok run with ⟨devm2, eq2, run⟩
  have h1 : pre.gasLeft = devm1.gasLeft := Devm.gasLeft_of_pop eq1
  have h2 : devm1.gasLeft = devm2.gasLeft + gMid := Devm.gasLeft_of_chargeGas eq2
  rcases Except.bind_eq_ok run with ⟨_, _, run⟩
  injection run with eq
  injection eq with eq_pc eq_devm
  cases eq_devm
  omega

lemma Devm.gasLeft_of_jumpi_run {pc sevm pre pc' inter}
    (run : Jinst.Run ⟨pc, sevm, pre⟩ .jumpi (.ok ⟨pc', inter⟩)) :
    pre.gasLeft = inter.gasLeft + gHigh := by
  rcases Except.bind_eq_ok run with ⟨⟨x, devm1⟩, eq1, run⟩
  rcases Except.bind_eq_ok run with ⟨⟨y, devm2⟩, eq2, run⟩
  rcases Except.bind_eq_ok run with ⟨devm3, eq3, run⟩
  have h1 : pre.gasLeft = devm1.gasLeft := Devm.gasLeft_of_pop eq1
  have h2 : devm1.gasLeft = devm2.gasLeft := Devm.gasLeft_of_pop eq2
  have h3 : devm2.gasLeft = devm3.gasLeft + gHigh := Devm.gasLeft_of_chargeGas eq3
  have h4 : devm3 = inter := by
    split at run
    · injection run with eq; injection eq
    · rcases Except.bind_eq_ok run with ⟨_, _, run⟩
      injection run with eq; injection eq
  rw [h4] at h3
  omega

/-! ### The `PUSH`'s cost and its headroom

`Ninst.step` on a `.push` charges before it pushes, and `Devm.push` asserts
`stack.length < 1024` on the state it is pushing onto.  `chargeGas` does not
move the stack, so that assertion is a fact about the **pre**-state -- which is
where `Func.RunCompiled`'s side conditions put it. -/

lemma Devm.pushRun_exact {x : B256} {pre inter : Devm} {cost : Nat}
    (h : (chargeGas cost pre >>= fun d => Devm.push x d) = .ok inter) :
    pre.stack.length < 1024 ∧ pre.gasLeft = inter.gasLeft + cost := by
  rcases Except.bind_eq_ok h with ⟨d, eq_charge, eq_push⟩
  have hg : pre.gasLeft = d.gasLeft + cost := Devm.gasLeft_of_chargeGas eq_charge
  have hst : pre.stack = d.stack := (Devm.burn_of_chargeGas eq_charge).stack
  rw [Devm.push_def] at eq_push
  simp only [Except.assert, bind, Except.bind] at eq_push
  by_cases h_room : d.stack.length < 1024
  · simp only [if_pos h_room] at eq_push
    injection eq_push with eq_inter
    rw [← eq_inter]
    exact ⟨hst ▸ h_room, hg⟩
  · simp only [if_neg h_room] at eq_push
    cases eq_push

/-! ## pc-independence of a pc-free `Ninst`

`Ninst.RunCompiled` asks for a single child-execution slot that works at
**every** program counter.  Only `Ninst.reg Rinst.pc` can tell the difference:
`Ninst.step`'s other two branches thread the pc solely into the *continuation*
counter, which `Step.Run` discards, and `Xinst.step` never receives it at all.
So on a pc-free instruction the strong form is free from the weak one. -/

set_option maxRecDepth 100000 in
/-- Every register instruction but `PC` ignores the program counter. -/
lemma Rinst.runCore_pc_irrel {devm : Devm} {sevm : Sevm} {r : Rinst}
    (h : r ≠ .pc) (pc pc' : Nat) :
    Rinst.runCore pc devm sevm r = Rinst.runCore pc' devm sevm r := by
  cases r <;> first | rfl | exact absurd rfl h

lemma Ninst.stepRun_pc_irrel {n : Ninst} (h : Ninst.pcFree n = true)
    {sevm : Sevm} {devm : Devm} {xl : Xlot} {ex : Execution} {pc pc' : Nat}
    (hs : Ninst.StepRun pc sevm devm n xl ex) :
    Ninst.StepRun pc' sevm devm n xl ex := by
  cases n with
  | push xs le =>
    rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hs ⊢
    exact hs
  | reg r =>
    have hr : r ≠ Rinst.pc := by rintro rfl; simp [Ninst.pcFree] at h
    rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hs ⊢
    refine ⟨hs.1, ?_⟩
    rw [hs.2]
    exact Rinst.runCore_pc_irrel hr pc pc'
  | exec x =>
    rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at hs ⊢
    exact hs

/-- On a pc-free instruction the weak instruction premise upgrades to the
strong one used by `Func.RunCompiled`. -/
lemma Ninst.runCompiled_of_run {sevm : Sevm} {devm : Devm} {n : Ninst}
    {devm' : Devm} (hpc : Ninst.pcFree n = true)
    (h : Ninst.Run sevm devm n devm') : Ninst.RunCompiled sevm devm n devm' := by
  rcases h with ⟨xl, hf, pc0, hs⟩
  exact ⟨xl, hf, fun pc => Ninst.stepRun_pc_irrel hpc hs⟩

/-! ## Exact-gas `Exec` inversion

The four wrappers below are `Blanc/CommonCore.lean`'s `push_of_pushAt`,
`jumpdest_at`, `jump_at` and `jumpi_at` with the measured gas equation carried
alongside the loose frame.  Three of them are pure wrappers -- `Jinst.run_of_at`
already hands back the raw `Jinst.Run`, so the existing `of_*_run` inversions
and the gas lemmas above both apply to it.  Only the `PUSH` needs its own copy
of the `cases exc` plumbing, because `push_of_pushAt` consumes the raw step
equation internally and never returns it. -/

lemma pushAt_run {pc sevm pre xs post} (exc : Exec pc sevm pre (.ok post))
    (h_at : PushAt sevm.code pc xs) (hne : xs ≠ []) :
    ∃ (inter : Devm) (exc' : Exec (pc + xs.length + 1) sevm inter (.ok post)),
      (chargeGas gVerylow pre >>= fun d => Devm.push xs.toB256 d) = .ok inter ∧
      ⟨pc + xs.length + 1, sevm, inter, .ok post, exc'⟩ ≺
        ⟨pc, sevm, pre, .ok post, exc⟩ := by
  rcases h_at with ⟨le, h_at⟩
  have hstep : Evm.step ⟨pc, sevm, pre⟩ = Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
    Evm.step_next h_at
  cases exc with
  | halt h => cases Ninst.step_ne_halt_ok (hstep.symm.trans h)
  | cont h exc' =>
    have hs := hstep.symm.trans h
    rw [Ninst.step_push, if_neg hne] at hs
    obtain ⟨hpc, hrun⟩ := Step.ofExecution_cont hs
    cases hpc
    exact ⟨_, exc', hrun, Exec.Deriv.Prec.cont h exc'⟩
  | doneOk h _ _ _ =>
    have hs := hstep.symm.trans h
    rw [Ninst.step_push] at hs
    cases Step.ofExecution_ne_spawn hs
  | runOk h _ _ _ _ =>
    have hs := hstep.symm.trans h
    rw [Ninst.step_push] at hs
    cases Step.ofExecution_ne_spawn hs

lemma pushAt_exact {pc sevm pre xs post} (exc : Exec pc sevm pre (.ok post))
    (h_at : PushAt sevm.code pc xs) (hne : xs ≠ []) :
    ∃ (inter : Devm) (exc' : Exec (pc + xs.length + 1) sevm inter (.ok post)),
      Devm.PushBurn [xs.toB256] pre inter ∧
      pre.stack.length < 1024 ∧
      pre.gasLeft = inter.gasLeft + gVerylow ∧
      ⟨pc + xs.length + 1, sevm, inter, .ok post, exc'⟩ ≺
        ⟨pc, sevm, pre, .ok post, exc⟩ := by
  rcases pushAt_run exc h_at hne with ⟨inter, exc', hrun, hprec⟩
  rcases Devm.pushRun_exact hrun with ⟨hroom, hgas⟩
  exact ⟨inter, exc', Devm.pushBurn_of_run hrun, hroom, hgas, hprec⟩

lemma jumpdest_at_exact {pc sevm pre post}
    (exc : Exec pc sevm pre (.ok post)) (jat : Jinst.At sevm.code pc .jumpdest) :
    ∃ (inter : Devm) (exc' : Exec (pc + 1) sevm inter (.ok post)),
      Devm.Burn pre inter ∧
      pre.gasLeft = inter.gasLeft + gJumpdest ∧
      ⟨pc + 1, sevm, inter, .ok post, exc'⟩ ≺ ⟨pc, sevm, pre, .ok post, exc⟩ := by
  rcases Jinst.run_of_at exc jat with ⟨pc', inter, exc', run, prec⟩
  have hgas := Devm.gasLeft_of_jumpdest_run run
  rcases of_jumpdest_run run with ⟨eq_pc, burn⟩
  cases eq_pc
  exact ⟨inter, exc', burn, hgas, prec⟩

lemma jump_at_exact {pc sevm pre post}
    (exc : Exec pc sevm pre (.ok post)) (jat : Jinst.At sevm.code pc .jump) :
    ∃ (x : B256) (inter : Devm) (exc' : Exec x.toNat sevm inter (.ok post)),
      Devm.PopBurn [x] pre inter ∧
      pre.gasLeft = inter.gasLeft + gMid ∧
      jumpable sevm.code x.toNat = true ∧
      ⟨x.toNat, sevm, inter, .ok post, exc'⟩ ≺ ⟨pc, sevm, pre, .ok post, exc⟩ := by
  rcases Jinst.run_of_at exc jat with ⟨pc', inter, exc', run, prec⟩
  have hgas := Devm.gasLeft_of_jump_run run
  rcases of_jump_run run with ⟨x, eq_pc, pb, jp⟩
  cases eq_pc
  exact ⟨x, inter, exc', pb, hgas, jp, prec⟩

lemma jumpi_at_exact {pc sevm pre post}
    (exc : Exec pc sevm pre (.ok post)) (jat : Jinst.At sevm.code pc .jumpi) :
    ( ∃ (x : B256) (inter : Devm) (exc' : Exec (pc + 1) sevm inter (.ok post)),
        Devm.PopBurn [x, 0] pre inter ∧
        pre.gasLeft = inter.gasLeft + gHigh ∧
        ⟨pc + 1, sevm, inter, .ok post, exc'⟩ ≺
          ⟨pc, sevm, pre, .ok post, exc⟩ ) ∨
    ( ∃ (x y : B256) (inter : Devm) (exc' : Exec x.toNat sevm inter (.ok post)),
        Devm.PopBurn [x, y] pre inter ∧
        pre.gasLeft = inter.gasLeft + gHigh ∧
        jumpable sevm.code x.toNat = true ∧ y ≠ 0 ∧
        ⟨x.toNat, sevm, inter, .ok post, exc'⟩ ≺
          ⟨pc, sevm, pre, .ok post, exc⟩ ) := by
  rcases Jinst.run_of_at exc jat with ⟨pc', inter, exc', run, prec⟩
  have hgas := Devm.gasLeft_of_jumpi_run run
  rcases of_jumpi_run run with ⟨x, pc_eq, pb⟩ | ⟨x, y, pc_eq, pb, je, ne⟩
  · left; cases pc_eq; exact ⟨x, inter, exc', pb, hgas, prec⟩
  · right; cases pc_eq; exact ⟨x, y, inter, exc', pb, hgas, je, ne, prec⟩

/-! ### pc-freedom, projected onto the sub-`Func`s a proof descends into -/

lemma Func.pcFree_next {fs : List Func} {n : Ninst} {p : Func}
    (h : Func.pcFree fs (.next n p) = true) :
    Ninst.pcFree n = true ∧ Func.pcFree fs p = true := by
  simp only [Func.pcFree, Func.pcFreeBody, Bool.and_eq_true] at h ⊢
  exact ⟨h.1.1, h.1.2, h.2⟩

lemma Func.pcFree_branch {fs : List Func} {p q : Func}
    (h : Func.pcFree fs (.branch p q) = true) :
    Func.pcFree fs p = true ∧ Func.pcFree fs q = true := by
  simp only [Func.pcFree, Func.pcFreeBody, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩

lemma Func.pcFree_call {fs : List Func} {k : Nat} {p : Func}
    (h : Func.pcFree fs (.call k) = true) (hg : fs[k]? = some p) :
    Func.pcFree fs p = true := by
  simp only [Func.pcFree, Func.pcFreeBody, Bool.and_eq_true] at h ⊢
  exact ⟨List.all_eq_true.mp h.2 p (List.mem_of_getElem? hg), h.2⟩

/-! ## The forward direction

`Func.runCompiled_of_exec_core` is the exact-gas strengthening of
`Blanc/CommonCore.lean`'s `correct_core`.  The recursion (`Exec.Deriv.strongRec`
over `Prec`), the `subcode` side condition and every structural step are
`correct_core`'s, reused rather than reproved; what this adds at each rule is
the gas *equation* and the stack headroom `Func.RunCompiled` demands.

The `Prog.pcFree` hypothesis is what buys `Ninst.RunCompiled`'s `∀ pc`: an
`Exec` derivation runs at one program counter, and only `PC` can tell that
counter from any other. -/

def Func.RunCompiledIfOk (fs : List Func) (sevm : Sevm) (devm : Devm) (f : Func) :
    Execution → Prop
  | .error _ => True
  | .ok devm' => Func.RunCompiled fs sevm devm f devm'

theorem Func.runCompiled_of_exec_core (f : Func) (fs : List Func) :
    ∀ (pk : Exec.Deriv) (p : Func),
      Func.pcFree (f :: fs) p = true →
      some pk.sevm.code.toList = Prog.compile ⟨f, fs⟩ →
      subcode pk.sevm.code.toList pk.pc (Func.compile (table 0 (f :: fs)) pk.pc p) →
      Func.RunCompiledIfOk (f :: fs) pk.sevm pk.devm p pk.exn := by
  apply Exec.Deriv.strongRec; intro pk ih p h_pcf h_eq sub
  rcases pk with ⟨pc, sevm, pre, exn, exc⟩
  simp only
  rcases exn with _ | post; {constructor}
  match p with
  | .last l =>
    exact Func.RunCompiled.last <| Linst.run_of_at exc <| Linst.at_of_slice sub
  | .next n p =>
    rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩
    rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩; clear h_eq'
    simp [pure] at h_rw
    rw [← h_rw] at h_slice
    clear h_rw cd
    have h_at : Ninst.At sevm.code pc n := by
      apply Ninst.at_of_slice
      apply List.slice_prefix h_slice
    rcases @Ninst.run_of_at pc sevm pre n post exc h_at with
      ⟨inter, exc', h_run, h_prec⟩
    rcases Func.pcFree_next h_pcf with ⟨h_n, h_p⟩
    apply @Func.RunCompiled.next (f :: fs) sevm pre n inter p post
      (Ninst.runCompiled_of_run h_n h_run)
    have quz :
      subcode sevm.code.toList (pc + n.size)
        (Func.compile (table 0 (f :: fs)) (pc + n.size) p) := by
      rw [h_eq'']
      simp only [subcode]
      rw [Ninst.size_eq_length_toBytes]
      apply List.slice_suffix h_slice
    exact ih ⟨pc + n.size, sevm, inter, .ok post, exc'⟩
      (Exec.Deriv.lt_of_prec h_prec) p h_p h_eq quz
  | .branch p q =>
    rcases subcode_compile_branch sub with
      ⟨loc, h_loc, pushAt, h_jumpi, h_scp, h_jumpdest, h_scq⟩
    rcases Func.pcFree_branch h_pcf with ⟨h_pp, h_pq⟩
    have h :
        ∃ (devm' : Devm) (exc' : Exec (pc + 3) sevm devm' (.ok post)),
          Devm.PushBurn [Nat.toB256 loc] pre devm' ∧
          pre.stack.length < 1024 ∧
          pre.gasLeft = devm'.gasLeft + gVerylow ∧
          ⟨pc + 3, sevm, devm', .ok post, exc'⟩ ≺
            ⟨pc, sevm, pre, .ok post, exc⟩ := by
      simp at pushAt
      rcases pushAt_exact exc ⟨_, pushAt⟩ (by simp) with
        ⟨s', cr', h, h_room, h_gas, h_prec⟩
      rw [List.toB256_pair _ h_loc] at h
      exact ⟨s', cr', h, h_room, h_gas, h_prec⟩
    rcases h with ⟨devm', exc', pushBurn, h_room, h_gas1, h_prec⟩
    rcases jumpi_at_exact exc' h_jumpi with
        ⟨x, devm'', exc'', popBurn, h_gas2, prec⟩
      | ⟨x, y, devm'', exc'', popBurn, h_gas2, jumpable, ne, prec⟩ <;> clear h_jumpi
    · clear h_scq h_jumpdest
      have h_pop' : Devm.PopBurn [0] pre devm'' := by
        rcases (Devm.pushBurn_cons_popBurn_cons pushBurn popBurn).right
          with ⟨st, pushBurn', popBurn'⟩
        apply Devm.popBurn_of_burn_of_popBurn _ popBurn'
        apply Devm.burn_of_pushBurn_nil pushBurn'
      apply Func.RunCompiled.zero h_room
        (Devm.PopBurnBy.of_popBurn h_pop' (by omega))
      have h_lt :
          Exec.Deriv.lt
            ⟨pc + 4, sevm, devm'', .ok post, exc''⟩
            ⟨pc, sevm, pre, .ok post, exc⟩ := by
        refine' ⟨_, _, h_prec⟩
        apply Exec.Deriv.le.step _ prec
        apply Exec.Deriv.le.refl _
      exact ih ⟨pc + 4, sevm, devm'', .ok post, exc''⟩ h_lt p h_pp h_eq h_scp
    · clear h_scp
      have h_loc' : loc < 2 ^ 256 := by
        apply Nat.lt_trans h_loc
        rw [Nat.pow_lt_pow_iff_right] <;> omega
      have h : x.toNat = loc ∧ Devm.PopBurn [y] pre devm'' := by
        rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn
          with ⟨hx, st, pushBurn', popBurn'⟩
        have h_loc_toNat : loc.toB256.toNat = loc := by
          rw [B256.toNat_toB256, Nat.lo_eq_of_lt h_loc']
        rw [← congrArg B256.toNat hx, h_loc_toNat]
        exact ⟨rfl, Devm.popBurn_of_burn_of_popBurn
          (Devm.burn_of_pushBurn_nil pushBurn') popBurn'⟩
      rcases h with ⟨hx, popBurn'⟩
      rw [← hx] at h_jumpdest
      rcases jumpdest_at_exact exc'' h_jumpdest with
        ⟨inter_jd, exc_jd, burn_jd, h_gas3, prec_jd⟩
      have run : Func.RunCompiled (f :: fs) sevm inter_jd q post := by
        have h_lt :
            Exec.Deriv.lt ⟨x.toNat + 1, sevm, inter_jd, .ok post, exc_jd⟩
              ⟨pc, sevm, pre, .ok post, exc⟩ := by
          refine' ⟨_, _, h_prec⟩
          apply Exec.Deriv.le.step _ prec
          apply Exec.Deriv.le.step _ prec_jd
          apply Exec.Deriv.le.refl _
        rw [← hx] at h_scq
        exact ih ⟨x.toNat + 1, sevm, inter_jd, .ok post, exc_jd⟩ h_lt q h_pq h_eq h_scq
      exact Func.RunCompiled.succ ne h_room
        (Devm.PopBurnBy.of_popBurn
          (Devm.popBurn_of_popBurn_of_pop popBurn' burn_jd) (by omega)) run
  | .call k =>
    rcases subcode_compile_call sub with ⟨loc, p, h_get, h_loc, pushAt, h_jump⟩
    have h_get' : (f :: fs)[k]? = some p := by
      rw [← @Prog.get?_table 0 k (f :: fs), h_get]; rfl
    have hd :
      ∃ (devm' : Devm) (exc' : Exec (pc + 3) sevm devm' (.ok post)),
        Devm.PushBurn [loc.toB256] pre devm' ∧
        pre.stack.length < 1024 ∧
        pre.gasLeft = devm'.gasLeft + gVerylow ∧
        ⟨pc + 3, sevm, devm', .ok post, exc'⟩ ≺
          ⟨pc, sevm, pre, .ok post, exc⟩ := by
      rcases pushAt_exact exc pushAt (by simp) with
        ⟨inter, exc', h, h_room, h_gas, h_prec⟩
      rw [List.toB256_pair _ h_loc] at h
      exact ⟨inter, exc', h, h_room, h_gas, h_prec⟩
    rcases hd with ⟨devm', exc', h_push, h_room, h_gas1, h_prec⟩
    rcases jump_at_exact exc' h_jump with
      ⟨x, devm'', exc'', h_pop, h_gas2, h_jumpable, h_prec'⟩
    rcases subcode_of_get?_eq_some h_eq h_get with ⟨h_jd, hp⟩; clear h_get
    have h_loc' : loc < 2 ^ 256 := by
      apply Nat.lt_trans h_loc
      rw [Nat.pow_lt_pow_iff_right] <;> omega
    have h_rw : loc = x.toNat ∧ Devm.Burn pre devm'' := by
      rcases Devm.pushBurn_cons_popBurn_cons h_push h_pop
        with ⟨hx, st, pushBurn', popBurn'⟩
      have h_loc_toNat : loc.toB256.toNat = loc := by
        rw [B256.toNat_toB256_of_lt h_loc']
      rw [← congrArg B256.toNat hx, h_loc_toNat]
      exact ⟨rfl, Devm.burn_trans (Devm.burn_of_pushBurn_nil pushBurn')
        (Devm.burn_of_popBurn_nil popBurn')⟩
    rcases h_rw with ⟨h_rw, h_burn⟩
    rw [h_rw] at h_jd
    rcases jumpdest_at_exact exc'' h_jd with
      ⟨inter_jd, exc''', burn_jd, h_gas3, h_prec''⟩
    rw [h_rw] at hp
    have h_lt :
        Exec.Deriv.lt ⟨x.toNat + 1, sevm, inter_jd, .ok post, exc'''⟩
          ⟨pc, sevm, pre, .ok post, exc⟩ := by
      refine' ⟨_, _, h_prec⟩
      apply Exec.Deriv.le.step _ h_prec'
      apply Exec.Deriv.le.step _ h_prec''
      apply Exec.Deriv.le.refl _
    have run : Func.RunCompiled (f :: fs) sevm inter_jd p post :=
      ih ⟨x.toNat + 1, sevm, inter_jd, .ok post, exc'''⟩ h_lt p
        (Func.pcFree_call h_pcf h_get') h_eq hp
    exact Func.RunCompiled.call h_get' h_room
      (Devm.BurnBy.of_burn (Devm.burn_trans h_burn burn_jd) (by omega)) run

/-- The exact-gas strengthening of `correct`: a successful execution of a
compiled pc-free program yields a gas-exact run of it. -/
theorem Prog.runCompiled_of_exec (sevm : Sevm) (pre : Devm) (p : Prog) (post : Devm)
    (h_pcf : Prog.pcFree p = true)
    (exc : Exec 0 sevm pre (.ok post))
    (eq : some sevm.code.toList = p.compile) :
    Prog.RunCompiled sevm pre p post := by
  rcases @subcode_of_get?_eq_some p.main p.aux sevm.code 0 _ p.main eq rfl
    with ⟨h_at, h_sub⟩
  rcases jumpdest_at_exact exc h_at with ⟨inter, exc', burn, h_gas, prec⟩
  refine ⟨inter, Devm.BurnBy.of_burn burn h_gas, ?_⟩
  exact Func.runCompiled_of_exec_core p.main p.aux
    ⟨1, sevm, inter, .ok post, exc'⟩ p.main h_pcf eq h_sub

/-! ## Jumpability of compiled jump targets -/

/-- A backward-scan specification for `noPushBefore`. -/
theorem noPushBefore_eq_true_iff (cd : ByteArray) :
    ∀ (K M : Nat), M ≤ 32 →
      (noPushBefore cd K M = true ↔
        ∀ p, K ≤ p + M → p < K → ∀ (hp : p < cd.size),
          96 ≤ cd[p].toNat → cd[p].toNat ≤ 127 →
          K + (32 - M) ≤ p + (cd[p].toNat - 95) →
          noPushBefore cd p 32 = false) := by
  intro K
  induction K with
  | zero => intro M _; simp [noPushBefore]
  | succ k ih =>
    intro M hM
    match M with
    | 0 => simp [noPushBefore]; omega
    | m + 1 =>
      rw [noPushBefore]
      have hm : m ≤ 32 := by omega
      have harith : k + 1 + (32 - (m + 1)) = k + (32 - m) := by omega
      rw [harith]
      have hthr : ∀ b : UInt8, (b < 127 - m.toUInt8) ↔ (b.toNat < 127 - m) := by
        intro b; rw [UInt8.lt_iff_toNat_lt]
        simp [UInt8.toNat_sub, Nat.toUInt8]; omega
      have hgt : ∀ b : UInt8, ((127 : UInt8) < b) ↔ (127 < b.toNat) := by
        intro b; rw [UInt8.lt_iff_toNat_lt]; rfl
      by_cases hk : k < cd.size
      · rw [dif_pos hk]
        by_cases hc : (decide (cd[k] < 127 - m.toUInt8) || decide (127 < cd[k])) = true
        · rw [if_pos hc, ih m hm]
          simp only [Bool.or_eq_true, decide_eq_true_eq, hthr, hgt] at hc
          constructor
          · intro h p h1 h2 hp h3 h4 h5
            rcases Nat.lt_or_ge p k with hlt | hge
            · exact h p (by omega) hlt hp h3 h4 h5
            · have hpk : p = k := by omega
              subst hpk; exfalso; omega
          · intro h p h1 h2 hp h3 h4 h5
            exact h p (by omega) (by omega) hp h3 h4 h5
        · simp only [Bool.or_eq_true, decide_eq_true_eq, hthr, hgt, not_or,
            Nat.not_lt] at hc
          rw [if_neg (by simp [hthr, hgt]; omega)]
          by_cases hreal : noPushBefore cd k 32 = true
          · rw [if_pos hreal]
            constructor
            · intro hf; cases hf
            · intro h
              rw [h k (by omega) (by omega) hk (by omega) (by omega) (by omega)] at hreal
              exact hreal
          · rw [if_neg hreal, ih m hm]
            constructor
            · intro h p h1 h2 hp h3 h4 h5
              rcases Nat.lt_or_ge p k with hlt | hge
              · exact h p (by omega) hlt hp h3 h4 h5
              · have hpk : p = k := by omega
                subst hpk; simpa using hreal
            · intro h p h1 h2 hp h3 h4 h5
              exact h p (by omega) (by omega) hp h3 h4 h5
      · rw [dif_neg hk, ih m hm]
        constructor
        · intro h p h1 h2 hp h3 h4 h5
          rcases Nat.lt_or_ge p k with hlt | hge
          · exact h p (by omega) hlt hp h3 h4 h5
          · exact (hk (by omega)).elim
        · intro h p h1 h2 hp h3 h4 h5
          exact h p (by omega) (by omega) hp h3 h4 h5

/-- **The transport lemma.**  If `k` is a position no `PUSH` immediate covers,
and `k` opens one complete instruction of span `s`, then the position just past
that instruction is again covered by no `PUSH` immediate.

The hypothesis `hinst` is what "one complete instruction of span `s` at `k`"
means at the byte level: either `cd[k]` is one of `PUSH1 … PUSH32` and `s` is
its opcode plus immediate, or `cd[k]` takes no immediate and `s` is 1.  A
position past the end of `cd` carries no constraint at all -- Jaune reads it as
`STOP` and nothing can be pushed from there. -/
theorem noPushBefore_add {cd : ByteArray} {k s : Nat}
    (hinst : ∀ (hk : k < cd.size),
      (96 ≤ cd[k].toNat ∧ cd[k].toNat ≤ 127 ∧ s = cd[k].toNat - 94) ∨
      ((cd[k].toNat < 96 ∨ 127 < cd[k].toNat) ∧ s = 1))
    (hb : noPushBefore cd k 32 = true) :
    noPushBefore cd (k + s) 32 = true := by
  rw [noPushBefore_eq_true_iff cd (k + s) 32 (le_refl 32)]
  intro p h1 h2 hp h3 h4 h5
  rcases Nat.lt_trichotomy p k with hlt | heq | hgt
  · exact (noPushBefore_eq_true_iff cd k 32 (le_refl 32)).mp hb p
      (by omega) hlt hp h3 h4 (by omega)
  · subst heq
    rcases hinst hp with ⟨_, _, hs⟩ | ⟨_, hs⟩ <;> exfalso <;> omega
  · have hk : k < cd.size := by omega
    rcases hinst hk with ⟨hlo, hhi, hs⟩ | ⟨_, hs⟩
    · by_cases hq : noPushBefore cd p 32 = true
      · exfalso
        have h := (noPushBefore_eq_true_iff cd p 32 (le_refl 32)).mp hq k
          (by omega) hgt hk hlo hhi (by omega)
        rw [h] at hb; cases hb
      · simpa using hq
    · exfalso; omega

lemma toInstType_eq_p_of_bounds {b : UInt8}
    (h1 : 96 ≤ b.toNat) (h2 : b.toNat ≤ 127) : b.toInstType = .P := by
  have hh : b.highs = 6 ∨ b.highs = 7 := by
    have h : b.highs.toNat = 6 ∨ b.highs.toNat = 7 := by
      simp [UInt8.highs, UInt8.toNat_shiftRight]; omega
    rcases h with h | h
    · left; exact UInt8.toNat_inj.mp h
    · right; exact UInt8.toNat_inj.mp h
  simp only [UInt8.toInstType]
  rcases hh with h | h <;> rw [h] <;> rfl

/-- One step of the boundary walk along a compiled block.  `(b :: ys) ++ zs`
sits at `k` and `b :: ys` is the complete encoding of one instruction, so the
"no `PUSH` immediate covers this position" property moves to `k + s`, where the
rest of the block still sits. -/
lemma noPushBefore_peel {code : ByteArray} {k s : Nat} {b : UInt8} {ys zs : Bytes}
    (h : List.Slice code.toList k ((b :: ys) ++ zs))
    (hb : noPushBefore code k 32 = true)
    (hs : s = ys.length + 1)
    (hinst : (96 ≤ b.toNat ∧ b.toNat ≤ 127 ∧ s = b.toNat - 94) ∨
             ((b.toNat < 96 ∨ 127 < b.toNat) ∧ ys = [])) :
    noPushBefore code (k + s) 32 = true ∧ List.Slice code.toList (k + s) zs := by
  have hlen : (b :: ys).length = s := by simp [hs]
  constructor
  · refine noPushBefore_add (fun hk => ?_) hb
    rw [ByteArray.getElem_of_getElem?_eq_some
      (List.get?_eq_of_slice (List.slice_prefix h)) hk]
    rcases hinst with hp | ⟨hnp, hnil⟩
    · exact Or.inl hp
    · exact Or.inr ⟨hnp, by simp [hs, hnil]⟩
  · have hsuf := List.slice_suffix h
    rwa [hlen] at hsuf

/-- No byte Jaune decodes as anything other than a `PUSH` with an immediate
lands in the range a `PUSH` opcode occupies.  With the existing
`Rinst/Xinst/Jinst/Linst.toInstType_toUInt8`, this is the only fact the whole
boundary walk needs about opcode bytes -- in particular `Rinst`'s ~70
constructors are never case-bashed. -/
lemma not_push_byte_of_ne_p {b : UInt8} (hne : b.toInstType ≠ .P) :
    b.toNat < 96 ∨ 127 < b.toNat := by
  rcases Nat.lt_or_ge b.toNat 96 with h | h
  · exact Or.inl h
  · rcases Nat.lt_or_ge 127 b.toNat with h' | h'
    · exact Or.inr h'
    · exact absurd (toInstType_eq_p_of_bounds h h') hne

/-- The instruction premise of `noPushBefore_peel` for a one-byte opcode. -/
lemma peel_inst_of_ne_p {b : UInt8} (hne : b.toInstType ≠ .P) :
    (96 ≤ b.toNat ∧ b.toNat ≤ 127 ∧ (1 : Nat) = b.toNat - 94) ∨
    ((b.toNat < 96 ∨ 127 < b.toNat) ∧ ([] : Bytes) = []) :=
  Or.inr ⟨not_push_byte_of_ne_p hne, rfl⟩

/-- The instruction premise of `noPushBefore_peel` for a `PUSH`.  `PUSH0`
(`bs = []`) takes the non-`PUSH` branch: `0x5F` reaches nothing. -/
lemma peel_inst_of_push {bs : Bytes} (le : bs.length ≤ 32) :
    (96 ≤ (pushToB8 bs).toNat ∧ (pushToB8 bs).toNat ≤ 127 ∧
      bs.length + 1 = (pushToB8 bs).toNat - 94) ∨
    (((pushToB8 bs).toNat < 96 ∨ 127 < (pushToB8 bs).toNat) ∧ bs = []) := by
  rw [toNat_pushToB8_eq le]
  match hbs : bs with
  | [] => exact Or.inr ⟨Or.inl (by simp), rfl⟩
  | x :: bs' => exact Or.inl ⟨by simp, by simp at le ⊢; omega, by simp⟩

/-- Peel one opcode that takes no immediate. -/
lemma noPushBefore_peel1 {code : ByteArray} {k : Nat} {b : UInt8} {zs : Bytes}
    (h : List.Slice code.toList k (b :: zs)) (hb : noPushBefore code k 32 = true)
    (hne : b.toInstType ≠ .P) :
    noPushBefore code (k + 1) 32 = true ∧ List.Slice code.toList (k + 1) zs := by
  refine noPushBefore_peel (ys := []) ?_ hb rfl (peel_inst_of_ne_p hne)
  simpa using h

/-- Peel the `PUSH2` that opens every jump `Func.compile` emits. -/
lemma noPushBefore_peel2 {code : ByteArray} {k : Nat} {x y : UInt8} {zs : Bytes}
    (h : List.Slice code.toList k ([(0x61 : UInt8), x, y] ++ zs))
    (hb : noPushBefore code k 32 = true) :
    noPushBefore code (k + 3) 32 = true ∧ List.Slice code.toList (k + 3) zs :=
  noPushBefore_peel h hb rfl (Or.inl ⟨by decide, by decide, by decide⟩)

/-- The boundary walk across one `Ninst` -- what a `.next` node needs.  Every
`Ninst`, `PUSH` included, encodes to bytes that end at a boundary if they start
at one. -/
lemma Func.noPushBefore_next {code : ByteArray} {l : List (Nat × Func)}
    {k : Nat} {i : Ninst} {p : Func}
    (sub : subcode code.toList k (Func.compile l k (Func.next i p)))
    (hb : noPushBefore code k 32 = true) :
    noPushBefore code (k + i.size) 32 = true ∧
    subcode code.toList (k + i.size) (Func.compile l (k + i.size) p) := by
  rcases of_subcode sub with ⟨cd, h_eq, h_slice⟩
  rcases of_bind_eq_some h_eq with ⟨pbs, h_pbs, h⟩
  rw [← of_pure_eq_some h] at h_slice
  have key : noPushBefore code (k + i.size) 32 = true ∧
      List.Slice code.toList (k + i.size) pbs := by
    cases i with
    | reg o =>
      exact noPushBefore_peel1 h_slice hb (by rw [Rinst.toInstType_toUInt8]; simp)
    | exec o =>
      exact noPushBefore_peel1 h_slice hb (by rw [Xinst.toInstType_toUInt8]; simp)
    | push bs le =>
      exact noPushBefore_peel h_slice hb rfl (peel_inst_of_push le)
  exact ⟨key.left, by rw [h_pbs]; exact key.right⟩

/-- **The boundary walk.**  A compiled `Func` block whose first byte no `PUSH`
immediate covers ends at a byte no `PUSH` immediate covers.

The induction mirrors `Func.compile`'s own recursion, and the boundary property
travels alongside `subcode` exactly as the program counter already does. -/
lemma Func.noPushBefore_compile {code : ByteArray} {l : List (Nat × Func)} :
    ∀ (p : Func) (k : Nat), subcode code.toList k (Func.compile l k p) →
      noPushBefore code k 32 = true →
      noPushBefore code (k + compsize p) 32 = true := by
  intro p
  induction p with
  | last o =>
    intro k sub hb
    exact (noPushBefore_peel1 (zs := []) sub hb
      (by rw [Linst.toInstType_toUInt8]; simp)).left
  | next i p ih =>
    intro k sub hb
    have key := Func.noPushBefore_next sub hb
    have hend := ih (k + i.size) key.right key.left
    have harith : k + i.size + compsize p = k + compsize (Func.next i p) := by
      simp only [compsize, Ninst.size_eq_length_toBytes]; omega
    rwa [harith] at hend
  | branch p q ihp ihq =>
    intro k sub hb
    rcases of_subcode sub with ⟨cd, h_eq, h_slice⟩
    rcases of_bind_eq_some h_eq with ⟨pbs, h_pbs, h⟩
    rcases of_guard_eq_some h with ⟨h_loc, h'⟩
    rcases of_bind_eq_some h' with ⟨qbs, h_qbs, h''⟩
    rw [← of_pure_eq_some h''] at h_slice
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h_slice
    have h3 := noPushBefore_peel2 h_slice hb
    have h4 := noPushBefore_peel1 h3.right h3.left
      (by rw [Jinst.toInstType_toUInt8]; simp)
    have hlenp : pbs.length = compsize p := Func.length_compile h_pbs
    have harm : noPushBefore code (k + 3 + 1 + compsize p) 32 = true := by
      refine ihp (k + 3 + 1) ?_ h4.left
      rw [h_pbs]; exact List.slice_prefix h4.right
    have hjd : List.Slice code.toList (k + 3 + 1 + compsize p)
        (Jinst.toUInt8 .jumpdest :: qbs) := by
      have := List.slice_suffix h4.right
      rwa [hlenp] at this
    have h5 := noPushBefore_peel1 hjd harm (by rw [Jinst.toInstType_toUInt8]; simp)
    have h_qbs' : Func.compile l (k + 3 + 1 + compsize p + 1) q = some qbs := by
      have hidx : k + 3 + 1 + compsize p + 1 = k + pbs.length + 4 + 1 := by omega
      rw [hidx]; exact h_qbs
    have hend := ihq (k + 3 + 1 + compsize p + 1) (by rw [h_qbs']; exact h5.right) h5.left
    have harith : k + 3 + 1 + compsize p + 1 + compsize q
        = k + compsize (Func.branch p q) := by simp only [compsize]; omega
    rwa [harith] at hend
  | call n =>
    intro k sub hb
    rcases of_subcode sub with ⟨cd, h_eq, h_slice⟩
    rcases of_bind_eq_some h_eq with ⟨⟨loc, r⟩, h_get, h⟩
    rcases of_guard_eq_some h with ⟨h_lt, h'⟩
    rw [← of_pure_eq_some h'] at h_slice
    simp only [List.cons_append, List.nil_append] at h_slice
    have h3 := noPushBefore_peel2 h_slice hb
    have h4 := noPushBefore_peel1 h3.right h3.left
      (by rw [Jinst.toInstType_toUInt8]; simp)
    exact h4.left

/-- The boundary walk across one opcode, from the byte rather than from a
slice. -/
lemma noPushBefore_succ_of_getElem? {code : ByteArray} {k : Nat} {b : UInt8}
    (hbyte : code.toList[k]? = some b) (hne : b.toInstType ≠ .P)
    (hb : noPushBefore code k 32 = true) :
    noPushBefore code (k + 1) 32 = true := by
  refine noPushBefore_add (fun hk => ?_) hb
  rw [ByteArray.getElem_of_getElem?_eq_some hbyte hk]
  exact Or.inr ⟨not_push_byte_of_ne_p hne, rfl⟩

/-- The boundary walk across a whole compiled table.  Every entry sits at a
`JUMPDEST` that no `PUSH` immediate covers. -/
lemma Table.noPushBefore_compile {code : ByteArray} {l : List (Nat × Func)} :
    ∀ (c : List Func) (k : Nat) (bs : Bytes),
      Table.compile l (table k c) = some bs →
      List.Slice code.toList k bs →
      noPushBefore code k 32 = true →
      ∀ (n loc : Nat) (r : Func), (table k c)[n]? = some (loc, r) →
        noPushBefore code loc 32 = true ∧
        code.toList[loc]? = some (Jinst.toUInt8 .jumpdest) := by
  intro c
  induction c with
  | nil => intro k bs _ _ _ n loc r h_get; simp [table] at h_get
  | cons g c' ih =>
    intro k bs h_cmp h_slice hb n loc r h_get
    simp only [table] at h_cmp h_get
    rcases Table.compile_cons_eq_some h_cmp with ⟨cg, crest, h_cg, h_crest, h_bs⟩
    rw [h_bs] at h_slice
    simp only [List.cons_append, List.nil_append] at h_slice
    match n with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h_get
      rcases h_get with ⟨h1, _⟩
      subst h1
      exact ⟨hb, List.get?_eq_of_slice h_slice⟩
    | m + 1 =>
      have h1 := noPushBefore_peel1 h_slice hb (by rw [Jinst.toInstType_toUInt8]; simp)
      have hlen : cg.length = compsize g := Func.length_compile h_cg
      have harm : noPushBefore code (k + 1 + compsize g) 32 = true := by
        refine @Func.noPushBefore_compile code l g (k + 1) ?_ h1.left
        rw [h_cg]; exact List.slice_prefix h1.right
      have hrest : List.Slice code.toList (k + 1 + compsize g) crest := by
        have hs := List.slice_suffix h1.right
        rwa [hlen] at hs
      have hidx : k + 1 + compsize g = k + compsize g + 1 := by omega
      rw [hidx] at harm hrest
      simp only [List.getElem?_cons_succ] at h_get
      exact ih (k + compsize g + 1) crest h_crest hrest harm m loc r h_get

/-! ### The `Prog`-level consequences

Both are stated at the same altitude as `subcode`: the boundary condition
travels beside it, is free at the top level (`Prog` enters at pc 0), and is
consumed at exactly the two nodes that emit a jump. -/

/-- Every entry of a compiled `Prog`'s table -- the destination of every
`.call` node, and the program's own entry at pc 0 -- is a valid jump
destination, and its body starts at a position no `PUSH` immediate covers. -/
theorem Prog.jumpable_of_get?_table {f fs} {code : ByteArray} {n loc : Nat} {r : Func}
    (h_eq : some code.toList = Prog.compile ⟨f, fs⟩)
    (h_get : (table 0 (f :: fs))[n]? = some (loc, r)) :
    jumpable code loc = true ∧ noPushBefore code (loc + 1) 32 = true := by
  -- `Prog.compile` is exactly this table compilation.
  have hcmp : Table.compile (table 0 (f :: fs)) (table 0 (f :: fs)) = some code.toList :=
    h_eq.symm
  have hw := @Table.noPushBefore_compile code (table 0 (f :: fs)) (f :: fs) 0
    code.toList hcmp (List.slice_refl _) rfl n loc r h_get
  have hlt := ByteArray.lt_size_of_getElem?_eq_some hw.right
  have hbyte := ByteArray.getElem_of_getElem?_eq_some hw.right hlt
  refine ⟨?_, noPushBefore_succ_of_getElem? hw.right
    (by rw [Jinst.toInstType_toUInt8]; simp) hw.left⟩
  unfold jumpable
  rw [dif_pos hlt, hbyte, if_pos rfl]
  exact hw.left

/-- `subcode_compile_branch`, carrying the boundary condition: the `JUMPDEST`
a `.branch` node jumps to is a valid destination, and both arms start at
positions no `PUSH` immediate covers.

Note there is no `JUMPDEST` before the first arm -- `.zero` falls through -- so
the first arm's boundary comes from the `PUSH2`/`JUMPI` pair, and the target's
from walking the first arm. -/
lemma subcode_compile_branch_jumpable {code : ByteArray} {k : Nat}
    {l : List (Nat × Func)} {p q : Func}
    (h : subcode code.toList k (Func.compile l k (Func.branch p q)))
    (hb : noPushBefore code k 32 = true) :
    ∃ loc : Nat,
      loc = k + 4 + compsize p ∧
      loc < 2 ^ 16 ∧
      Ninst.At code k (.push [(loc >>> 8).toUInt8, loc.toUInt8] two_le_32) ∧
      Jinst.At code (k + 3) Jinst.jumpi ∧
      subcode code.toList (k + 4) (Func.compile l (k + 4) p) ∧
      noPushBefore code (k + 4) 32 = true ∧
      Jinst.At code loc Jinst.jumpdest ∧
      jumpable code loc = true ∧
      subcode code.toList (loc + 1) (Func.compile l (loc + 1) q) ∧
      noPushBefore code (loc + 1) 32 = true := by
  rcases of_subcode h with ⟨cd, h_eq, h_slice⟩
  rcases of_bind_eq_some h_eq with ⟨pbs, h_pbs, h'⟩
  rcases of_guard_eq_some h' with ⟨h_loc, h''⟩
  rcases of_bind_eq_some h'' with ⟨qbs, h_qbs, h'''⟩
  rw [← of_pure_eq_some h'''] at h_slice
  have hlenp : pbs.length = compsize p := Func.length_compile h_pbs
  have hpush : Ninst.At code k
      (.push [((k + pbs.length + 4) >>> 8).toUInt8, (k + pbs.length + 4).toUInt8]
        two_le_32) := by
    apply @Ninst.at_of_slice code k
    simp only [Ninst.toBytes, pushToB8L, pushToB8]
    exact List.slice_prefix h_slice
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h_slice
  have h3 := noPushBefore_peel2 h_slice hb
  have h4 := noPushBefore_peel1 h3.right h3.left
    (by rw [Jinst.toInstType_toUInt8]; simp)
  have hjumpi : Jinst.At code (k + 3) Jinst.jumpi := Jinst.at_of_slice h3.right
  rw [show k + 3 + 1 = k + 4 from by omega] at h4
  have hsubp : subcode code.toList (k + 4) (Func.compile l (k + 4) p) := by
    rw [h_pbs]; exact List.slice_prefix h4.right
  have harm : noPushBefore code (k + 4 + compsize p) 32 = true :=
    @Func.noPushBefore_compile code l p (k + 4) hsubp h4.left
  have hjd : List.Slice code.toList (k + 4 + compsize p)
      (Jinst.toUInt8 .jumpdest :: qbs) := by
    have hs := List.slice_suffix h4.right
    rwa [hlenp] at hs
  have h5 := noPushBefore_peel1 hjd harm (by rw [Jinst.toInstType_toUInt8]; simp)
  have hidx : k + pbs.length + 4 = k + 4 + compsize p := by omega
  refine ⟨k + pbs.length + 4, by omega, h_loc, hpush, hjumpi, hsubp, ?_, ?_, ?_, ?_, ?_⟩
  · exact h4.left
  · rw [hidx]; exact Jinst.at_of_slice hjd
  · rw [hidx]
    have hlt := ByteArray.lt_size_of_getElem?_eq_some (List.get?_eq_of_slice hjd)
    unfold jumpable
    rw [dif_pos hlt,
      ByteArray.getElem_of_getElem?_eq_some (List.get?_eq_of_slice hjd) hlt,
      if_pos rfl]
    exact harm
  · rw [h_qbs]; rw [hidx]; exact h5.right
  · rw [hidx]; exact h5.left

/-! ## The liveness direction: construction support

Everything below builds `Exec` derivations *from* `RunCompiled` premises --
the dual of the inversion layer above.  Where the forward direction took a
step equation apart, these lemmas evaluate the step functions forward: each
`Evm.step … = .cont …` equation is produced by running `chargeGas`, `push`
and `pop` on states whose success conditions the relation's premises supply.

The frames pin every `Devm` field, so the state the machine computes and the
state the derivation names are identified by extensionality through the
fourteen canonical projections. -/

/-- Extensionality through the fourteen canonical projections -- exactly the
fields a `Devm.Rel` frame relates, so an all-equal frame identifies states. -/
lemma Devm.eq_of_proj {a b : Devm}
    (h_stack : a.stack = b.stack) (h_memory : a.memory = b.memory)
    (h_gasLeft : a.gasLeft = b.gasLeft) (h_logs : a.logs = b.logs)
    (h_refund : a.refundCounter = b.refundCounter)
    (h_output : a.output = b.output)
    (h_del : a.accountsToDelete = b.accountsToDelete)
    (h_ret : a.returnData = b.returnData) (h_err : a.error = b.error)
    (h_aa : a.accessedAddresses = b.accessedAddresses)
    (h_ask : a.accessedStorageKeys = b.accessedStorageKeys)
    (h_state : a.state = b.state) (h_ca : a.createdAccounts = b.createdAccounts)
    (h_ts : a.transientStorage = b.transientStorage) : a = b := by
  rcases a with ⟨⟨s₁, m₁, g₁⟩, ⟨l₁, r₁, o₁, d₁, rd₁, e₁, aa₁, ak₁, ca₁⟩, ⟨st₁, ts₁⟩⟩
  rcases b with ⟨⟨s₂, m₂, g₂⟩, ⟨l₂, r₂, o₂, d₂, rd₂, e₂, aa₂, ak₂, ca₂⟩, ⟨st₂, ts₂⟩⟩
  simp only [Devm.stack, Devm.memory, Devm.gasLeft, Devm.logs,
    Devm.refundCounter, Devm.output, Devm.accountsToDelete, Devm.returnData,
    Devm.error, Devm.accessedAddresses, Devm.accessedStorageKeys, Devm.state,
    Devm.createdAccounts, Devm.transientStorage] at *
  subst_vars
  rfl

/-- Overwriting an overwritten machine keeps only the last write. -/
lemma Devm.setMach_setMach {devm : Devm} {m m' : Mach} :
    (devm.setMach m).setMach m' = devm.setMach m' := rfl

lemma Devm.memory_setMach {devm : Devm} {m : Mach} :
    (devm.setMach m).memory = m.memory := rfl

lemma Devm.gasLeft_setMach {devm : Devm} {m : Mach} :
    (devm.setMach m).gasLeft = m.gasLeft := rfl

/-- `chargeGas`, evaluated forward: with the gas to pay, it succeeds and the
whole account is the decrement. -/
lemma chargeGas_eq_ok {cost : Nat} {devm : Devm} (h : cost ≤ devm.gasLeft) :
    chargeGas cost devm =
      .ok (devm.setMach ⟨devm.stack, devm.memory, devm.gasLeft - cost⟩) := by
  rw [chargeGas_def]
  have hs : safeSub devm.gasLeft cost = some (devm.gasLeft - cost) := by
    unfold safeSub; rw [if_pos h]
  rw [hs]
  rfl

/-- `Devm.push`, evaluated forward: with headroom, it succeeds. -/
lemma Devm.push_eq_ok {x : B256} {devm : Devm} (h : devm.stack.length < 1024) :
    Devm.push x devm =
      .ok (devm.setMach ⟨x :: devm.stack, devm.memory, devm.gasLeft⟩) := by
  rw [Devm.push_def]
  simp only [Except.assert, bind, Except.bind, if_pos h]
  rfl

/-- `Devm.pop`, evaluated forward: on a cons-shaped stack, it succeeds. -/
lemma Devm.pop_eq_ok {x : B256} {s : List B256} {devm : Devm}
    (h : devm.stack = x :: s) :
    Devm.pop devm = .ok ⟨x, devm.setMach ⟨s, devm.memory, devm.gasLeft⟩⟩ := by
  rw [Devm.pop_def, h]
  rfl

/-- A `PUSH` with gas and headroom continues past itself with the value
pushed. -/
lemma Evm.push_cont {pc : Nat} {sevm : Sevm} {devm : Devm} {xs : Bytes}
    {le : xs.length ≤ 32} (hne : xs ≠ [])
    (h_at : Ninst.At sevm.code pc (.push xs le))
    (h_gas : gVerylow ≤ devm.gasLeft) (h_room : devm.stack.length < 1024) :
    Evm.step ⟨pc, sevm, devm⟩ =
      .cont (pc + xs.length + 1)
        (devm.setMach
          ⟨xs.toB256 :: devm.stack, devm.memory, devm.gasLeft - gVerylow⟩) := by
  rw [Evm.step_next h_at, Ninst.step_push, if_neg hne]
  rw [chargeGas_eq_ok h_gas]
  simp only [bind, Except.bind]
  rw [Devm.push_eq_ok (devm := devm.setMach
    ⟨devm.stack, devm.memory, devm.gasLeft - gVerylow⟩) h_room]
  rfl

/-- A `JUMPDEST` continues to the next byte, and its exact burn frame lands
the step on the frame's own far state. -/
lemma Evm.jumpdest_cont {pc : Nat} {sevm : Sevm} {devm tgt : Devm}
    (h_at : Jinst.At sevm.code pc .jumpdest)
    (h_burn : Devm.BurnBy gJumpdest devm tgt) :
    Evm.step ⟨pc, sevm, devm⟩ = .cont (pc + 1) tgt := by
  have h_gas : gJumpdest ≤ devm.gasLeft := by have := h_burn.gasLeft; omega
  have h_tgt : devm.setMach ⟨devm.stack, devm.memory, devm.gasLeft - gJumpdest⟩
      = tgt := by
    refine Devm.eq_of_proj h_burn.stack h_burn.memory ?_ h_burn.logs
      h_burn.refundCounter h_burn.output h_burn.accountsToDelete
      h_burn.returnData h_burn.error h_burn.accessedAddresses
      h_burn.accessedStorageKeys h_burn.state h_burn.createdAccounts
      h_burn.transientStorage
    show devm.gasLeft - gJumpdest = tgt.gasLeft
    have := h_burn.gasLeft; omega
  rw [Evm.step_jump h_at]
  have hrun : Jinst.run ⟨pc, sevm, devm⟩ .jumpdest = .ok ⟨pc + 1, tgt⟩ := by
    show Jinst.runCore pc devm sevm .jumpdest = _
    unfold Jinst.runCore
    rw [chargeGas_eq_ok h_gas]
    simp only [bind, Except.bind]
    rw [h_tgt]
  rw [hrun]
  rfl

/-- A `JUMPI` whose condition is zero falls through, popping both operands. -/
lemma Evm.jumpi_cont_zero {pc : Nat} {sevm : Sevm} {devm : Devm} {x : B256}
    {s : List B256}
    (h_at : Jinst.At sevm.code pc .jumpi)
    (h_stk : devm.stack = x :: 0 :: s)
    (h_gas : gHigh ≤ devm.gasLeft) :
    Evm.step ⟨pc, sevm, devm⟩ =
      .cont (pc + 1) (devm.setMach ⟨s, devm.memory, devm.gasLeft - gHigh⟩) := by
  rw [Evm.step_jump h_at]
  have hrun : Jinst.run ⟨pc, sevm, devm⟩ .jumpi =
      .ok ⟨pc + 1, devm.setMach ⟨s, devm.memory, devm.gasLeft - gHigh⟩⟩ := by
    show Jinst.runCore pc devm sevm .jumpi = _
    unfold Jinst.runCore
    rw [Devm.pop_eq_ok h_stk]
    simp only [bind, Except.bind]
    rw [Devm.pop_eq_ok
      (devm := devm.setMach ⟨(0 : B256) :: s, devm.memory, devm.gasLeft⟩) rfl]
    simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
    rw [chargeGas_eq_ok
      (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
    simp only [if_true]
    rfl
  rw [hrun]
  rfl

/-- A `JUMPI` whose condition is nonzero jumps to a valid destination,
popping both operands. -/
lemma Evm.jumpi_cont_jump {pc : Nat} {sevm : Sevm} {devm : Devm} {x w : B256}
    {s : List B256}
    (h_at : Jinst.At sevm.code pc .jumpi)
    (h_stk : devm.stack = x :: w :: s) (h_ne : w ≠ 0)
    (h_gas : gHigh ≤ devm.gasLeft)
    (h_jp : jumpable sevm.code x.toNat = true) :
    Evm.step ⟨pc, sevm, devm⟩ =
      .cont x.toNat (devm.setMach ⟨s, devm.memory, devm.gasLeft - gHigh⟩) := by
  rw [Evm.step_jump h_at]
  have hrun : Jinst.run ⟨pc, sevm, devm⟩ .jumpi =
      .ok ⟨x.toNat, devm.setMach ⟨s, devm.memory, devm.gasLeft - gHigh⟩⟩ := by
    show Jinst.runCore pc devm sevm .jumpi = _
    unfold Jinst.runCore
    rw [Devm.pop_eq_ok h_stk]
    simp only [bind, Except.bind]
    rw [Devm.pop_eq_ok
      (devm := devm.setMach ⟨w :: s, devm.memory, devm.gasLeft⟩) rfl]
    simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
    rw [chargeGas_eq_ok
      (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
    simp only [if_neg h_ne, Except.assert, if_pos h_jp]
    rfl
  rw [hrun]
  rfl

/-- A `JUMP` to a valid destination continues there, popping its operand. -/
lemma Evm.jump_cont {pc : Nat} {sevm : Sevm} {devm : Devm} {x : B256}
    {s : List B256}
    (h_at : Jinst.At sevm.code pc .jump)
    (h_stk : devm.stack = x :: s)
    (h_gas : gMid ≤ devm.gasLeft)
    (h_jp : jumpable sevm.code x.toNat = true) :
    Evm.step ⟨pc, sevm, devm⟩ =
      .cont x.toNat (devm.setMach ⟨s, devm.memory, devm.gasLeft - gMid⟩) := by
  rw [Evm.step_jump h_at]
  have hrun : Jinst.run ⟨pc, sevm, devm⟩ .jump =
      .ok ⟨x.toNat, devm.setMach ⟨s, devm.memory, devm.gasLeft - gMid⟩⟩ := by
    show Jinst.runCore pc devm sevm .jump = _
    unfold Jinst.runCore
    rw [Devm.pop_eq_ok h_stk]
    simp only [bind, Except.bind]
    rw [chargeGas_eq_ok
      (devm := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) h_gas]
    simp only [Except.assert, if_pos h_jp]
    rfl
  rw [hrun]
  rfl

/-! ## The generic instruction step, constructed

`Func.RunCompiled`'s `.next` premise is relational: one filled child slot and
a step outcome at every pc.  Constructing the `Exec` node from it is a case
analysis on the instruction's step shape -- a `.cont` for the childless kinds,
and the `doneOk` / `runOk` constructors when a call-type instruction spawns.
The spawning case is where `xl.Filled` is consumed: the callee's derivation is
a hypothesis and nothing here discharges it, which is the structural reason
liveness for a contract with an external call is conditional on callee
behaviour. -/

lemma Ninst.exec_of_stepRun {pc : Nat} {sevm : Sevm} {devm devmMid : Devm}
    {n : Ninst} {xl : Xlot} {exn : Execution}
    (h_at : Ninst.At sevm.code pc n)
    (h_filled : xl.Filled)
    (h_step : Ninst.StepRun pc sevm devm n xl (.ok devmMid))
    (h_next : Nonempty (Exec (pc + n.size) sevm devmMid exn)) :
    Nonempty (Exec pc sevm devm exn) := by
  obtain ⟨exc'⟩ := h_next
  have hstep : Evm.step ⟨pc, sevm, devm⟩ = Ninst.step ⟨pc, sevm, devm⟩ n :=
    Evm.step_next h_at
  cases n with
  | reg r =>
    rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at h_step
    refine ⟨Exec.cont ?_ exc'⟩
    rw [hstep, Ninst.step_reg, ← h_step.2]
    rfl
  | push xs le =>
    rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_step
    refine ⟨Exec.cont ?_ exc'⟩
    rw [hstep, Ninst.step_push, ← h_step.2]
    rfl
  | exec x =>
    rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at h_step
    cases hx : Xinst.step sevm devm x with
    | done e =>
      rw [hx] at h_step
      simp only [XStep.Run] at h_step
      refine ⟨Exec.cont ?_ exc'⟩
      rw [hstep, Ninst.step_exec, hx, ← h_step.2]
      rfl
    | spawn fr rsm =>
      rw [hx] at h_step
      rcases h_step with ⟨r, hframe, hex⟩
      have hstep' : Evm.step ⟨pc, sevm, devm⟩ = .spawn fr rsm (pc + 1) := by
        rw [hstep, Ninst.step_exec, hx]
        rfl
      unfold RunFrame at hframe
      rcases henter : fr.enter with r' | cevm <;> simp only [henter] at hframe
      · exact ⟨Exec.doneOk hstep' henter (hframe.2 ▸ hex.symm) exc'⟩
      · rcases hframe with ⟨raw, hxl, hr⟩
        subst hxl
        obtain ⟨excChild⟩ : Nonempty (Exec cevm.pc cevm.sta cevm.dyna raw) :=
          h_filled
        refine ⟨Exec.runOk hstep' henter excChild ?_ exc'⟩
        rw [← hr]
        exact hex.symm

/-! ## The hidden instructions of each rule, as machine steps

One lemma per jump-emitting rule.  Each turns the rule's premises -- the
exact-gas frame, the stack headroom, and Step 3's jumpability -- into the
`.cont` equations its `Exec` nodes need, with the intermediate states written
out and the final state identified with the frame's far state by
extensionality. -/

/-- `PUSH2 loc; JUMPI` with `0` on the stack: both steps of the `.zero` arm. -/
lemma Evm.branch_zero_steps {pc loc : Nat} {sevm : Sevm} {devm tgt : Devm}
    {le : ([(loc >>> 8).toUInt8, loc.toUInt8] : Bytes).length ≤ 32}
    (h_push : Ninst.At sevm.code pc (.push [(loc >>> 8).toUInt8, loc.toUInt8] le))
    (h_jumpi : Jinst.At sevm.code (pc + 3) .jumpi)
    (h_loc : loc < 2 ^ 16)
    (h_room : devm.stack.length < 1024)
    (h_pop : Devm.PopBurnBy [0] (gVerylow + gHigh) devm tgt) :
    Evm.step ⟨pc, sevm, devm⟩ =
      .cont (pc + 3)
        (devm.setMach
          ⟨loc.toB256 :: devm.stack, devm.memory, devm.gasLeft - gVerylow⟩) ∧
    Evm.step ⟨pc + 3, sevm,
        devm.setMach
          ⟨loc.toB256 :: devm.stack, devm.memory, devm.gasLeft - gVerylow⟩⟩ =
      .cont (pc + 4) tgt := by
  have h_stk : devm.stack = (0 : B256) :: tgt.stack := h_pop.stack
  have h_gas : devm.gasLeft = tgt.gasLeft + (gVerylow + gHigh) := h_pop.gasLeft
  have h_v : Bytes.toB256 [(loc >>> 8).toUInt8, loc.toUInt8] = loc.toB256 :=
    List.toB256_pair _ h_loc
  constructor
  · have h1 := Evm.push_cont (le := le) (by simp) h_push (by omega) h_room
    rw [h_v] at h1
    exact h1
  · have h2 := Evm.jumpi_cont_zero
      (devm := devm.setMach
        ⟨loc.toB256 :: devm.stack, devm.memory, devm.gasLeft - gVerylow⟩)
      (x := loc.toB256) (s := tgt.stack) h_jumpi
      (by show loc.toB256 :: devm.stack = _; rw [h_stk])
      (by show gHigh ≤ devm.gasLeft - gVerylow; omega)
    simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
      at h2
    have h_fin : devm.setMach
        ⟨tgt.stack, devm.memory, devm.gasLeft - gVerylow - gHigh⟩ = tgt := by
      refine Devm.eq_of_proj rfl h_pop.memory ?_ h_pop.logs h_pop.refundCounter
        h_pop.output h_pop.accountsToDelete h_pop.returnData h_pop.error
        h_pop.accessedAddresses h_pop.accessedStorageKeys h_pop.state
        h_pop.createdAccounts h_pop.transientStorage
      show devm.gasLeft - gVerylow - gHigh = tgt.gasLeft
      omega
    rw [h_fin] at h2
    exact h2

/-- `PUSH2 loc; JUMPI` with nonzero `w`, landing on the `JUMPDEST` before the
second arm: all three steps of the `.succ` arm. -/
lemma Evm.branch_succ_steps {pc loc : Nat} {sevm : Sevm} {devm tgt : Devm}
    {w : B256}
    {le : ([(loc >>> 8).toUInt8, loc.toUInt8] : Bytes).length ≤ 32}
    (h_push : Ninst.At sevm.code pc (.push [(loc >>> 8).toUInt8, loc.toUInt8] le))
    (h_jumpi : Jinst.At sevm.code (pc + 3) .jumpi)
    (h_jd : Jinst.At sevm.code loc .jumpdest)
    (h_jp : jumpable sevm.code loc = true)
    (h_loc : loc < 2 ^ 16)
    (h_ne : w ≠ 0)
    (h_room : devm.stack.length < 1024)
    (h_pop : Devm.PopBurnBy [w] (gVerylow + gHigh + gJumpdest) devm tgt) :
    Evm.step ⟨pc, sevm, devm⟩ =
      .cont (pc + 3)
        (devm.setMach
          ⟨loc.toB256 :: devm.stack, devm.memory, devm.gasLeft - gVerylow⟩) ∧
    Evm.step ⟨pc + 3, sevm,
        devm.setMach
          ⟨loc.toB256 :: devm.stack, devm.memory, devm.gasLeft - gVerylow⟩⟩ =
      .cont loc
        (devm.setMach
          ⟨tgt.stack, devm.memory, devm.gasLeft - gVerylow - gHigh⟩) ∧
    Evm.step ⟨loc, sevm,
        devm.setMach
          ⟨tgt.stack, devm.memory, devm.gasLeft - gVerylow - gHigh⟩⟩ =
      .cont (loc + 1) tgt := by
  have h_stk : devm.stack = w :: tgt.stack := h_pop.stack
  have h_gas : devm.gasLeft = tgt.gasLeft + (gVerylow + gHigh + gJumpdest) :=
    h_pop.gasLeft
  have h_v : Bytes.toB256 [(loc >>> 8).toUInt8, loc.toUInt8] = loc.toB256 :=
    List.toB256_pair _ h_loc
  have h_loc' : loc < 2 ^ 256 := by
    apply Nat.lt_trans h_loc
    rw [Nat.pow_lt_pow_iff_right] <;> omega
  have h_toNat : (loc.toB256).toNat = loc := B256.toNat_toB256_of_lt h_loc'
  refine ⟨?_, ?_, ?_⟩
  · have h1 := Evm.push_cont (le := le) (by simp) h_push (by omega) h_room
    rw [h_v] at h1
    exact h1
  · have h2 := Evm.jumpi_cont_jump
      (devm := devm.setMach
        ⟨loc.toB256 :: devm.stack, devm.memory, devm.gasLeft - gVerylow⟩)
      (x := loc.toB256) (w := w) (s := tgt.stack) h_jumpi
      (by show loc.toB256 :: devm.stack = _; rw [h_stk]) h_ne
      (by show gHigh ≤ devm.gasLeft - gVerylow; omega)
      (by rw [h_toNat]; exact h_jp)
    simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
      at h2
    rw [h_toNat] at h2
    exact h2
  · refine Evm.jumpdest_cont h_jd ?_
    refine
      { stack := rfl, memory := h_pop.memory,
        gasLeft := ?_, logs := h_pop.logs,
        refundCounter := h_pop.refundCounter, output := h_pop.output,
        accountsToDelete := h_pop.accountsToDelete,
        returnData := h_pop.returnData, error := h_pop.error,
        accessedAddresses := h_pop.accessedAddresses,
        accessedStorageKeys := h_pop.accessedStorageKeys,
        state := h_pop.state, createdAccounts := h_pop.createdAccounts,
        transientStorage := h_pop.transientStorage }
    show devm.gasLeft - gVerylow - gHigh = tgt.gasLeft + gJumpdest
    omega

/-- `PUSH2 loc; JUMP`, landing on the table entry's `JUMPDEST`: all three
steps of a `.call`. -/
lemma Evm.call_steps {pc loc : Nat} {sevm : Sevm} {devm tgt : Devm}
    {le : ([(loc >>> 8).toUInt8, loc.toUInt8] : Bytes).length ≤ 32}
    (h_push : Ninst.At sevm.code pc (.push [(loc >>> 8).toUInt8, loc.toUInt8] le))
    (h_jump : Jinst.At sevm.code (pc + 3) .jump)
    (h_jd : Jinst.At sevm.code loc .jumpdest)
    (h_jp : jumpable sevm.code loc = true)
    (h_loc : loc < 2 ^ 16)
    (h_room : devm.stack.length < 1024)
    (h_burn : Devm.BurnBy (gVerylow + gMid + gJumpdest) devm tgt) :
    Evm.step ⟨pc, sevm, devm⟩ =
      .cont (pc + 3)
        (devm.setMach
          ⟨loc.toB256 :: devm.stack, devm.memory, devm.gasLeft - gVerylow⟩) ∧
    Evm.step ⟨pc + 3, sevm,
        devm.setMach
          ⟨loc.toB256 :: devm.stack, devm.memory, devm.gasLeft - gVerylow⟩⟩ =
      .cont loc
        (devm.setMach
          ⟨devm.stack, devm.memory, devm.gasLeft - gVerylow - gMid⟩) ∧
    Evm.step ⟨loc, sevm,
        devm.setMach
          ⟨devm.stack, devm.memory, devm.gasLeft - gVerylow - gMid⟩⟩ =
      .cont (loc + 1) tgt := by
  have h_gas : devm.gasLeft = tgt.gasLeft + (gVerylow + gMid + gJumpdest) :=
    h_burn.gasLeft
  have h_v : Bytes.toB256 [(loc >>> 8).toUInt8, loc.toUInt8] = loc.toB256 :=
    List.toB256_pair _ h_loc
  have h_loc' : loc < 2 ^ 256 := by
    apply Nat.lt_trans h_loc
    rw [Nat.pow_lt_pow_iff_right] <;> omega
  have h_toNat : (loc.toB256).toNat = loc := B256.toNat_toB256_of_lt h_loc'
  refine ⟨?_, ?_, ?_⟩
  · have h1 := Evm.push_cont (le := le) (by simp) h_push (by omega) h_room
    rw [h_v] at h1
    exact h1
  · have h2 := Evm.jump_cont
      (devm := devm.setMach
        ⟨loc.toB256 :: devm.stack, devm.memory, devm.gasLeft - gVerylow⟩)
      (x := loc.toB256) (s := devm.stack) h_jump rfl
      (by show gMid ≤ devm.gasLeft - gVerylow; omega)
      (by rw [h_toNat]; exact h_jp)
    simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
      at h2
    rw [h_toNat] at h2
    exact h2
  · refine Evm.jumpdest_cont h_jd ?_
    refine
      { stack := h_burn.stack, memory := h_burn.memory,
        gasLeft := ?_, logs := h_burn.logs,
        refundCounter := h_burn.refundCounter, output := h_burn.output,
        accountsToDelete := h_burn.accountsToDelete,
        returnData := h_burn.returnData, error := h_burn.error,
        accessedAddresses := h_burn.accessedAddresses,
        accessedStorageKeys := h_burn.accessedStorageKeys,
        state := h_burn.state, createdAccounts := h_burn.createdAccounts,
        transientStorage := h_burn.transientStorage }
    show devm.gasLeft - gVerylow - gMid = tgt.gasLeft + gJumpdest
    omega

/-! ## The liveness direction

The induction is on the `RunCompiled` derivation itself: it is a `Prop`, the
conclusion is a `Prop`, and at `.call` the induction hypothesis is about a
strictly smaller *derivation*, so no termination measure and no gas induction
appears.  The conclusion is generalised over the program counter, and the
boundary condition `noPushBefore … pc 32` travels beside `subcode` exactly as
in the walks above -- free at pc 0, maintained per case, consumed at the two
node kinds that emit a jump.

There is no `pcFree` hypothesis: a PC-using program has no `RunCompiled`
witness in the first place, so nothing needs excluding. -/

theorem Func.exec_of_runCompiled_core :
    ∀ {f₀ : Func} {fs' : List Func} {sevm : Sevm} {FS : List Func}
      {devm : Devm} {p : Func} {devm' : Devm},
      Func.RunCompiled FS sevm devm p devm' →
      some sevm.code.toList = Prog.compile ⟨f₀, fs'⟩ →
      FS = f₀ :: fs' →
      ∀ pc,
        subcode sevm.code.toList pc (Func.compile (table 0 (f₀ :: fs')) pc p) →
        noPushBefore sevm.code pc 32 = true →
        Nonempty (Exec pc sevm devm (.ok devm')) := by
  intro f₀ fs' sevm FS devm p devm' h_run
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

/-- The liveness direction at the program level: a gas-exact run of a
compiled program *is* a successful execution from pc 0.  No `pcFree`
hypothesis -- a PC-using program has no `RunCompiled` witness to begin
with. -/
theorem Prog.exec_of_runCompiled {sevm : Sevm} {pre : Devm} {p : Prog}
    {post : Devm}
    (h : Prog.RunCompiled sevm pre p post)
    (h_eq : some sevm.code.toList = p.compile) :
    exec ⟨0, sevm, pre⟩ = .ok post := by
  rcases h with ⟨mid, h_burn, h_run⟩
  have h_eq' : some sevm.code.toList = Prog.compile ⟨p.main, p.aux⟩ := h_eq
  have h_get : (table 0 (p.main :: p.aux))[0]? = some (0, p.main) := rfl
  rcases subcode_of_get?_eq_some h_eq' h_get with ⟨h_jd, h_sub⟩
  have h_npb : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table h_eq' h_get).2
  have h1 : Evm.step ⟨0, sevm, pre⟩ = .cont 1 mid :=
    Evm.jumpdest_cont h_jd h_burn
  obtain ⟨exc⟩ :=
    Func.exec_of_runCompiled_core h_run h_eq' rfl 1 h_sub h_npb
  rw [← exec_iff_exec_eq]
  exact ⟨Exec.cont h1 exc⟩

/-- **The biconditional.**  A gas-exact Blanc-level run of a compiled pc-free
program is *equivalent* to a successful Jaune execution of its code at pc 0.

What this does **not** say, so that nothing downstream overreads it:

* **It is not liveness.**  It converts run witnesses into executions and back;
  it does not produce a run witness for any contract, and nothing in this
  repository says any contract call ever succeeds.  In particular, at every
  external call the witness *contains* the callee's execution as a premise
  (`Xlot.Filled`), so for a contract with an external call every consequence
  stays conditional on callee behaviour.
* **It says nothing about transaction-level execution.**  Both sides live at
  the code-frame level: intrinsic gas, the 63/64 rule and transaction
  validity are a further layer.
* **It is `.ok`-level only.**  Contraposition yields "no successful
  execution", never "the EVM reverts with *this* error" -- the two sides'
  error types differ and no error taxonomy is introduced.

The `pcFree` hypothesis is consumed by the forward direction alone; the
liveness direction holds without it. -/
theorem Prog.runCompiled_iff_exec {sevm : Sevm} {pre : Devm} {p : Prog}
    {post : Devm}
    (h_pcf : Prog.pcFree p = true)
    (h_eq : some sevm.code.toList = p.compile) :
    Prog.RunCompiled sevm pre p post ↔ exec ⟨0, sevm, pre⟩ = .ok post := by
  constructor
  · intro h
    exact Prog.exec_of_runCompiled h h_eq
  · intro h
    obtain ⟨exc⟩ := (exec_iff_exec_eq 0 sevm pre (.ok post)).mpr h
    exact Prog.runCompiled_of_exec sevm pre p post h_pcf exc h_eq

end Blanc
