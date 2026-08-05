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

end Blanc
