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

end Blanc
