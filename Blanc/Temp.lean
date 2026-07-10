import Blanc.Common

/-!
# Temporary plan: compositional execution effects

This file is deliberately a scaffold.  It imports only `Blanc.Common`, and every
theorem below is stated with `sorry`.  Proving the scaffold has two intended
payoffs:

1. one reusable relational-effect traversal of the EVM execution hierarchy,
   instantiable with equality, footprints, monotone metrics, bounded changes,
   and other transitive effects; and
2. a complete balance-sum-nonincreasing instance, ending in the theorem needed
   to replace `processMessageCall_sum_le` in `Blanc/Solvent.lean`.

The order is intentional.  Future proof agents should normally work from top to
bottom.  The stars estimate proof difficulty, not importance:

* ★☆☆☆☆: routine unfolding / constructors;
* ★★☆☆☆: short structural induction or arithmetic;
* ★★★☆☆: several semantic cases, but locally contained;
* ★★★★☆: substantial interpreter inversion;
* ★★★★★: central recursive/oracle proof requiring careful bookkeeping.
-/

namespace Temp

/-! ## 1. Generic compositional relations -/

namespace CEffect

abbrev Rel (σ : Type) := σ → σ → Prop

def Refines {σ : Type} (R S : Rel σ) : Prop :=
  ∀ ⦃s t⦄, R s t → S s t

def Comp {σ : Type} (R S : Rel σ) : Rel σ :=
  fun s u => ∃ t, R s t ∧ S t u

def Holds {σ : Type} (run effect : Rel σ) : Prop :=
  Refines run effect

def ObsEq {σ α : Type} (obs : σ → α) : Rel σ :=
  fun s t => obs s = obs t

def Stable {σ α : Type} (obs : σ → α) (effect : Rel σ) : Prop :=
  Refines effect (ObsEq obs)

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: unfold `Comp`; reassociate the two existential witnesses.
Given `s --R--> a --S--> b --T--> u`, use `b` for the outer witness on the
right and `a` for the inner witness.  Prove the converse identically.
-/
lemma comp_assoc {σ : Type} (R S T : Rel σ) :
    Comp (Comp R S) T = Comp R (Comp S T) := by
  ext s u
  constructor
  · rintro ⟨b, ⟨a, hRa, hSab⟩, hTbu⟩
    exact ⟨a, hRa, b, hSab, hTbu⟩
  · rintro ⟨a, hRa, b, hSab, hTbu⟩
    exact ⟨b, ⟨a, hRa, hSab⟩, hTbu⟩

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: unfold `Holds`, `Refines`, and `Comp`.  Extract the intermediate
state from the run composition, apply `hR` to the first run and `hS` to the
second, then reuse the same intermediate state for the effect composition.
-/
lemma holds_comp {σ : Type} {run₁ run₂ R S : Rel σ}
    (hR : Holds run₁ R) (hS : Holds run₂ S) :
    Holds (Comp run₁ run₂) (Comp R S) := by
  rintro s t ⟨u, h1, h2⟩
  exact ⟨u, hR h1, hS h2⟩

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: this is implication composition.  Unfold `Holds` and
`Refines`; apply `hweak` to the result of `h`.
-/
lemma holds_weaken {σ : Type} {run R S : Rel σ}
    (h : Holds run R) (hweak : Refines R S) : Holds run S := by
  intro s t hrun
  exact hweak (h hrun)

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: use `holds_comp`, then unfold `Refines`/`Comp` and apply
`htrans` to the two effect facts around the intermediate state.
-/
lemma holds_comp_of_transitive {σ : Type} {run₁ run₂ R : Rel σ}
    (htrans : Transitive R)
    (h₁ : Holds run₁ R) (h₂ : Holds run₂ R) :
    Holds (Comp run₁ run₂) R := by
  intro s u hrun
  rcases hrun with ⟨t, hR1, hR2⟩
  exact htrans (h₁ hR1) (h₂ hR2)

/-
(1) Difficulty: ★★☆☆☆
(2) Proof sketch: induct on `Relation.ReflTransGen step s t`.  The reflexive
case is `Relation.ReflTransGen.refl`; in the tail case, map the new `step` edge
through `hrefine` and append it with the constructor corresponding to one more
transitive-closure step.  Inspect the constructors with LSP before writing the
induction, because their argument order is easy to reverse.
-/
lemma reflTransGen_mono {σ : Type} {step effect : Rel σ} {s t : σ}
    (hrefine : Refines step effect)
    (h : Relation.ReflTransGen step s t) :
    Relation.ReflTransGen effect s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h1 h2 ih => exact Relation.ReflTransGen.tail ih (hrefine h2)

/-
(1) Difficulty: ★★☆☆☆
(2) Proof sketch: induct on the closure proof.  The reflexive case uses `hrefl`;
the step case combines the induction hypothesis with `hrefine` applied to the
last edge, using `htrans`.  This is the generic “every small step has `R`, hence
the whole run has `R`” theorem.
-/
lemma reflTransGen_collapse {σ : Type} {step R : Rel σ} {s t : σ}
    (hrefl : Reflexive R) (htrans : Transitive R)
    (hrefine : Refines step R)
    (h : Relation.ReflTransGen step s t) : R s t := by
  induction h with
  | refl => exact hrefl _
  | tail h_prev h_step ih => exact htrans ih (hrefine h_step)

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: unfold `ObsEq`; both results are ordinary equality facts.
Use `rfl` for reflexivity and `Eq.trans` for transitivity.
-/
lemma obsEq_refl_trans {σ α : Type} (obs : σ → α) :
    Reflexive (ObsEq obs) ∧ Transitive (ObsEq obs) := by
  constructor
  · intro x
    rfl
  · intro x y z hxy hyz
    exact Eq.trans hxy hyz

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: unfold `Stable`, `Refines`, and `ObsEq`.  Given an `R`-step,
first obtain equality of `obs`; apply congruence with `f`.
-/
lemma Stable.comp {σ α β : Type} {obs : σ → α} {R : Rel σ}
    (h : Stable obs R) (f : α → β) : Stable (f ∘ obs) R := by
  intro s t hR; exact congrArg f (h hR)

end CEffect

/-! ## 2. Composing the fieldwise `Devm.Rels` already present in Semantics -/

def Devm.Rels.comp (r s : Devm.Rels) : Devm.Rels :=
  {
    stack := CEffect.Comp r.stack s.stack
    memory := CEffect.Comp r.memory s.memory
    gasLeft := CEffect.Comp r.gasLeft s.gasLeft
    logs := CEffect.Comp r.logs s.logs
    refundCounter := CEffect.Comp r.refundCounter s.refundCounter
    output := CEffect.Comp r.output s.output
    accountsToDelete := CEffect.Comp r.accountsToDelete s.accountsToDelete
    returnData := CEffect.Comp r.returnData s.returnData
    error := CEffect.Comp r.error s.error
    accessedAddresses := CEffect.Comp r.accessedAddresses s.accessedAddresses
    accessedStorageKeys := CEffect.Comp r.accessedStorageKeys s.accessedStorageKeys
    state := CEffect.Comp r.state s.state
    createdAccounts := CEffect.Comp r.createdAccounts s.createdAccounts
    transientStorage := CEffect.Comp r.transientStorage s.transientStorage
  }

def Devm.Rels.Refl (r : Devm.Rels) : Prop :=
  Reflexive r.stack ∧ Reflexive r.memory ∧ Reflexive r.gasLeft ∧
  Reflexive r.logs ∧ Reflexive r.refundCounter ∧ Reflexive r.output ∧
  Reflexive r.accountsToDelete ∧ Reflexive r.returnData ∧ Reflexive r.error ∧
  Reflexive r.accessedAddresses ∧ Reflexive r.accessedStorageKeys ∧
  Reflexive r.state ∧ Reflexive r.createdAccounts ∧
  Reflexive r.transientStorage

def Devm.Rels.Trans (r : Devm.Rels) : Prop :=
  Transitive r.stack ∧ Transitive r.memory ∧ Transitive r.gasLeft ∧
  Transitive r.logs ∧ Transitive r.refundCounter ∧ Transitive r.output ∧
  Transitive r.accountsToDelete ∧ Transitive r.returnData ∧ Transitive r.error ∧
  Transitive r.accessedAddresses ∧ Transitive r.accessedStorageKeys ∧
  Transitive r.state ∧ Transitive r.createdAccounts ∧
  Transitive r.transientStorage

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: construct `Devm.Rel (r.comp s) a c`.  For each record field,
use the corresponding field of the intermediate `b` as the existential witness,
then pair the matching fields of `hab` and `hbc`.  There are fourteen repetitive
goals; solve explicitly first, then consider a small constructor tactic.
-/
lemma Devm.Rel.comp {r s : Devm.Rels} {a b c : Devm}
    (hab : Devm.Rel r a b) (hbc : Devm.Rel s b c) :
    Devm.Rel (Devm.Rels.comp r s) a c := by
  exact {
    stack := ⟨b.stack, hab.stack, hbc.stack⟩
    memory := ⟨b.memory, hab.memory, hbc.memory⟩
    gasLeft := ⟨b.gasLeft, hab.gasLeft, hbc.gasLeft⟩
    logs := ⟨b.logs, hab.logs, hbc.logs⟩
    refundCounter := ⟨b.refundCounter, hab.refundCounter, hbc.refundCounter⟩
    output := ⟨b.output, hab.output, hbc.output⟩
    accountsToDelete := ⟨b.accountsToDelete, hab.accountsToDelete, hbc.accountsToDelete⟩
    returnData := ⟨b.returnData, hab.returnData, hbc.returnData⟩
    error := ⟨b.error, hab.error, hbc.error⟩
    accessedAddresses := ⟨b.accessedAddresses, hab.accessedAddresses, hbc.accessedAddresses⟩
    accessedStorageKeys := ⟨b.accessedStorageKeys, hab.accessedStorageKeys, hbc.accessedStorageKeys⟩
    state := ⟨b.state, hab.state, hbc.state⟩
    createdAccounts := ⟨b.createdAccounts, hab.createdAccounts, hbc.createdAccounts⟩
    transientStorage := ⟨b.transientStorage, hab.transientStorage, hbc.transientStorage⟩
  }

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: unpack `hr` into its fourteen reflexivity hypotheses and
construct `Devm.Rel r d d`, applying each hypothesis to the corresponding
projection of `d`.
-/
lemma Devm.rel_refl {r : Devm.Rels} (hr : Devm.Rels.Refl r) :
    Reflexive (Devm.Rel r) := by
  intro d
  rcases hr with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  constructor
  · exact h1 _
  · exact h2 _
  · exact h3 _
  · exact h4 _
  · exact h5 _
  · exact h6 _
  · exact h7 _
  · exact h8 _
  · exact h9 _
  · exact h10 _
  · exact h11 _
  · exact h12 _
  · exact h13 _
  · exact h14 _

/-
(1) Difficulty: ★★☆☆☆
(2) Proof sketch: unpack `hr`, then construct the output relation field by
field.  Each field is the corresponding transitivity hypothesis applied to the
matching fields of `hab` and `hbc`.  This is intentionally generic and should
be the only fourteen-field transitivity proof needed by clients.
-/
lemma Devm.rel_trans {r : Devm.Rels} (hr : Devm.Rels.Trans r) :
    Transitive (Devm.Rel r) := by
  intro a b c hab hbc
  constructor
  · exact hr.1 hab.stack hbc.stack
  · exact hr.2.1 hab.memory hbc.memory
  · exact hr.2.2.1 hab.gasLeft hbc.gasLeft
  · exact hr.2.2.2.1 hab.logs hbc.logs
  · exact hr.2.2.2.2.1 hab.refundCounter hbc.refundCounter
  · exact hr.2.2.2.2.2.1 hab.output hbc.output
  · exact hr.2.2.2.2.2.2.1 hab.accountsToDelete hbc.accountsToDelete
  · exact hr.2.2.2.2.2.2.2.1 hab.returnData hbc.returnData
  · exact hr.2.2.2.2.2.2.2.2.1 hab.error hbc.error
  · exact hr.2.2.2.2.2.2.2.2.2.1 hab.accessedAddresses hbc.accessedAddresses
  · exact hr.2.2.2.2.2.2.2.2.2.2.1 hab.accessedStorageKeys hbc.accessedStorageKeys
  · exact hr.2.2.2.2.2.2.2.2.2.2.2.1 hab.state hbc.state
  · exact hr.2.2.2.2.2.2.2.2.2.2.2.2.1 hab.createdAccounts hbc.createdAccounts
  · exact hr.2.2.2.2.2.2.2.2.2.2.2.2.2 hab.transientStorage hbc.transientStorage

def Devm.OnlyGas : Devm → Devm → Prop :=
  Devm.Rel { Devm.Rels.eq with gasLeft := fun _ _ => True }

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: unfold `CEffect.Stable`, `CEffect.Refines`, `CEffect.ObsEq`,
and `Devm.OnlyGas`.  The `state` field of the supplied `Devm.Rel` proof is
literally an equality, so return it.  `CEffect.Stable.comp` then gives stability
of every observation factoring through `Devm.state` without one lemma per
observation; this is the concrete footprint example requested by the review.
-/
lemma Devm.onlyGas_stable_state :
    CEffect.Stable Devm.state Devm.OnlyGas := by
  intro x y h
  exact h.state

/-! ## 3. Outcome-aware effects for the EVM semantic layers -/

namespace Outcome

def Rel {σ ε α : Type}
    (errState : ε → σ) (okState : α → σ)
    (R : σ → σ → Prop) (pre : σ) : Except ε α → Prop
  | .error err => R pre (errState err)
  | .ok value => R pre (okState value)

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: cases on `out`; in each branch unfold `Rel` and apply
`hrefine` to `h`.  This is the generic weakening rule for both success and
error outcomes, replacing duplicated `_eq`, `_err`, and `_gen` lemmas.
-/
lemma Rel.mono {σ ε α : Type}
    {errState : ε → σ} {okState : α → σ} {R S : σ → σ → Prop}
    {pre : σ} {out : Except ε α}
    (hrefine : CEffect.Refines R S)
    (h : Rel errState okState R pre out) :
    Rel errState okState S pre out := by
  cases out <;> exact hrefine h

end Outcome

def Execution.Rel (R : Devm → Devm → Prop) (pre : Devm) (out : Execution) : Prop :=
  Outcome.Rel Prod.snd id R pre out

def Xlot.Rel (R : Devm → Devm → Prop) : Xlot → Prop
  | .none => True
  | .some ⟨_, pre, out⟩ => Execution.Rel R pre out

def Rinst.Effect (R : Devm → Devm → Prop) (r : Rinst) : Prop :=
  ∀ {pc sevm pre out},
    Rinst.run ⟨pc, sevm, pre⟩ r = out → Execution.Rel R pre out

def Jinst.Effect (R : Devm → Devm → Prop) (j : Jinst) : Prop :=
  ∀ {evm out},
    Jinst.Run evm j out →
      Outcome.Rel Prod.snd Prod.snd R evm.dyna out

def Linst.Effect (R : Devm → Devm → Prop) (l : Linst) : Prop :=
  ∀ {sevm pre out},
    Linst.Run sevm pre l out → Execution.Rel R pre out

def Xinst.EffectGen (R : Devm → Devm → Prop) (x : Xinst) : Prop :=
  ∀ {sevm pre xl out},
    Xlot.Rel R xl → Xinst.Run sevm pre x xl out → Execution.Rel R pre out

def Ninst.EffectGen (R : Devm → Devm → Prop) (n : Ninst) : Prop :=
  ∀ {pc sevm pre xl out},
    Xlot.Rel R xl → Ninst.Run' pc sevm pre n xl out → Execution.Rel R pre out

def Ninst.Effect (R : Devm → Devm → Prop) (n : Ninst) : Prop :=
  ∀ {sevm pre post}, Ninst.Run sevm pre n post → R pre post

def Func.Effect (R : Devm → Devm → Prop) (p : Func) : Prop :=
  ∀ {fs sevm pre post}, Func.Run fs sevm pre p post → R pre post

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: unfold `Ninst.EffectGen` and `Ninst.Run'`.  The only possible
oracle for `.reg r` is `.none`; the `.some` branch is `False`.  In the `.none`
branch, apply `hr` to the defining equality for `Rinst.run`.
-/
lemma Ninst.effectGen_reg {R : Devm → Devm → Prop} {r : Rinst}
    (hr : Rinst.Effect R r) : Ninst.EffectGen R (.reg r) := by
  intro pc sevm pre xl out hxl hrun
  cases xl with
  | none => exact hr hrun
  | some val => exact False.elim hrun

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: unfold `Ninst.EffectGen` and `Ninst.Run'`.  The `.exec x`
definition is exactly `Xinst.Run`, so this should close with `hx hxl hrun` after
minor simplification.
-/
lemma Ninst.effectGen_exec {R : Devm → Devm → Prop} {x : Xinst}
    (hx : Xinst.EffectGen R x) : Ninst.EffectGen R (.exec x) := by
  intro pc sevm pre xl out hxl hrun
  exact hx hxl hrun

/-
(1) Difficulty: ★★★★★
(2) Proof sketch: perform `Exec.rec` on `run`, exactly once for arbitrary `R`.
Invalid-opcode uses `hrefl`.  Error constructors use the matching instruction
effect directly.  Recursive constructors first obtain the instruction effect,
then compose it with the induction hypothesis using `htrans`.  For
`nextSomeErr`/`nextSomeRec`, build `Xlot.Rel R (.some ...)` from the induction
hypothesis for the nested execution before applying `hn`.  Jump and last cases
use `hj`/`hl`.  This theorem is the central payoff: future properties must not
repeat an `Exec.rec` traversal.
-/
theorem Exec.effect {R : Devm → Devm → Prop}
    (hrefl : Reflexive R) (htrans : Transitive R)
    (hn : ∀ n, Ninst.EffectGen R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : Execution.Rel R pre out := by
  have hcomp : ∀ {a b : Devm} {o : Execution},
      R a b → Execution.Rel R b o → Execution.Rel R a o := by
    intro a b o hab hbo
    cases o <;> exact htrans hab hbo
  induction run with
  | invOp h => exact hrefl _
  | nextNoneErr hAt hRun =>
    exact hn _ (xl := .none) (by trivial) hRun
  | nextSomeErr hAt hRun hExec ih =>
    exact hn _ (xl := .some ⟨_, _, _⟩) ih hRun
  | nextNoneRec hAt hRun hExec ih =>
    exact hcomp (hn _ (xl := .none) (by trivial) hRun) ih
  | nextSomeRec hAt hRun hExecSub hExec ihSub ih =>
    exact hcomp (hn _ (xl := .some ⟨_, _, _⟩) ihSub hRun) ih
  | jumpErr hAt hRun => exact hj _ hRun
  | jumpRec hAt hRun hExec ih =>
    exact hcomp (hj _ hRun) ih
  | last hAt hRun => exact hl _ hRun

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: cases on `xl`.  `.none` is trivial.  In the filled case,
unpack `Nonempty (Exec 0 sevm pre out)` and apply `Exec.effect` with the supplied
local effect tables.  This packages the oracle side condition used by public
`Ninst.Run` proofs.
-/
lemma Xlot.rel_of_filled {R : Devm → Devm → Prop}
    (hrefl : Reflexive R) (htrans : Transitive R)
    (hn : ∀ n, Ninst.EffectGen R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {xl : Xlot} (hfilled : xl.Filled) : Xlot.Rel R xl := by
  cases xl with
  | none => trivial
  | some tuple =>
    rcases tuple with ⟨sevm, pre, out⟩
    rcases hfilled with ⟨hrun⟩
    exact Exec.effect hrefl htrans hn hj hl hrun

/-
(1) Difficulty: ★★☆☆☆
(2) Proof sketch: unpack `Ninst.Run` into `xl`, `hfilled`, `pc`, and `hrun`.
Use `Xlot.rel_of_filled` to discharge the oracle contract, apply `hn n`, and
simplify `Execution.Rel` for the final `.ok post` result.
-/
lemma Ninst.effect_of_effectGen {R : Devm → Devm → Prop}
    (hrefl : Reflexive R) (htrans : Transitive R)
    (hn : ∀ n, Ninst.EffectGen R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l) :
    ∀ n, Ninst.Effect R n := by
  intro n sevm pre post hrun
  rcases hrun with ⟨xl, hfilled, pc, hrun'⟩
  have hrel := Xlot.rel_of_filled hrefl htrans hn hj hl hfilled
  exact hn n hrel hrun'

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: induct on the supplied `Func.Run` derivation, not on `p`.
Branch cases compose `hpop`, optionally `hburn`, and the branch induction
hypothesis.  `last` uses `hl` and simplifies the `.ok` outcome.  `next` composes
`hn` with the continuation IH.  `call` composes `hburn` with its IH.  All
composition is `htrans`; no observable-specific reasoning should occur here.
-/
theorem Func.effect {R : Devm → Devm → Prop}
    (htrans : Transitive R)
    (hpop : ∀ xs pre post, Devm.PopBurn xs pre post → R pre post)
    (hburn : ∀ pre post, Devm.Burn pre post → R pre post)
    (hn : ∀ n, Ninst.Effect R n)
    (hl : ∀ l, Linst.Effect R l)
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {p : Func}
    (run : Func.Run fs sevm pre p post) : R pre post := by
  induction run with
  | zero pop run' ih =>
    exact htrans (hpop _ _ _ pop) ih
  | succ neq pop burn run' ih =>
    exact htrans (hpop _ _ _ pop) (htrans (hburn _ _ burn) ih)
  | last run' =>
    exact hl _ run'
  | next runi run' ih =>
    exact htrans (hn _ runi) ih
  | call eq burn run' ih =>
    exact htrans (hburn _ _ burn) ih

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: unfold `Ninst.Effect`, `CEffect.ObsEq`, and `Ninst.Inv`; the
two propositions are definitionally the same after reordering implicit
arguments.  Prove both directions by applying the supplied function.
-/
lemma Ninst.effect_obsEq_iff_inv {α : Type} (obs : Devm → α) (n : Ninst) :
    Ninst.Effect (CEffect.ObsEq obs) n ↔ Ninst.Inv obs n := by
  unfold Ninst.Effect CEffect.ObsEq Ninst.Inv
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: as above, unfold `Func.Effect`, `CEffect.ObsEq`, and
`Func.Inv`.  Specializing both observations of `Func.Inv` to `obs` makes the
statements identical.  This bridge is what allows existing program-level frame
proofs to migrate incrementally to the new relational traversal.
-/
lemma Func.effect_obsEq_iff_inv {α : Type} (obs : Devm → α) (p : Func) :
    Func.Effect (CEffect.ObsEq obs) p ↔ Func.Inv obs obs p := by
  exact Iff.rfl

/-! ## 4. Balance-sum relations and primitive state updates -/

def State.balSum (st : _root_.State) : Nat :=
  sum st.bal

def Devm.balSum (d : Devm) : Nat :=
  State.balSum d.state

def State.BalNoninc (pre post : _root_.State) : Prop :=
  State.balSum post ≤ State.balSum pre

def Devm.BalNoninc (pre post : Devm) : Prop :=
  Devm.balSum post ≤ Devm.balSum pre

def State.BalGrowth (allowance : Nat) (pre post : _root_.State) : Prop :=
  State.balSum post ≤ State.balSum pre + allowance

def State.SumNof (st : _root_.State) : Prop :=
  State.balSum st < 2 ^ 256

def Devm.SumNof (d : Devm) : Prop :=
  Devm.balSum d < 2 ^ 256

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: unfold the two relations.  Reflexivity is `Nat.le_refl` and
transitivity follows from `Nat.le_trans`, remembering that the inequalities are
oriented `post ≤ pre`.
-/
lemma balNoninc_refl_trans :
    (Reflexive State.BalNoninc ∧ Transitive State.BalNoninc) ∧
    (Reflexive Devm.BalNoninc ∧ Transitive Devm.BalNoninc) := by
  exact ⟨⟨fun _ => Nat.le_refl _, fun _ _ _ h1 h2 => Nat.le_trans h2 h1⟩,
         ⟨fun _ => Nat.le_refl _, fun _ _ _ h1 h2 => Nat.le_trans h2 h1⟩⟩

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: unfold `State.SumNof` and `State.BalNoninc`; combine
`post.balSum ≤ pre.balSum` with `pre.balSum < 2^256` using transitivity of `<`
over `≤` (`omega` also closes it).  The Devm version later follows identically.
-/
lemma State.SumNof.of_noninc {pre post : _root_.State}
    (hrel : State.BalNoninc pre post) (hnof : State.SumNof pre) :
    State.SumNof post :=
  Nat.lt_of_le_of_lt hrel hnof

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: unfold `State.balSum`, `State.setBal`, `State.bal`, and `sum`.
Prove the corresponding `sumBelow` replacement identity by induction on the
bound.  At each successor, split on whether the enumerated address equals `a`,
using `State.get_set_self`/`State.get_set_ne`; exactly one summand changes.  This
is the fundamental finite-map update theorem and should replace repeated ad-hoc
sum calculations elsewhere.
-/
lemma adr_toNat_lt_size_local (a : Adr) : a.toNat < 2 ^ 160 := by
  rw [← toAdr_toNat a, Nat.toNat_toAdr, Nat.lo]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

lemma sumBelow_setBal_eq_local (st : _root_.State) (a : Adr) (v : B256)
    (n : Nat) (hn : n ≤ a.toNat) (hsize : n ≤ 2 ^ 160) :
    sumBelow (fun x => (st.setBal a v).bal x) n =
      sumBelow (fun x => st.bal x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    rw [ih (Nat.le_of_succ_le hn) (Nat.le_of_succ_le hsize)]
    have hnlt : n < a.toNat := Nat.lt_of_succ_le hn
    have hnsize : n < 2 ^ 160 := Nat.lt_of_succ_le hsize
    have hne : n.toAdr ≠ a := by
      intro heq
      have hnat := congrArg Adr.toNat heq
      rw [Nat.toNat_toAdr, Nat.lo_eq_of_lt hnsize] at hnat
      omega
    have hget : (st.setBal a v).get n.toAdr = st.get n.toAdr :=
      State.get_set_ne hne.symm
    have hbal : (st.setBal a v).bal n.toAdr = st.bal n.toAdr := by
      dsimp [State.bal, State.setBal]
      have hget' : (st.set a ((st.get a).withBal v)).get n.toAdr =
          st.get n.toAdr := by
        simpa [State.setBal] using hget
      rw [hget']
    rw [hbal]

lemma sumBelow_setBal_add_local (st : _root_.State) (a : Adr) (v : B256)
    (n : Nat) (hsize : n ≤ 2 ^ 160) (ha : a.toNat < n) :
    sumBelow (fun x => (st.setBal a v).bal x) n + (st.bal a).toNat =
      sumBelow (fun x => st.bal x) n + v.toNat := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    have hnsize : n < 2 ^ 160 := Nat.lt_of_succ_le hsize
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha_lt | ha_eq
    · have hih := ih (Nat.le_of_succ_le hsize) ha_lt
      have hne : n.toAdr ≠ a := by
        intro heq
        have hnat := congrArg Adr.toNat heq
        rw [Nat.toNat_toAdr, Nat.lo_eq_of_lt hnsize] at hnat
        omega
      have hget : (st.setBal a v).get n.toAdr = st.get n.toAdr :=
        State.get_set_ne hne.symm
      change sumBelow (fun x => (st.setBal a v).bal x) n +
          ((st.setBal a v).get n.toAdr).bal.toNat + (st.bal a).toNat =
        sumBelow (fun x => st.bal x) n + (st.get n.toAdr).bal.toNat + v.toNat
      rw [hget]
      omega
    · have hprefix := sumBelow_setBal_eq_local st a v n
        (Nat.le_of_eq ha_eq.symm) (Nat.le_of_succ_le hsize)
      have haddr : n.toAdr = a := by
        rw [← ha_eq]
        exact toAdr_toNat a
      rw [hprefix, haddr]
      change sumBelow (fun x => st.bal x) n +
          ((st.setBal a v).get a).bal.toNat + (st.bal a).toNat =
        sumBelow (fun x => st.bal x) n + (st.get a).bal.toNat + v.toNat
      dsimp [State.setBal]
      rw [State.get_set_self]
      change sumBelow (fun x => st.bal x) n + v.toNat +
          (st.get a).bal.toNat =
        sumBelow (fun x => st.bal x) n + (st.get a).bal.toNat + v.toNat
      omega


lemma State.balSum_setBal (st : _root_.State) (a : Adr) (v : B256) :
    State.balSum (st.setBal a v) + (st.bal a).toNat =
      State.balSum st + v.toNat := by
  have hmax : Adr.max.toNat.succ = 2 ^ 160 := by native_decide
  have ha : a.toNat < Adr.max.toNat.succ := by
    rw [hmax]
    exact adr_toNat_lt_size_local a
  simpa [State.balSum, sum] using
    (sumBelow_setBal_add_local st a v Adr.max.toNat.succ
      (by rw [hmax]) ha)

/-
(1) Difficulty: ★★☆☆☆
(2) Proof sketch: unfold `State.subBal` at `h`; the successful branch provides
`v ≤ st.bal a`.  Substitute `mid = st.setBal a (st.bal a - v)`, apply
`State.balSum_setBal`, and use the existing B256 `toNat` subtraction lemma plus
ordinary Nat arithmetic.  Search locally for the exact B256 lemma name before
writing the arithmetic step.
-/
lemma State.balSum_subBal {st mid : _root_.State} {a : Adr} {v : B256}
    (h : st.subBal a v = some mid) :
    State.balSum mid + v.toNat = State.balSum st := by
  unfold State.subBal at h
  split at h
  · contradiction
  · injection h with h_mid
    subst h_mid
    have h_set := State.balSum_setBal st a (st.bal a - v)
    rename_i h_not_lt
    have h_le : v ≤ st.bal a := le_of_not_gt h_not_lt
    have h_le2 : v.toNat ≤ (st.bal a).toNat := B256.toNat_le_toNat h_le
    rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_set
    omega

/-
(1) Difficulty: ★★☆☆☆
(2) Proof sketch: unfold `State.addBal`, rewrite with `State.balSum_setBal`, and
use the modular-addition bound `(x + v).toNat ≤ x.toNat + v.toNat`.  The proof
must not assume non-overflow: wrapping is precisely why the conclusion is `≤`.
Verify the exact B256 lemma name with `lean_local_search`.
-/
lemma State.addBal_growth (st : _root_.State) (a : Adr) (v : B256) :
    State.BalGrowth v.toNat st (st.addBal a v) := by
  unfold State.addBal State.BalGrowth
  have h := State.balSum_setBal st a (st.bal a + v)
  rw [B256.toNat_add] at h
  unfold Nat.lo at h
  have h_mod := Nat.mod_le ((st.bal a).toNat + v.toNat) (2^256)
  omega

/-
(1) Difficulty: ★★☆☆☆
(2) Proof sketch: combine `State.balSum_subBal hsub` with
`State.addBal_growth mid to v`.  The latter bounds the final sum by
`mid.balSum + v.toNat`, which the former rewrites to `st.balSum`.  This lemma is
the reusable conservation/nonincrease theorem for value transfer, including
the recipient-overflow case.
-/
lemma State.sub_addBal_noninc {st mid : _root_.State}
    {src dst : Adr} {v : B256}
    (hsub : st.subBal src v = some mid) :
    State.BalNoninc st (mid.addBal dst v) := by
  dsimp [State.BalNoninc]
  have h1 := State.addBal_growth mid dst v
  dsimp [State.BalGrowth] at h1
  have h2 := State.balSum_subBal hsub
  omega

lemma State.setBal_zero_noninc (st : _root_.State) (a : Adr) :
    State.BalNoninc st (st.setBal a 0) := by
  unfold State.BalNoninc
  have h := State.balSum_setBal st a 0
  have hz : ((0 : B256).toNat) = 0 := by native_decide
  rw [hz, Nat.add_zero] at h
  omega

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: both definitions reduce to the same inequality on
`state.balSum`; use the hypothesis directly.  This is the bridge between state
update lemmas and the interpreter's `Devm` relation.
-/
lemma Devm.balNoninc_of_state {pre post : Devm}
    (h : State.BalNoninc pre.state post.state) : Devm.BalNoninc pre post := by
  exact h

lemma Devm.balNoninc_of_getBal_eq {pre post : Devm}
    (h : post.getBal = pre.getBal) : Devm.BalNoninc pre post := by
  unfold Devm.BalNoninc Devm.balSum State.balSum
  change sum post.getBal ≤ sum pre.getBal
  rw [h]

/-! ## 5. Balance effects of instruction and message semantic units -/

def MessageExecution := Except (String × _root_.State × AdrSet × Tra) Devm

def MessageExecution.state : MessageExecution → _root_.State
  | .ok d => d.state
  | .error ⟨_, st, _, _⟩ => st

def MessageExecution.Rel
    (R : _root_.State → _root_.State → Prop)
    (pre : _root_.State) (out : MessageExecution) : Prop :=
  R pre out.state

def BenvExecution.state : Except (String × _root_.State × AdrSet × Tra) Benv →
    _root_.State
  | .ok benv => benv.state
  | .error ⟨_, st, _, _⟩ => st

/-! Error-side `getBal` frame lemmas, mirroring the generated `*_getCode_err`
family in `Blanc/Common.lean`: every regular-instruction error path leaves
balances unchanged. -/

lemma Devm.pop_map_snd_getBal_eq {devm devm1 : Devm} (hp : (devm.pop <&> Prod.snd) = .ok devm1) (a : Adr) : devm1.getBal a = devm.getBal a := by
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hp
  rcases hp2 : devm.pop with _ | ⟨x, devm2⟩
  · simp [hp2] at hp
  · simp [hp2] at hp
    rcases hp with ⟨_, rfl⟩
    exact Devm.pop_getBal_eq hp2 a

lemma Devm.pop_map_snd_getBal_err {devm : Devm} {err : String × Devm} (hp : (devm.pop <&> Prod.snd) = .error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hp
  rcases hp2 : devm.pop with e | ⟨x, devm2⟩
  · simp [hp2] at hp; cases hp
    simp only [Devm.pop] at hp2
    split at hp2 <;> try contradiction
    cases hp2; rfl
  · simp [hp2] at hp

lemma Devm.pop_getBal_err {err devm} (h : Devm.pop devm = .error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  simp only [Devm.pop] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeGas_getBal_err {cost devm err} (h : chargeGas cost devm = .error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  simp only [chargeGas] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_getBal_err {v devm err} (h : Devm.push v devm = Except.error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  unfold Devm.push Except.assert at h; dsimp [Bind.bind, Except.bind] at h
  split_ifs at h; try contradiction
  injection h with h1; rw [← h1]

lemma assert_getBal_err {cond : Prop} [Decidable cond] {msg : String} {devm : Devm} {err : String × Devm} (h : Except.assert cond (msg, devm) = Except.error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  unfold Except.assert at h
  split_ifs at h; try contradiction
  injection h with h1; rw [← h1]

lemma Devm.popToNat_getBal_err {devm err} (h : Devm.popToNat devm = .error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  dsimp [Devm.popToNat, Functor.map, Except.map] at h
  rcases hp : devm.pop with err_pop | ⟨x, devm1⟩
  · simp [hp] at h; cases h; exact Devm.pop_getBal_err hp a
  · simp [hp] at h

lemma Devm.popToAdr_getBal_err {devm err} (h : Devm.popToAdr devm = .error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  dsimp [Devm.popToAdr, Functor.map, Except.map] at h
  rcases hp : devm.pop with err_pop | ⟨x, devm1⟩
  · simp [hp] at h; cases h; exact Devm.pop_getBal_err hp a
  · simp [hp] at h

lemma getBal_err_of_bind {α} {ma : Except (String × Devm) α} {f : α → Execution}
    {devm : Devm} {a : Adr} {err : String × Devm}
    (run : (ma >>= f) = Except.error err)
    (getDevm : α → Devm)
    (h_first_ok : ∀ v, ma = Except.ok v → (getDevm v).getBal a = devm.getBal a)
    (h_first_err : ∀ e, ma = Except.error e → e.2.getBal a = devm.getBal a)
    (h_rest_err : ∀ v, ma = Except.ok v → f v = Except.error err → err.2.getBal a = (getDevm v).getBal a) :
    err.2.getBal a = devm.getBal a := by
  cases h_ma : ma
  case error e =>
    rw [h_ma, Except.bind_error] at run
    injection run with h_eq; subst h_eq
    exact h_first_err _ h_ma
  case ok v =>
    rw [h_ma, Except.bind_ok] at run
    have h1 := h_rest_err v h_ma run
    have h2 := h_first_ok v h_ma
    exact h1.trans h2

lemma Devm.popN_getBal_err {n : Nat} {devm : Devm} {err : String × Devm}
    (hp : devm.popN n = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  induction n generalizing devm err with
  | zero => simp [Devm.popN] at hp
  | succ n ih =>
    simp [Devm.popN, bind, Except.bind] at hp
    split at hp
    · rename_i eq_err; injection hp with eq; subst eq
      exact Devm.pop_getBal_err eq_err a
    · rename_i eq_ok; split at hp
      · rename_i eq_err; injection hp with eq; subst eq
        have h1 := ih eq_err
        have h2 := Devm.pop_getBal_eq eq_ok a
        exact h1.trans h2
      · rename_i eq_ok2; injection hp

lemma pushItem_getBal_err {x c devm err} (h : pushItem x c devm = Except.error err) (a : Adr) : err.2.getBal a = devm.getBal a := by
  simp only [pushItem] at h
  refine getBal_err_of_bind h id ?_ ?_ ?_
  · intro devm1 hc; exact chargeGas_getBal_eq hc a
  · intro e hc; exact chargeGas_getBal_err hc a
  · intro devm1 hc run; exact Devm.push_getBal_err run a

lemma applyUnary_getBal_err {f : B256 → B256} {cost devm err}
    (h : applyUnary f cost devm = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  simp only [applyUnary] at h
  refine getBal_err_of_bind h Prod.snd ?_ ?_ ?_
  · intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a
  · intro e hp; exact Devm.pop_getBal_err hp a
  · intro ⟨x, devm1⟩ hp run; exact pushItem_getBal_err run a

lemma applyBinary_getBal_err {f : B256 → B256 → B256} {cost devm err}
    (h : applyBinary f cost devm = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  simp only [applyBinary] at h
  refine getBal_err_of_bind h Prod.snd ?_ ?_ ?_
  · intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a
  · intro e hp; exact Devm.pop_getBal_err hp a
  · intro ⟨x, devm1⟩ hp run
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getBal_eq hp2 a
    · intro e hp2; exact Devm.pop_getBal_err hp2 a
    · intro ⟨y, devm2⟩ hp2 run2; exact pushItem_getBal_err run2 a

lemma applyTernary_getBal_err {f : B256 → B256 → B256 → B256} {cost devm err}
    (h : applyTernary f cost devm = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  simp only [applyTernary] at h
  refine getBal_err_of_bind h Prod.snd ?_ ?_ ?_
  · intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a
  · intro e hp; exact Devm.pop_getBal_err hp a
  · intro ⟨x, devm1⟩ hp run
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getBal_eq hp2 a
    · intro e hp2; exact Devm.pop_getBal_err hp2 a
    · intro ⟨y, devm2⟩ hp2 run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨z, devm3⟩ hp3; exact Devm.pop_getBal_eq hp3 a
      · intro e hp3; exact Devm.pop_getBal_err hp3 a
      · intro ⟨z, devm3⟩ hp3 run3; exact pushItem_getBal_err run3 a

lemma Rinst.inv_getBal_err
    {pc sevm devm r err}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  cases r <;> dsimp [Rinst.run, Rinst.runCore] at run
  case add => apply applyBinary_getBal_err run
  case mul => apply applyBinary_getBal_err run
  case sub => apply applyBinary_getBal_err run
  case div => apply applyBinary_getBal_err run
  case sdiv => apply applyBinary_getBal_err run
  case mod => apply applyBinary_getBal_err run
  case smod => apply applyBinary_getBal_err run
  case addmod => apply applyTernary_getBal_err run
  case mulmod => apply applyTernary_getBal_err run
  case exp =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a
    · intro e hp; exact Devm.pop_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getBal_eq hp2 a
      · intro e hp2; exact Devm.pop_getBal_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3; exact pushItem_getBal_err run3 a
  case signextend => apply applyBinary_getBal_err run
  case lt => apply applyBinary_getBal_err run
  case gt => apply applyBinary_getBal_err run
  case slt => apply applyBinary_getBal_err run
  case sgt => apply applyBinary_getBal_err run
  case eq => apply applyBinary_getBal_err run
  case iszero => apply applyUnary_getBal_err run
  case and => apply applyBinary_getBal_err run
  case or => apply applyBinary_getBal_err run
  case xor => apply applyBinary_getBal_err run
  case not => apply applyUnary_getBal_err run
  case byte => apply applyBinary_getBal_err run
  case shr => apply applyBinary_getBal_err run
  case shl => apply applyBinary_getBal_err run
  case sar => apply applyBinary_getBal_err run
  case kec =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getBal_eq hp a
    · intro e hp; exact Devm.popToNat_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getBal_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getBal_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getBal_err_of_bind run3 id ?_ ?_ ?_
        · intro devm3 hc; exact chargeGas_getBal_eq hc a
        · intro e hc; exact chargeGas_getBal_err hc a
        · intro devm3 hc run4; exact Devm.push_getBal_err run4 a
  case address => apply pushItem_getBal_err run
  case balance =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a
    · intro e hp; exact Devm.pop_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2; split at run2
      · refine getBal_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getBal_eq hc a
        · intro e hc; exact chargeGas_getBal_err hc a
        · intro devm2 hc run3; exact Devm.push_getBal_err run3 a
      · refine getBal_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getBal_eq hc a
        · intro e hc; exact chargeGas_getBal_err hc a
        · intro devm2 hc run3; exact Devm.push_getBal_err run3 a
  case origin => apply pushItem_getBal_err run
  case caller => apply pushItem_getBal_err run
  case callvalue => apply pushItem_getBal_err run
  case calldataload =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a
    · intro e hp; exact Devm.pop_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 id ?_ ?_ ?_
      · intro devm2 hc; exact chargeGas_getBal_eq hc a
      · intro e hc; exact chargeGas_getBal_err hc a
      · intro devm2 hc run3; exact Devm.push_getBal_err run3 a
  case calldatasize => apply pushItem_getBal_err run
  case calldatacopy =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getBal_eq hp a
    · intro e hp; exact Devm.popToNat_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getBal_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getBal_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getBal_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_getBal_eq hp3 a
        · intro e hp3; exact Devm.popToNat_getBal_err hp3 a
        · intro ⟨z, devm3⟩ hp3 run4
          refine getBal_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact chargeGas_getBal_eq hc a
          · intro e hc; exact chargeGas_getBal_err hc a
          · intro devm4 hc run5; injection run5
  case codesize => apply pushItem_getBal_err run
  case codecopy =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getBal_eq hp a
    · intro e hp; exact Devm.popToNat_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getBal_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getBal_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getBal_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_getBal_eq hp3 a
        · intro e hp3; exact Devm.popToNat_getBal_err hp3 a
        · intro ⟨z, devm3⟩ hp3 run4
          refine getBal_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact chargeGas_getBal_eq hc a
          · intro e hc; exact chargeGas_getBal_err hc a
          · intro devm4 hc run5; injection run5
  case gasprice => apply pushItem_getBal_err run
  case extcodesize =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_getBal_eq hp a
    · intro e hp; exact Devm.popToAdr_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2; split at run2
      · refine getBal_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getBal_eq hc a
        · intro e hc; exact chargeGas_getBal_err hc a
        · intro devm2 hc run3; exact Devm.push_getBal_err run3 a
      · refine getBal_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getBal_eq hc a
        · intro e hc; exact chargeGas_getBal_err hc a
        · intro devm2 hc run3; exact Devm.push_getBal_err run3 a
  case extcodecopy =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_getBal_eq hp a
    · intro e hp; exact Devm.popToAdr_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getBal_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getBal_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getBal_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_getBal_eq hp3 a
        · intro e hp3; exact Devm.popToNat_getBal_err hp3 a
        · intro ⟨z, devm3⟩ hp3 run4
          refine getBal_err_of_bind run4 Prod.snd ?_ ?_ ?_
          · intro ⟨w, devm4⟩ hp4; exact Devm.popToNat_getBal_eq hp4 a
          · intro e hp4; exact Devm.popToNat_getBal_err hp4 a
          · intro ⟨w, devm4⟩ hp4 run5
            split at run5
            · refine getBal_err_of_bind run5 id ?_ ?_ ?_
              · intro devm5 hc; exact chargeGas_getBal_eq hc a
              · intro e hc; exact chargeGas_getBal_err hc a
              · intro devm5 hc run6; injection run6
            · refine getBal_err_of_bind run5 id ?_ ?_ ?_
              · intro devm5 hc; exact chargeGas_getBal_eq hc a
              · intro e hc; exact chargeGas_getBal_err hc a
              · intro devm5 hc run6; injection run6
  case retdatasize => apply pushItem_getBal_err run
  case retdatacopy =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getBal_eq hp a
    · intro e hp; exact Devm.popToNat_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getBal_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getBal_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getBal_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_getBal_eq hp3 a
        · intro e hp3; exact Devm.popToNat_getBal_err hp3 a
        · intro ⟨z, devm3⟩ hp3 run4
          refine getBal_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact chargeGas_getBal_eq hc a
          · intro e hc; exact chargeGas_getBal_err hc a
          · intro devm4 hc run5
            split_ifs at run5
            all_goals (try { cases run5; rfl })
            all_goals (try contradiction)
  case extcodehash =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToAdr_getBal_eq hp a
    · intro e hp; exact Devm.popToAdr_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2; split at run2
      · refine getBal_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getBal_eq hc a
        · intro e hc; exact chargeGas_getBal_err hc a
        · intro devm2 hc run3; exact Devm.push_getBal_err run3 a
      · refine getBal_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getBal_eq hc a
        · intro e hc; exact chargeGas_getBal_err hc a
        · intro devm2 hc run3; exact Devm.push_getBal_err run3 a
  case blockhash =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a
    · intro e hp; exact Devm.pop_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 id ?_ ?_ ?_
      · intro devm2 hc; exact chargeGas_getBal_eq hc a
      · intro e hc; exact chargeGas_getBal_err hc a
      · intro devm2 hc run3; exact Devm.push_getBal_err run3 a
  case coinbase => apply pushItem_getBal_err run
  case timestamp => apply pushItem_getBal_err run
  case number => apply pushItem_getBal_err run
  case prevrandao => apply pushItem_getBal_err run
  case gaslimit => apply pushItem_getBal_err run
  case chainid => apply pushItem_getBal_err run
  case selfbalance => apply pushItem_getBal_err run
  case basefee => apply pushItem_getBal_err run
  case blobhash =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    exact fun ⟨x, devm1⟩ hp => Devm.pop_getBal_eq hp a
    exact fun e hp => Devm.pop_getBal_err hp a
    intro ⟨x, devm1⟩ hp run2
    refine getBal_err_of_bind run2 id ?_ ?_ ?_
    exact fun devm2 hc => chargeGas_getBal_eq hc a
    exact fun e hc => chargeGas_getBal_err hc a
    intro devm2 hc run3; exact Devm.push_getBal_err run3 a
  case blobbasefee => apply pushItem_getBal_err run
  case pop =>
    refine getBal_err_of_bind run id ?_ ?_ ?_
    exact fun devm1 hc => Devm.pop_map_snd_getBal_eq hc a
    exact fun e hc => Devm.pop_map_snd_getBal_err hc a
    intro devm1 hc run2; exact chargeGas_getBal_err run2 a
  case mload =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    exact fun ⟨x, devm1⟩ hp => Devm.popToNat_getBal_eq hp a
    exact fun e hp => Devm.popToNat_getBal_err hp a
    intro ⟨x, devm1⟩ hp run2
    refine getBal_err_of_bind run2 id ?_ ?_ ?_
    exact fun devm2 hc => chargeGas_getBal_eq hc a
    exact fun e hc => chargeGas_getBal_err hc a
    intro devm2 hc run3; exact Devm.push_getBal_err run3 a
  case mstore =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getBal_eq hp a
    · intro e hp; exact Devm.popToNat_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getBal_eq hp2 a
      · intro e hp2; exact Devm.pop_getBal_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getBal_err_of_bind run3 id ?_ ?_ ?_
        · intro devm3 hc; exact chargeGas_getBal_eq hc a
        · intro e hc; exact chargeGas_getBal_err hc a
        · intro devm3 hc run4; cases run4
  case mstore8 =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getBal_eq hp a
    · intro e hp; exact Devm.popToNat_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getBal_eq hp2 a
      · intro e hp2; exact Devm.pop_getBal_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getBal_err_of_bind run3 id ?_ ?_ ?_
        · intro devm3 hc; exact chargeGas_getBal_eq hc a
        · intro e hc; exact chargeGas_getBal_err hc a
        · intro devm3 hc run4; injection run4
  case sload =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a
    · intro e hp; exact Devm.pop_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2; split at run2
      · refine getBal_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getBal_eq hc a
        · intro e hc; exact chargeGas_getBal_err hc a
        · intro devm2 hc run3; exact Devm.push_getBal_err run3 a
      · refine getBal_err_of_bind run2 id ?_ ?_ ?_
        · intro devm2 hc; exact chargeGas_getBal_eq hc a
        · intro e hc; exact chargeGas_getBal_err hc a
        · intro devm2 hc run3; exact Devm.push_getBal_err run3 a
  case sstore =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a
    · intro e hp; exact Devm.pop_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getBal_eq hp2 a
      · intro e hp2; exact Devm.pop_getBal_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getBal_err_of_bind run3 (fun _ => devm2) ?_ ?_ ?_
        · intro u h_assert; rfl
        · intro e h_assert; exact assert_getBal_err h_assert a
        · intro u h_assert run4
          split_ifs at run4
          all_goals {
            refine getBal_err_of_bind run4 id ?_ ?_ ?_
            · intro devm3 hc; exact chargeGas_getBal_eq hc a
            · intro e hc; exact chargeGas_getBal_err hc a
            · intro devm3 hc run5
              dsimp [assertDynamic, Except.assert] at run5
              split_ifs at run5
              all_goals (try { cases run5; rfl })
              all_goals (try injection run5)
          }
  case pc =>
    refine getBal_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact chargeGas_getBal_eq hc a
    · intro e hc; exact chargeGas_getBal_err hc a
    · intro devm1 hc run2; exact Devm.push_getBal_err run2 a
  case msize =>
    refine getBal_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact chargeGas_getBal_eq hc a
    · intro e hc; exact chargeGas_getBal_err hc a
    · intro devm1 hc run2; exact Devm.push_getBal_err run2 a
  case gas =>
    refine getBal_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact chargeGas_getBal_eq hc a
    · intro e hc; exact chargeGas_getBal_err hc a
    · intro devm1 hc run2; exact Devm.push_getBal_err run2 a
  case tload =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a
    · intro e hp; exact Devm.pop_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 id ?_ ?_ ?_
      · intro devm2 hc; exact chargeGas_getBal_eq hc a
      · intro e hc; exact chargeGas_getBal_err hc a
      · intro devm2 hc run3; exact Devm.push_getBal_err run3 a
  case tstore =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.pop_getBal_eq hp a
    · intro e hp; exact Devm.pop_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.pop_getBal_eq hp2 a
      · intro e hp2; exact Devm.pop_getBal_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getBal_err_of_bind run3 id ?_ ?_ ?_
        · intro devm3 hc; exact chargeGas_getBal_eq hc a
        · intro e hc; exact chargeGas_getBal_err hc a
        · intro devm3 hc run4
          dsimp [assertDynamic, Except.assert] at run4
          simp only [bind, Except.bind] at run4
          try split_ifs at run4; simp at run4
          rw [← run4]; rfl
  case mcopy =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getBal_eq hp a
    · intro e hp; exact Devm.popToNat_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getBal_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getBal_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getBal_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popToNat_getBal_eq hp3 a
        · intro e hp3; exact Devm.popToNat_getBal_err hp3 a
        · intro ⟨z, devm3⟩ hp3 run4
          refine getBal_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact chargeGas_getBal_eq hc a
          · intro e hc; exact chargeGas_getBal_err hc a
          · intro devm4 hc run5; contradiction
  case dup =>
    refine getBal_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact chargeGas_getBal_eq hc a
    · intro e hc; exact chargeGas_getBal_err hc a
    · intro devm1 hc run2
      split at run2
      · injection run2 with h_eq; cases h_eq; rfl
      · exact Devm.push_getBal_err run2 a
  case swap =>
    refine getBal_err_of_bind run id ?_ ?_ ?_
    · intro devm1 hc; exact chargeGas_getBal_eq hc a
    · intro e hc; exact chargeGas_getBal_err hc a
    · intro devm1 hc run2
      split at run2
      · injection run2 with h_eq; cases h_eq; rfl
      · contradiction
  case log =>
    refine getBal_err_of_bind run Prod.snd ?_ ?_ ?_
    · intro ⟨x, devm1⟩ hp; exact Devm.popToNat_getBal_eq hp a
    · intro e hp; exact Devm.popToNat_getBal_err hp a
    · intro ⟨x, devm1⟩ hp run2
      refine getBal_err_of_bind run2 Prod.snd ?_ ?_ ?_
      · intro ⟨y, devm2⟩ hp2; exact Devm.popToNat_getBal_eq hp2 a
      · intro e hp2; exact Devm.popToNat_getBal_err hp2 a
      · intro ⟨y, devm2⟩ hp2 run3
        refine getBal_err_of_bind run3 Prod.snd ?_ ?_ ?_
        · intro ⟨z, devm3⟩ hp3; exact Devm.popN_getBal_eq hp3 a
        · intro e hp3; exact Devm.popN_getBal_err hp3 a
        · intro ⟨z, devm3⟩ hp3 run4
          refine getBal_err_of_bind run4 id ?_ ?_ ?_
          · intro devm4 hc; exact chargeGas_getBal_eq hc a
          · intro e hc; exact chargeGas_getBal_err hc a
          · intro devm4 hc run5
            dsimp [assertDynamic, Except.assert] at run5
            simp only [bind, Except.bind] at run5
            try split_ifs at run5; simp at run5
            rw [← run5]; rfl

/-
(1) Difficulty: ★★★★☆
(2) Proof sketch: cases on `r`.  For successful runs, reuse `Rinst.inv_bal` and
turn equality of `getBal` into equality of `balSum`, hence nonincrease.  For
errors, follow the same bind-decomposition pattern as the existing generated
`*_getBal_err` lemmas: stack, gas, memory, storage, and transient-storage
operations leave balances equal.  Prove this once for the entire `Rinst` family
rather than once per observable.  SSTORE is the only state-writing regular
instruction, but `sstore_inv_getBal` already provides its balance frame fact.
-/
lemma Rinst.balance_effect (r : Rinst) :
    Rinst.Effect Devm.BalNoninc r := by
  intro pc sevm pre out h
  cases out with
  | ok post =>
    exact Devm.balNoninc_of_getBal_eq (Rinst.inv_bal h).symm
  | error err =>
    exact Devm.balNoninc_of_getBal_eq
      (funext (fun a => Rinst.inv_getBal_err h a))

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: cases on `j` and unfold `Jinst.Run`, `Jinst.run`, and
`Jinst.runCore`.  Every successful or failed path changes only stack/gas/pc, so
show equality of the `state` (or `getBal`) of the output Devm and conclude by
reflexivity of `BalNoninc`.  Existing `Devm.pop_of_pop` and
`Devm.burn_of_chargeGas` state fields should eliminate most manual rewriting.
-/
lemma Jinst.balance_effect (j : Jinst) :
    Jinst.Effect Devm.BalNoninc j := by
  cases j
  · intro pre out H; unfold Jinst.Run Jinst.run Jinst.runCore at H; revert H; dsimp; intro H; subst H
    simp only [bind, Except.bind]
    split; rename_i d eq
    · unfold Outcome.Rel
      apply Devm.balNoninc_of_state
      rw [Devm.pop_err_snd eq]
      apply balNoninc_refl_trans.1.1
    · rename_i discr eq
      rcases discr with ⟨jump_dest, devm'⟩
      split; rename_i d' eq'
      · unfold Outcome.Rel
        apply Devm.balNoninc_of_state
        rw [chargeGas_err_snd eq', ←(Devm.pop_of_pop eq).state]
        apply balNoninc_refl_trans.1.1
      · rename_i devm'' eq'
        split; rename_i d'' eq''
        · unfold Outcome.Rel
          apply Devm.balNoninc_of_state
          rw [Except.assert_err_snd eq'', ←(Devm.burn_of_chargeGas eq').state, ←(Devm.pop_of_pop eq).state]
          apply balNoninc_refl_trans.1.1
        · rename_i dest_pc eq''
          unfold Outcome.Rel
          apply Devm.balNoninc_of_state
          rw [←(Devm.burn_of_chargeGas eq').state, ←(Devm.pop_of_pop eq).state]
          apply balNoninc_refl_trans.1.1
  · intro pre out H; unfold Jinst.Run Jinst.run Jinst.runCore at H; revert H; dsimp; intro H; subst H
    simp only [bind, Except.bind]
    split; rename_i d eq
    · unfold Outcome.Rel
      apply Devm.balNoninc_of_state
      rw [Devm.pop_err_snd eq]
      apply balNoninc_refl_trans.1.1
    · rename_i discr eq
      rcases discr with ⟨dest, devm'⟩
      split; rename_i d' eq'
      · unfold Outcome.Rel
        apply Devm.balNoninc_of_state
        rw [Devm.pop_err_snd eq', ←(Devm.pop_of_pop eq).state]
        apply balNoninc_refl_trans.1.1
      · rename_i discr' eq'
        rcases discr' with ⟨cond, devm''⟩
        split; rename_i d'' eq''
        · unfold Outcome.Rel
          apply Devm.balNoninc_of_state
          rw [chargeGas_err_snd eq'', ←(Devm.pop_of_pop eq').state, ←(Devm.pop_of_pop eq).state]
          apply balNoninc_refl_trans.1.1
        · rename_i devm''' eq''
          split; rename_i hcond
          · unfold Outcome.Rel
            apply Devm.balNoninc_of_state
            rw [←(Devm.burn_of_chargeGas eq'').state, ←(Devm.pop_of_pop eq').state, ←(Devm.pop_of_pop eq).state]
            apply balNoninc_refl_trans.1.1
          · split; rename_i d''' eq'''
            · unfold Outcome.Rel
              apply Devm.balNoninc_of_state
              rw [Except.assert_err_snd eq''', ←(Devm.burn_of_chargeGas eq'').state, ←(Devm.pop_of_pop eq').state, ←(Devm.pop_of_pop eq).state]
              apply balNoninc_refl_trans.1.1
            · rename_i dest_pc eq'''
              unfold Outcome.Rel
              apply Devm.balNoninc_of_state
              rw [←(Devm.burn_of_chargeGas eq'').state, ←(Devm.pop_of_pop eq').state, ←(Devm.pop_of_pop eq).state]
              apply balNoninc_refl_trans.1.1
  · intro pre out H; unfold Jinst.Run Jinst.run Jinst.runCore at H; revert H; dsimp; intro H; subst H
    simp only [bind, Except.bind]
    split; rename_i d eq
    · unfold Outcome.Rel
      apply Devm.balNoninc_of_state
      rw [chargeGas_err_snd eq]
      apply balNoninc_refl_trans.1.1
    · rename_i devm' eq
      unfold Outcome.Rel
      apply Devm.balNoninc_of_state
      rw [←(Devm.burn_of_chargeGas eq).state]
      apply balNoninc_refl_trans.1.1

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: unfold `Ninst.EffectGen` and the `.push` branch of
`Ninst.Run'`; `xl` must be `.none`.  Decompose the `chargeGas >>= push` result,
including both errors.  `chargeGas` and `Devm.push` preserve state, hence the
balance sum is equal in every outcome.
-/
lemma Ninst.push_balance_effectGen {xs : B8L} {hxs : xs.length ≤ 32} :
    Ninst.EffectGen Devm.BalNoninc (.push xs hxs) := by
  unfold Ninst.EffectGen Ninst.Run'
  intro pc sevm pre xl out hxl hRun
  cases xl
  · simp only at hRun
    cases hcg : chargeGas (if xs = [] then gBase else gVerylow) pre with
    | error e =>
      simp [hcg] at hRun
      subst hRun
      unfold Execution.Rel Outcome.Rel
      simp only [chargeGas] at hcg
      split at hcg
      · cases hcg; exact balNoninc_refl_trans.2.1 pre
      · contradiction
    | ok devm' =>
      simp [hcg] at hRun
      cases hpush : Devm.push xs.toB256 devm'
      · rw [← hRun, hpush]
        simp only [Execution.Rel, Outcome.Rel]
        simp only [Devm.push, Except.assert, bind, Except.bind] at hpush
        split at hpush <;> try contradiction
        rename_i a x err heq
        cases hpush
        split at heq <;> try contradiction
        have hs : devm' = a.2 := by
          simpa using congrArg (fun e : Except (String × Devm) Unit =>
            match e with | .error (_, d) => d | .ok _ => devm') heq
        apply Devm.balNoninc_of_state
        rw [← hs, ← (Devm.burn_of_chargeGas hcg).state]
        exact balNoninc_refl_trans.1.1 pre.state
      · rw [← hRun, hpush]
        simp only [Execution.Rel, Outcome.Rel]
        apply Devm.balNoninc_of_state
        simp only [id]
        rw [← (Devm.push_of_push hpush).state,
          ← (Devm.burn_of_chargeGas hcg).state]
        exact balNoninc_refl_trans.1.1 pre.state
  · simp only at hRun

/-
(1) Difficulty: ★★★★☆
(2) Proof sketch: cases on `l`.  STOP is reflexive.  RETURN and REVERT only pop,
burn gas, read memory, and set output, so prove state equality for both success
and error outcomes.  SELFDESTRUCT is the real case: invert its pops/charges,
use `State.sub_addBal_noninc` for donor-to-donee transfer, and show that the
optional `setBal donor 0`/account-to-delete update cannot increase the sum.
Handle `donor = donee` explicitly rather than assuming distinct addresses.
-/
lemma Linst.balance_effect (l : Linst) :
    Linst.Effect Devm.BalNoninc l := by
  intro sevm pre out run
  cases l
  case stop =>
    dsimp [Linst.Run, Linst.run] at run
    rw [← run]
    exact balNoninc_refl_trans.2.1 pre
  case ret =>
    dsimp [Linst.Run, Linst.run] at run
    revert run
    dsimp [bind, Except.bind]
    cases h1 : pre.popToNat <;> dsimp
    case error err =>
      intro run
      rw [← run]
      apply Devm.balNoninc_of_getBal_eq
      rw [Devm.popToNat_err_snd h1]
    case ok res1 =>
      have hp1 : res1.2.getBal = pre.getBal := by
        funext a
        exact Devm.popToNat_getBal_eq h1 a
      cases h2 : res1.2.popToNat <;> dsimp
      case error err =>
        intro run
        rw [← run]
        apply Devm.balNoninc_of_getBal_eq
        rw [Devm.popToNat_err_snd h2]
        exact hp1
      case ok res2 =>
        have hp2 : res2.2.getBal = pre.getBal := by
          funext a
          exact (Devm.popToNat_getBal_eq h2 a).trans (congrFun hp1 a)
        cases h3 : chargeGas (res2.2.extCost [(res1.1, res2.1)]) res2.2 <;> dsimp
        case error err =>
          intro run
          rw [← run]
          apply Devm.balNoninc_of_getBal_eq
          rw [chargeGas_err_snd h3]
          exact hp2
        case ok res3 =>
          intro run
          rw [← run]
          apply Devm.balNoninc_of_getBal_eq
          funext a
          have hmem : res3.memRead res1.1 res2.1 =
              ⟨(res3.memRead res1.1 res2.1).1, (res3.memRead res1.1 res2.1).2⟩ := rfl
          exact (memRead_getBal_eq hmem a).trans
            ((chargeGas_getBal_eq h3 a).trans (congrFun hp2 a))
  case rev =>
    dsimp [Linst.Run, Linst.run] at run
    revert run
    dsimp [bind, Except.bind]
    cases h1 : pre.popToNat <;> dsimp
    case error err =>
      intro run
      rw [← run]
      apply Devm.balNoninc_of_getBal_eq
      rw [Devm.popToNat_err_snd h1]
    case ok res1 =>
      have hp1 : res1.2.getBal = pre.getBal := by
        funext a
        exact Devm.popToNat_getBal_eq h1 a
      cases h2 : res1.2.popToNat <;> dsimp
      case error err =>
        intro run
        rw [← run]
        apply Devm.balNoninc_of_getBal_eq
        rw [Devm.popToNat_err_snd h2]
        exact hp1
      case ok res2 =>
        have hp2 : res2.2.getBal = pre.getBal := by
          funext a
          exact (Devm.popToNat_getBal_eq h2 a).trans (congrFun hp1 a)
        cases h3 : chargeGas (res2.2.extCost [(res1.1, res2.1)]) res2.2 <;> dsimp
        case error err =>
          intro run
          rw [← run]
          apply Devm.balNoninc_of_getBal_eq
          rw [chargeGas_err_snd h3]
          exact hp2
        case ok res3 =>
          intro run
          rw [← run]
          apply Devm.balNoninc_of_getBal_eq
          funext a
          have hmem : res3.memRead res1.1 res2.1 =
              ⟨(res3.memRead res1.1 res2.1).1, (res3.memRead res1.1 res2.1).2⟩ := rfl
          exact (memRead_getBal_eq hmem a).trans
            ((chargeGas_getBal_eq h3 a).trans (congrFun hp2 a))
  case dest =>
    dsimp [Linst.Run, Linst.run] at run
    revert run
    dsimp [bind, Except.bind]
    cases h1 : pre.popToAdr <;> dsimp
    case error err =>
      intro run
      rw [← run]
      apply Devm.balNoninc_of_getBal_eq
      rw [Devm.popToAdr_err_snd h1]
    case ok res1 =>
      have hpop : res1.2.getBal = pre.getBal := by
        funext a
        exact Devm.popToAdr_getBal_eq h1 a
      have hacc :
          (if res1.1 ∉ res1.2.accessedAddresses then
              (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess)
            else (res1.2, gasSelfDestruct)).1.getBal = res1.2.getBal := by
        funext a
        split <;> rfl
      cases h2 : chargeGas
          (if ((if res1.1 ∉ res1.2.accessedAddresses then
                      (addAccessedAddress res1.2 res1.1,
                        gasSelfDestruct + gasColdAccountAccess)
                    else (res1.2, gasSelfDestruct)).1.getAcct res1.1).Empty ∧
                ¬(res1.2.getAcct sevm.currentTarget).bal = 0 then
            (if res1.1 ∉ res1.2.accessedAddresses then
                  (addAccessedAddress res1.2 res1.1,
                    gasSelfDestruct + gasColdAccountAccess)
                else (res1.2, gasSelfDestruct)).2 + gasSelfDestructNewAccount
          else
            (if res1.1 ∉ res1.2.accessedAddresses then
                (addAccessedAddress res1.2 res1.1,
                  gasSelfDestruct + gasColdAccountAccess)
              else (res1.2, gasSelfDestruct)).2)
          (if res1.1 ∉ res1.2.accessedAddresses then
              (addAccessedAddress res1.2 res1.1,
                gasSelfDestruct + gasColdAccountAccess)
            else (res1.2, gasSelfDestruct)).1 <;> dsimp
      case error err =>
        intro run
        rw [← run]
        apply Devm.balNoninc_of_getBal_eq
        rw [chargeGas_err_snd h2]
        exact hacc.trans hpop
      case ok res2 =>
        have hpre : res2.getBal = pre.getBal := by
          funext a
          exact (chargeGas_getBal_eq h2 a).trans
            (congrFun (hacc.trans hpop) a)
        cases h3 : assertDynamic sevm res2
        case error err =>
          intro run
          rw [← run]
          apply Devm.balNoninc_of_getBal_eq
          have herr : err.2 = res2 := by
            dsimp [assertDynamic] at h3
            exact Except.assert_err_snd h3
          rw [herr]
          exact hpre
        case ok _ =>
          cases h4 : res2.subBal sevm.currentTarget
              (res1.2.getAcct sevm.currentTarget).bal <;> dsimp [Option.toExcept]
          case none =>
            intro run
            rw [← run]
            exact Devm.balNoninc_of_getBal_eq hpre
          case some res3 =>
            have hsub : res2.state.subBal sevm.currentTarget
                (res1.2.getAcct sevm.currentTarget).bal = some res3.state := by
              dsimp [Devm.subBal, Option.bind] at h4
              cases hs : res2.state.subBal sevm.currentTarget
                  (res1.2.getAcct sevm.currentTarget).bal
              · rw [hs] at h4
                contradiction
              · rw [hs] at h4
                injection h4 with heq
                subst heq
                rfl
            have htransfer : State.BalNoninc pre.state
                (res3.addBal res1.1
                  (res1.2.getAcct sevm.currentTarget).bal).state := by
              have ht := State.sub_addBal_noninc (dst := res1.1) hsub
              have hbal : res2.state.bal = pre.state.bal := hpre
              unfold State.BalNoninc State.balSum at ht ⊢
              rw [hbal] at ht
              exact ht
            by_cases hdel : sevm.currentTarget ∈
                (res3.addBal res1.1
                  (res1.2.getAcct sevm.currentTarget).bal).createdAccounts
            · simp only [hdel, if_pos]
              intro run
              rw [← run]
              unfold Execution.Rel Outcome.Rel
              apply Devm.balNoninc_of_state
              apply balNoninc_refl_trans.1.2 htransfer
              exact State.setBal_zero_noninc _ _
            · simp only [hdel]
              intro run
              rw [← run]
              unfold Execution.Rel Outcome.Rel
              exact Devm.balNoninc_of_state htransfer

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: unfold `Msg.benvAfterTransfer` and split on
`shouldTransferValue`.  The false branch is reflexive.  In the true branch,
errors carry the original state; a successful subtraction followed by addition
is exactly `State.sub_addBal_noninc`.  This removes the existing `SumNof`
assumption needed only for an equality theorem: nonincrease holds unconditionally.
-/
lemma Msg.benvAfterTransfer_balance_effect {msg : Msg}
    {out : Except (String × _root_.State × AdrSet × Tra) Benv}
    (h : msg.benvAfterTransfer = out) :
    State.BalNoninc msg.benv.state (BenvExecution.state out) := by
  by_cases h_stv : msg.shouldTransferValue = true
  · unfold Msg.benvAfterTransfer at h
    rw [h_stv] at h
    simp only [if_true] at h
    unfold Benv.subBal at h
    rcases h_sub : msg.benv.state.subBal msg.caller msg.value with _ | st_mid
    · rw [h_sub] at h
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
      rw [← h]
      exact Nat.le_refl _
    · rw [h_sub] at h
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
      rw [← h]
      change State.BalNoninc msg.benv.state (st_mid.addBal msg.currentTarget msg.value)
      exact State.sub_addBal_noninc h_sub
  · unfold Msg.benvAfterTransfer at h
    rw [if_neg h_stv] at h
    rw [← h]
    exact Nat.le_refl _

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: unfold `processCreateMessage.chargeCodeGas`.  Every branch
either returns the input error state or changes only gas.  Establish state
equality using the state field of `Devm.burn_of_chargeGas`, then weaken equality
to `Devm.BalNoninc`.
-/
lemma processCreateMessage.chargeCodeGas_balance_effect
    {pre : Devm} {out : Execution}
    (h : processCreateMessage.chargeCodeGas pre = out) :
    Execution.Rel Devm.BalNoninc pre out := by
  rcases out with ⟨err, d⟩ | d <;> simp only [Execution.Rel, Outcome.Rel]
  · simp only [processCreateMessage.chargeCodeGas] at h
    split at h
    · simp only [Except.error.injEq] at h
      cases h
      exact balNoninc_refl_trans.2.1 pre
    · dsimp [Bind.bind, Except.bind] at h
      split at h
      · rename_i code neq ex errCharge hCharge
        simp only [Except.error.injEq] at h
        cases h
        have hstate := chargeGas_err_snd hCharge
        change d = pre at hstate
        rw [hstate]
        exact balNoninc_refl_trans.2.1 pre
      · split at h
        · simp only [Except.error.injEq] at h
          cases h
          rename_i code neq ex hSize hCharge
          have hb := Devm.burn_of_chargeGas hCharge
          apply Devm.balNoninc_of_state
          rw [hb.state]
          exact balNoninc_refl_trans.1.1 d.state
        · cases h
  · simp only [id]
    simp only [processCreateMessage.chargeCodeGas] at h
    split at h
    · cases h
    · dsimp [Bind.bind, Except.bind] at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i code neq ex hSize hCharge
          simp only [Except.ok.injEq] at h
          cases h
          have hb := Devm.burn_of_chargeGas hSize
          apply Devm.balNoninc_of_state
          rw [hb.state]
          exact balNoninc_refl_trans.1.1 d.state

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: unfold `executePrecomp`/`applyPrecompResult` only far enough to
show that each precompile result changes gas/output/error data but not `state`.
Reuse the existing `executePrecomp_inv_getCode` proof pattern, replacing the
accessor conclusion by equality of `state`, then weaken to balance nonincrease.
-/
lemma executePrecomp_balance_effect {evm : Evm} {a : Adr} {out : Execution}
    (h : executePrecomp evm a = out) :
    Execution.Rel Devm.BalNoninc evm.dyna out := by
  subst out
  unfold executePrecomp applyPrecompResult Execution.Rel Outcome.Rel
    Devm.BalNoninc Devm.balSum State.balSum
  cases precompileRun evm a <;> rfl

/-
(1) Difficulty: ★★★★★
(2) Proof sketch: unfold the relational `ProcessMessage` definition.  First use
`Msg.benvAfterTransfer_balance_effect`.  On transfer failure, the error state is
the original and the result is immediate.  On success, invert `ExecuteCode`:
precompile paths use `executePrecomp_balance_effect`; bytecode paths use `hxl`.
Then inspect `executeCode.handleError` and the final error flag.  A failed child
rolls back to the pre-transfer state; a successful child preserves the child
nonincrease fact.  Compose initial transfer and execution with transitivity of
`State.BalNoninc`.
-/
lemma ProcessMessage.balance_effect {msg : Msg} {xl : Xlot}
    {out : MessageExecution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : ProcessMessage msg xl out) :
    MessageExecution.Rel State.BalNoninc msg.benv.state out := by
  sorry

/-
(1) Difficulty: ★★★★☆
(2) Proof sketch: unfold `ProcessCreateMessage`.  Apply
`ProcessMessage.balance_effect` to the inner message, noting that `setStor` and
`incrNonce` in `processCreateMessage.msg` leave balances unchanged.  On success,
`chargeCodeGas_balance_effect` and `setCode` preserve balances.  Exceptional
halt and explicit rollback return the original state, while the nonexceptional
error exposes the already-bounded child state.
-/
lemma ProcessCreateMessage.balance_effect {msg : Msg} {xl : Xlot}
    {out : MessageExecution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : ProcessCreateMessage msg xl out) :
    MessageExecution.Rel State.BalNoninc msg.benv.state out := by
  dsimp only [ProcessCreateMessage] at run
  rcases run with ⟨ex', run_pm, h_split⟩
  have h_seed : (processCreateMessage.msg msg).benv.state.bal = msg.benv.state.bal := by
    change ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
      msg.currentTarget).bal = msg.benv.state.bal
    rw [State.incrNonce_bal, State.setStor_bal]
  have h_pm := ProcessMessage.balance_effect hxl run_pm
  unfold MessageExecution.Rel State.BalNoninc State.balSum at h_pm
  rw [h_seed] at h_pm
  dsimp only [Except.Split] at h_split
  rcases h_split with ⟨x, h_ex', h_out⟩ | ⟨evm, h_ex', h_body⟩
  · subst ex'
    subst out
    exact h_pm
  · subst ex'
    by_cases h_err : evm.error.isNone = true
    · rw [if_pos h_err] at h_body
      rcases h_cg : processCreateMessage.chargeCodeGas evm with ⟨err, evm'⟩ | evm'
      · rw [h_cg] at h_body
        dsimp only at h_body
        by_cases h_halt : isExceptionalHalt err
        · rw [if_pos h_halt] at h_body
          rw [← h_body]
          exact balNoninc_refl_trans.1.1 _
        · rw [if_neg h_halt] at h_body
          have h_charge := processCreateMessage.chargeCodeGas_balance_effect h_cg
          unfold Execution.Rel Outcome.Rel Devm.BalNoninc Devm.balSum State.balSum at h_charge
          dsimp only [id] at h_charge
          dsimp only [MessageExecution.state] at h_pm
          rw [← h_body]
          exact Nat.le_trans h_charge h_pm
      · rw [h_cg] at h_body
        dsimp only at h_body
        have h_charge := processCreateMessage.chargeCodeGas_balance_effect h_cg
        unfold Execution.Rel Outcome.Rel Devm.BalNoninc Devm.balSum State.balSum at h_charge
        dsimp only [id] at h_charge
        dsimp only [MessageExecution.state] at h_pm
        rw [← h_body]
        change sum (evm'.state.setCode msg.currentTarget ⟨⟨evm'.output⟩⟩).bal ≤
          sum msg.benv.state.bal
        rw [State.setCode_bal]
        exact Nat.le_trans h_charge h_pm
    · rw [if_neg h_err] at h_body
      rw [← h_body]
      exact balNoninc_refl_trans.1.1 _

/-
(1) Difficulty: ★★★★★
(2) Proof sketch: follow the existing `GenericCall.inv_nof` inversion, but carry
the stronger relation rather than a unary bound.  All preparation steps preserve
state.  Apply `ProcessMessage.balance_effect hxl` to the child.  Both
`incorporateChildOnError` and `incorporateChildOnSuccess` install `child.state`,
so inherit the child relation; push/memory-write cleanup preserves it.  Depth
failure is reflexive.  Compose with transitivity where intermediate states occur.
-/
lemma GenericCall.balance_effect
    {sevm : Sevm} {pre : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv istat : Bool}
    {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCall sevm pre gas value caller target codeAddress
      stv istat ii is oi os code dp xl out) :
    Execution.Rel Devm.BalNoninc pre out := by
  sorry

/-
(1) Difficulty: ★★★★★
(2) Proof sketch: follow `GenericCreate.inv_nof`.  Stack, gas, memory, nonce,
and return-data preparation preserve balances.  Failure branches are reflexive.
For the creation branch apply `ProcessCreateMessage.balance_effect hxl` to the
child.  Incorporating the child installs its state and the final push preserves
it.  Be careful that creation's endowment transfer occurs inside the child
message and is already covered by `Msg.benvAfterTransfer_balance_effect`.
-/
lemma GenericCreate.balance_effect
    {sevm : Sevm} {pre : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCreate sevm pre endowment newAddress mi ms xl out) :
    Execution.Rel Devm.BalNoninc pre out := by
  sorry

/-
(1) Difficulty: ★★★★★
(2) Proof sketch: cases on the six `Xinst` constructors and invert the leading
stack pops/gas charges as in `Xinst.inv_nof_gen`.  These preparations preserve
balances for both success and error results.  The terminal semantic call is
either `GenericCreate.balance_effect` or `GenericCall.balance_effect`; compose
the equal preparation effects with that result.  This is long but conceptually
uniform, and should be the last Xinst-wide balance case split needed.
-/
lemma Xinst.balance_effectGen (x : Xinst) :
    Xinst.EffectGen Devm.BalNoninc x := by
  sorry

/-
(1) Difficulty: ★★☆☆☆
(2) Proof sketch: cases on `n`.  PUSH uses
`Ninst.push_balance_effectGen`; REG uses `Ninst.effectGen_reg` with
`Rinst.balance_effect`; EXEC uses `Ninst.effectGen_exec` with
`Xinst.balance_effectGen`.
-/
lemma Ninst.balance_effectGen (n : Ninst) :
    Ninst.EffectGen Devm.BalNoninc n := by
  cases n
  case reg r =>
    apply Ninst.effectGen_reg
    apply Rinst.balance_effect
  case exec x =>
    apply Ninst.effectGen_exec
    apply Xinst.balance_effectGen
  case push xs hxs =>
    apply Ninst.push_balance_effectGen

/-
(1) Difficulty: ★★☆☆☆
(2) Proof sketch: obtain reflexivity/transitivity from `balNoninc_refl_trans`
and instantiate the generic `Exec.effect` with `Ninst.balance_effectGen`,
`Jinst.balance_effect`, and `Linst.balance_effect`.  No recursion or instruction
case split should appear in this proof.
-/
theorem Exec.balance_effect {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    Execution.Rel Devm.BalNoninc pre out :=
  Exec.effect balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2 Ninst.balance_effectGen Jinst.balance_effect Linst.balance_effect run

/-
(1) Difficulty: ★★☆☆☆
(2) Proof sketch: instantiate `Ninst.effect_of_effectGen` with the balance
relations and the three balance effect tables.  This is the public instruction
theorem corresponding to `Ninst.Run`; it should contain no semantic inversion.
-/
lemma Ninst.balance_effect (n : Ninst) : Ninst.Effect Devm.BalNoninc n := by
  apply Ninst.effect_of_effectGen balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2
  · exact Ninst.balance_effectGen
  · exact Jinst.balance_effect
  · exact Linst.balance_effect

/-
(1) Difficulty: ★★☆☆☆
(2) Proof sketch: apply generic `Func.effect` with transitivity of
`Devm.BalNoninc`.  `PopBurn` and `Burn` preserve state by their structure fields,
so they satisfy the relation reflexively.  Use `Ninst.balance_effect` and
`Linst.balance_effect` for the instruction hypotheses.  This theorem can replace
the separate `Func.inv_nof` traversal.
-/
theorem Func.balance_effect {fs : List Func} {sevm : Sevm}
    {pre post : Devm} {p : Func}
    (run : Func.Run fs sevm pre p post) : Devm.BalNoninc pre post := by
  apply Func.effect (R := Devm.BalNoninc) (htrans := balNoninc_refl_trans.2.2) _ _ Ninst.balance_effect Linst.balance_effect run
  · intro xs pr po hpop
    apply Devm.balNoninc_of_state
    rw [hpop.state]
    exact balNoninc_refl_trans.1.1 _
  · intro pr po hburn
    apply Devm.balNoninc_of_state
    rw [hburn.state]
    exact balNoninc_refl_trans.1.1 _

/-! ## 6. Executable wrappers and the Solvent.lean endpoint -/

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: cases on `xl`.  In the `.some` case unpack `Xlot.Good` into a
smaller `exec` equation and the implication from the child's recursion-limit
error to the outer one.  `hfit` makes the child result fit; apply `of_exec` to
obtain `Nonempty (Exec ...)`, then `Exec.balance_effect`.  This is the executable
oracle bridge needed by both `processMessage` wrappers.
-/
lemma Xlot.balance_rel_of_good {ξ υ : Type} {lim : Nat}
    {outer : Except (String × ξ) υ} {xl : Xlot}
    (hfit : outer.Fit) (hgood : xl.Good lim outer) :
    Xlot.Rel Devm.BalNoninc xl := by
  rcases xl with _ | ⟨sevm, devm, exn⟩
  · constructor
  · rcases hgood with ⟨lim', _, exec_eq, lim_of_lim⟩
    have hfit' : exn.Fit := fun h => hfit (lim_of_lim h)
    rcases of_exec lim' 0 sevm devm exn hfit' exec_eq with ⟨exc⟩
    exact Exec.balance_effect exc

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: the successful output is automatically `Fit`.  Apply
`of_processMessage msg lim (.ok post)` to get `xl`, `Xlot.Good`, and the
relational `ProcessMessage` run.  Convert `Good` with
`Xlot.balance_rel_of_good`, apply `ProcessMessage.balance_effect`, and simplify
`MessageExecution.state (.ok post)`.
-/
lemma processMessage_balance_noninc {msg : Msg} {lim : Nat} {post : Devm}
    (h : processMessage msg lim = .ok post) :
    State.BalNoninc msg.benv.state post.state := by
  have hfit : (Except.ok post : Except (String × State × AdrSet × Tra) Devm).Fit := by
    intro hlim
    simp [Except.Lim, Except.toError?] at hlim
  obtain ⟨xl, hgood, hrun⟩ := of_processMessage msg lim (.ok post) hfit h
  have heff := ProcessMessage.balance_effect (Xlot.balance_rel_of_good hfit hgood) hrun
  change State.BalNoninc msg.benv.state post.state at heff
  exact heff

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: identical wrapper structure to `processMessage_balance_noninc`,
using `of_processCreateMessage` and `ProcessCreateMessage.balance_effect`.
-/
lemma processCreateMessage_balance_noninc
    {msg : Msg} {lim : Nat} {post : Devm}
    (h : processCreateMessage msg lim = .ok post) :
    State.BalNoninc msg.benv.state post.state := by
  have hfit : (Except.ok post : Except (String × State × AdrSet × Tra) Devm).Fit := by
    simp [Except.Fit, Except.Lim]
    change ¬ (none : Option String) = some "RecursionLimit"
    simp
  rcases of_processCreateMessage msg lim (.ok post) hfit h with ⟨xl, hgood, hrun⟩
  have hxl : Xlot.Rel Devm.BalNoninc xl := Xlot.balance_rel_of_good hfit hgood
  have heff := ProcessCreateMessage.balance_effect hxl hrun
  exact heff

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: unfold `setDelegation` and its loop.  Delegation authorization
steps alter nonce/code but never balances.  Prove or reuse a loop invariant
`msg'.benv.state.bal = msg.benv.state.bal`; turn this function equality into
`balSum` equality.  The final delegated-code rewrite also preserves the state.
This lemma isolates transaction-level preprocessing from EVM execution.
-/
lemma setDelegationStep_bal_eq {auth : Auth} {msg msg' : Msg} {rc rc' : B256}
    (h : setDelegationStep auth msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.state.bal = msg.benv.state.bal := by
  unfold setDelegationStep at h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩; rfl
    · split at h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩; rfl
        · cases h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩; rfl
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩; rfl
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            show ((msg.benv.state.setCode _ _).incrNonce _).bal =
              msg.benv.state.bal
            rw [State.incrNonce_bal, State.setCode_bal]

lemma setDelegationLoop_bal_eq {auths : List Auth} {msg msg' : Msg}
    {rc rc' : B256}
    (h : setDelegationLoop auths msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.state.bal = msg.benv.state.bal := by
  induction auths generalizing msg rc with
  | nil =>
    unfold setDelegationLoop at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  | cons auth auths ih =>
    unfold setDelegationLoop at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i p h_step
      obtain ⟨msgS, rcS⟩ := p
      exact (ih h).trans (setDelegationStep_bal_eq h_step)

lemma setDelegation_balSum_eq {msg msg' : Msg} {refund : B256}
    (h : setDelegation msg = .ok ⟨msg', refund⟩) :
    State.balSum msg'.benv.state = State.balSum msg.benv.state := by
  unfold setDelegation at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p h_loop
    obtain ⟨msgL, rcL⟩ := p
    have h_bal := setDelegationLoop_bal_eq h_loop
    split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      unfold State.balSum
      rw [show ({ msgL with
        code := msgL.benv.state.getCode _ } : Msg).benv.state.bal =
          msgL.benv.state.bal from rfl, h_bal]

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: unfold `processMessageCall.call`.  In the no-authorization
branch the message state is unchanged; otherwise use `setDelegation_balSum_eq`.
The delegated-code `msgPc` update changes no state.  Invert the successful
`processMessage` call, apply `processMessage_balance_noninc`, and simplify the
final output constructor.  Refund/log/account-delete calculations do not alter
the returned state.
-/
lemma processMessageCall.call_balance_noninc
    {msg : Msg} {post : _root_.State} {out : MsgCallOutput}
    (h : processMessageCall.call msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall.call at h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    unfold Except.bimap at h
    split at h
    · injection h
    · rename_i evm h_evm
      split at h_evm
      · injection h_evm
      · rename_i evm' h_pm
        simp only [id_eq, Except.ok.injEq] at h_evm
        subst h_evm
        have hbal := processMessage_balance_noninc h_pm
        have hpre : State.BalNoninc msg.benv.state evm'.state := by
          split at hbal <;> exact hbal
        split at h
        · split at h
          · injection h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact hpre
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact hpre
  · rcases h_del : setDelegation msg with ⟨err⟩ | ⟨⟨msgD, val⟩⟩
    · simp only [h_del, bind, Except.bind] at h
      injection h
    · simp only [h_del, bind, Except.bind] at h
      have h_sum := setDelegation_balSum_eq h_del
      unfold Except.bimap at h
      split at h
      · injection h
      · rename_i evm h_evm
        split at h_evm
        · injection h_evm
        · rename_i evm' h_pm
          simp only [id_eq, Except.ok.injEq] at h_evm
          subst h_evm
          have hbal := processMessage_balance_noninc h_pm
          have hpre : State.BalNoninc msg.benv.state evm'.state := by
            have hD : State.BalNoninc msgD.benv.state evm'.state := by
              split at hbal <;> exact hbal
            unfold State.BalNoninc at *
            omega
          split at h
          · split at h
            · injection h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, _⟩
              exact hpre
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact hpre

/-
(1) Difficulty: ★★★☆☆
(2) Proof sketch: unfold `processMessageCall.create`.  Collision/failure paths
return the original state.  In the proper creation path invert the successful
`processCreateMessage` call and apply `processCreateMessage_balance_noninc`;
the subsequent output construction does not change the returned state.
-/
lemma processMessageCall.create_balance_noninc
    {msg : Msg} {post : _root_.State} {out : MsgCallOutput}
    (h : processMessageCall.create msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall.create at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩
    exact le_refl _
  · simp only [bind, Except.bind] at h
    unfold Except.bimap at h
    split at h
    · injection h
    · rename_i evm h_evm
      split at h_evm
      · injection h_evm
      · rename_i evm' h_pm
        simp only [id_eq, Except.ok.injEq] at h_evm
        subst h_evm
        have hbal := processCreateMessage_balance_noninc h_pm
        split at h
        · split at h
          · injection h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact hbal
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact hbal

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: unfold `processMessageCall`, split on `msg.target.isNone`, and
apply the corresponding call/create balance lemma.  This is the relational form
of the currently missing `processMessageCall_sum_le` theorem.
-/
lemma processMessageCall_balance_noninc
    {msg : Msg} {post : _root_.State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall at h
  split at h
  · exact processMessageCall.create_balance_noninc h
  · exact processMessageCall.call_balance_noninc h

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: apply `processMessageCall_balance_noninc h` and unfold
`State.BalNoninc`/`State.balSum`.  This statement is intentionally identical to
the sorry in `Solvent.lean` after removing the `Temp` namespace.
-/
lemma processMessageCall_sum_le
    {msg : Msg} {post : _root_.State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨post, out⟩) :
    sum post.bal ≤ sum msg.benv.state.bal := by
  exact processMessageCall_balance_noninc h

/-
(1) Difficulty: ★☆☆☆☆
(2) Proof sketch: combine `processMessageCall_balance_noninc h` with
`State.SumNof.of_noninc`.  This is the promised non-overflow-preservation
corollary; analogous corollaries for `Exec`, `Ninst`, and `Func` should now be
one-liners rather than separate recursive developments.
-/
lemma processMessageCall_preserves_sumNof
    {msg : Msg} {post : _root_.State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨post, out⟩)
    (hnof : State.SumNof msg.benv.state) : State.SumNof post := by
  exact State.SumNof.of_noninc (processMessageCall_balance_noninc h) hnof

end Temp
