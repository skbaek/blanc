import Blanc.ExecutionFrames

/-!
# Accessed-address growth along a frame

The EIP-2929 accessed-address set of a frame only grows while the frame runs: every
instruction either leaves it alone or inserts into it, a successful child is united into it, and
a failed child is dropped without touching the set the parent already had.  A child frame starts
from the set of its parent at the spawning instruction.

This module states that as a walk of Jaune's interpreter, in the success-only form the frame
induction needs: an outcome that is an error is never continued from, so nothing is claimed of
it.  `Devm.AccGrow` is the relation, `Except.OkOn` the success-only lift.
-/

namespace Blanc

open Jaune

/-- The accessed-address set only grows. -/
def Devm.AccGrow (d d' : Devm) : Prop :=
  ∀ a, a ∈ d.accessedAddresses → a ∈ d'.accessedAddresses

theorem Devm.AccGrow.rfl {d : Devm} : Devm.AccGrow d d := fun _ h => h

theorem Devm.AccGrow.trans {a b c : Devm} (hab : Devm.AccGrow a b) (hbc : Devm.AccGrow b c) :
    Devm.AccGrow a c := fun x hx => hbc x (hab x hx)

theorem Devm.AccGrow.of_eq {d d' : Devm}
    (h : d.accessedAddresses = d'.accessedAddresses) : Devm.AccGrow d d' :=
  fun _ hx => h ▸ hx

/-- A property of every successful result. -/
def Except.OkOn {ε α : Type} (P : α → Prop) (x : Except ε α) : Prop :=
  ∀ a, x = .ok a → P a

namespace Except.OkOn

theorem ok {ε α : Type} {P : α → Prop} {a : α} (h : P a) : Except.OkOn P (Except.ok a : Except ε α) := by
  intro b hb
  cases hb
  exact h

theorem error {ε α : Type} {P : α → Prop} {e : ε} : Except.OkOn P (Except.error e : Except ε α) := by
  intro b hb
  cases hb

theorem bind {ε α β : Type} {P : α → Prop} {Q : β → Prop} {x : Except ε α}
    {f : α → Except ε β} (hx : Except.OkOn P x) (hf : ∀ a, P a → Except.OkOn Q (f a)) :
    Except.OkOn Q (x >>= f) := by
  intro b hb
  cases x with
  | error e => cases hb
  | ok a => exact hf a (hx a rfl) b hb

theorem mono {ε α : Type} {P Q : α → Prop} {x : Except ε α} (h : Except.OkOn P x)
    (hPQ : ∀ a, P a → Q a) : Except.OkOn Q x :=
  fun a ha => hPQ a (h a ha)

theorem pure {ε α : Type} {P : α → Prop} {a : α} (h : P a) :
    Except.OkOn P (Pure.pure a : Except ε α) := Except.OkOn.ok h

theorem bind_ok {ε α β : Type} {Q : β → Prop} {x : α} {f : α → Except ε β}
    (h : Except.OkOn Q (f x)) : Except.OkOn Q (Except.ok x >>= f) := h

end Except.OkOn

/-- Extend a growth fact by a step that leaves the accessed set alone. -/
theorem Devm.AccGrow.keep {pre d d' : Devm} (h : Devm.AccGrow pre d)
    (e : d'.accessedAddresses = d.accessedAddresses) : Devm.AccGrow pre d' :=
  fun a ha => e ▸ h a ha

theorem liftMach_okOn {α : Type} (core : Mach → Footprint.Outcome Mach α) {pre d : Devm}
    (h : Devm.AccGrow pre d) :
    Except.OkOn (fun r : α × Devm => Devm.AccGrow pre r.2) (liftMach core d) := by
  intro r hr
  unfold liftMach Footprint.liftOutcome at hr
  split at hr <;> cases hr
  exact h

theorem liftMachExecution_okOn (core : Mach → Footprint.Outcome Mach Unit) {pre d : Devm}
    (h : Devm.AccGrow pre d) :
    Except.OkOn (Devm.AccGrow pre) (liftMachExecution core d) := by
  intro r hr
  unfold liftMachExecution Footprint.toExecution at hr
  split at hr
  · cases hr
  · rename_i x heq
    cases hr
    exact (liftMach_okOn core h) _ heq


/-! ### Primitives -/

theorem Devm.pop_okOn {pre d : Devm} (h : Devm.AccGrow pre d) :
    Except.OkOn (fun r : B256 × Devm => Devm.AccGrow pre r.2) (Devm.pop d) :=
  liftMach_okOn _ h

theorem Devm.popToNat_okOn {pre d : Devm} (h : Devm.AccGrow pre d) :
    Except.OkOn (fun r : Nat × Devm => Devm.AccGrow pre r.2) (Devm.popToNat d) :=
  liftMach_okOn _ h

theorem Devm.popToAdr_okOn {pre d : Devm} (h : Devm.AccGrow pre d) :
    Except.OkOn (fun r : Adr × Devm => Devm.AccGrow pre r.2) (Devm.popToAdr d) :=
  liftMach_okOn _ h

theorem Devm.popN_okOn {pre d : Devm} (n : Nat) (h : Devm.AccGrow pre d) :
    Except.OkOn (fun r : List B256 × Devm => Devm.AccGrow pre r.2) (Devm.popN d n) :=
  liftMach_okOn _ h

theorem chargeGas_okOn {pre d : Devm} (c : Nat) (h : Devm.AccGrow pre d) :
    Except.OkOn (Devm.AccGrow pre) (chargeGas c d) :=
  liftMachExecution_okOn _ h

theorem Devm.push_okOn {pre d : Devm} (x : B256) (h : Devm.AccGrow pre d) :
    Except.OkOn (Devm.AccGrow pre) (Devm.push x d) :=
  liftMachExecution_okOn _ h

theorem pushItem_okOn {pre d : Devm} (x : B256) (c : Nat) (h : Devm.AccGrow pre d) :
    Except.OkOn (Devm.AccGrow pre) (pushItem x c d) :=
  liftMachExecution_okOn _ h

theorem applyUnary_okOn {pre d : Devm} (f : B256 → B256) (c : Nat) (h : Devm.AccGrow pre d) :
    Except.OkOn (Devm.AccGrow pre) (applyUnary f c d) :=
  liftMachExecution_okOn _ h

theorem applyBinary_okOn {pre d : Devm} (f : B256 → B256 → B256) (c : Nat)
    (h : Devm.AccGrow pre d) : Except.OkOn (Devm.AccGrow pre) (applyBinary f c d) :=
  liftMachExecution_okOn _ h

theorem applyTernary_okOn {pre d : Devm} (f : B256 → B256 → B256 → B256) (c : Nat)
    (h : Devm.AccGrow pre d) : Except.OkOn (Devm.AccGrow pre) (applyTernary f c d) :=
  liftMachExecution_okOn _ h

theorem Except.assert_okOn {ε : Type} (p : Prop) [Decidable p] (e : ε) :
    Except.OkOn (fun _ : Unit => True) (Except.assert p e) := fun _ _ => trivial

theorem assertDynamic_okOn (sevm : Sevm) (d : Devm) :
    Except.OkOn (fun _ : Unit => True) (assertDynamic sevm d) := fun _ _ => trivial

theorem addAccessedAddress_accGrow (d : Devm) (a : Adr) :
    Devm.AccGrow d (addAccessedAddress d a) := by
  intro x hx
  exact Std.HashSet.mem_insert.2 (Or.inr hx)

theorem Devm.AccGrow.warm {pre d : Devm} (h : Devm.AccGrow pre d) (a : Adr) :
    Devm.AccGrow pre (addAccessedAddress d a) :=
  h.trans (addAccessedAddress_accGrow d a)

theorem Devm.pop_map_okOn {pre d : Devm} (h : Devm.AccGrow pre d) :
    Except.OkOn (Devm.AccGrow pre) (Devm.pop d <&> Prod.snd) := by
  intro r hr
  have hx := Devm.pop_okOn h
  cases hp : Devm.pop d with
  | error e => rw [hp] at hr; cases hr
  | ok a =>
    rw [hp] at hr
    cases hr
    exact hx a hp

theorem Devm.AccGrow.balReadAccount {pre d : Devm} (h : Devm.AccGrow pre d)
    (rules : ForkRules) (a : Adr) : Devm.AccGrow pre (d.balReadAccount rules a) :=
  h.keep (by simp)

theorem Devm.AccGrow.balReadStorage {pre d : Devm} (h : Devm.AccGrow pre d)
    (rules : ForkRules) (a : Adr) (k : B256) : Devm.AccGrow pre (d.balReadStorage rules a k) :=
  h.keep (by simp)

theorem Devm.AccGrow.memWrite {pre d : Devm} (h : Devm.AccGrow pre d) (i : Nat) (v : Bytes) :
    Devm.AccGrow pre (d.memWrite i v) := h.keep (Eq.refl _)

theorem Devm.AccGrow.memRead {pre d : Devm} (h : Devm.AccGrow pre d) (i n : Nat) :
    Devm.AccGrow pre (d.memRead i n).2 := h.keep (Eq.refl _)

theorem Devm.AccGrow.memExtends {pre d : Devm} (h : Devm.AccGrow pre d) (ps : List (Nat × Nat)) :
    Devm.AccGrow pre (d.memExtends ps) := h.keep (Eq.refl _)

theorem Devm.AccGrow.withStack {pre d : Devm} (h : Devm.AccGrow pre d) (s : List B256) :
    Devm.AccGrow pre (d.withStack s) := h.keep (Eq.refl _)

theorem Devm.AccGrow.withGasLeft {pre d : Devm} (h : Devm.AccGrow pre d) (g : Nat) :
    Devm.AccGrow pre (d.withGasLeft g) := h.keep (Eq.refl _)

theorem Devm.AccGrow.withReturnData {pre d : Devm} (h : Devm.AccGrow pre d) (r : Bytes) :
    Devm.AccGrow pre (d.withReturnData r) := h.keep (Eq.refl _)

theorem Devm.AccGrow.withOutput {pre d : Devm} (h : Devm.AccGrow pre d) (r : Bytes) :
    Devm.AccGrow pre (d.withOutput r) := h.keep (Eq.refl _)

theorem Devm.AccGrow.withRefundCounter {pre d : Devm} (h : Devm.AccGrow pre d) (r : Int) :
    Devm.AccGrow pre (d.withRefundCounter r) := h.keep (Eq.refl _)

theorem Devm.AccGrow.addLog {pre d : Devm} (h : Devm.AccGrow pre d) (l : Log) :
    Devm.AccGrow pre (d.addLog l) := h.keep (Eq.refl _)

theorem Devm.AccGrow.setStorVal {pre d : Devm} (h : Devm.AccGrow pre d) (a : Adr) (k v : B256) :
    Devm.AccGrow pre (d.setStorVal a k v) := h.keep (Eq.refl _)

theorem Devm.AccGrow.setTransVal {pre d : Devm} (h : Devm.AccGrow pre d) (a : Adr) (k v : B256) :
    Devm.AccGrow pre (d.setTransVal a k v) := h.keep (Eq.refl _)

theorem Devm.AccGrow.addStorageKey {pre d : Devm} (h : Devm.AccGrow pre d) (a : Adr) (k : B256) :
    Devm.AccGrow pre (addAccessedStorageKey d a k) := h.keep (Eq.refl _)

theorem Devm.AccGrow.incrNonce {pre d : Devm} (h : Devm.AccGrow pre d) (a : Adr) :
    Devm.AccGrow pre (d.incrNonce a) := h.keep (Eq.refl _)

/-- A failed child is dropped without touching the parent's accessed set. -/
theorem incorporateChildOnError_accGrow (parent child : Devm) (rd : Bytes) :
    Devm.AccGrow parent (incorporateChildOnError parent child rd) :=
  Devm.AccGrow.of_eq (Eq.refl _)

/-- A successful child is united into the parent's accessed set. -/
theorem incorporateChildOnSuccess_accGrow (parent child : Devm) (rd : Bytes) :
    Devm.AccGrow parent (incorporateChildOnSuccess parent child rd) := by
  intro a ha
  exact Std.HashSet.mem_union_of_left ha

theorem Devm.AccGrow.addBal {pre d : Devm} (h : Devm.AccGrow pre d) (a : Adr) (v : B256) :
    Devm.AccGrow pre (d.addBal a v) := h.keep (Eq.refl _)

theorem Devm.AccGrow.setBal {pre d : Devm} (h : Devm.AccGrow pre d) (a : Adr) (v : B256) :
    Devm.AccGrow pre (d.setBal a v) := h.keep (Eq.refl _)

theorem Devm.AccGrow.addAccountToDelete {pre d : Devm} (h : Devm.AccGrow pre d) (a : Adr) :
    Devm.AccGrow pre (addAccountToDelete d a) := h.keep (Eq.refl _)

theorem Devm.subBal_okOn {pre d : Devm} (h : Devm.AccGrow pre d) (a : Adr) (v : B256)
    (e : EvmError × Devm) :
    Except.OkOn (Devm.AccGrow pre) ((d.subBal a v).toExcept e) := by
  intro r hr
  unfold Devm.subBal at hr
  cases hs : d.state.subBal a v with
  | none => simp [hs, Option.toExcept] at hr
  | some st =>
    simp only [hs, Option.toExcept] at hr
    cases hr
    exact h

/-- One step of proving growth of a machine built from a known one by accessed-set-preserving
updates and warmings.  Extensible: later modules add rules. -/
syntax "acc_grow1" : tactic

/-- Prove growth of a machine or call outcome from the hypotheses in scope. -/
macro "acc_grow" : tactic => `(tactic| repeat acc_grow1)

macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible assumption)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.balReadAccount)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.balReadStorage)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.warm)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.memWrite)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.memRead)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.memExtends)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.withStack)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.withGasLeft)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.withReturnData)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.withOutput)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.withRefundCounter)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.addLog)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.setStorVal)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.setTransVal)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.addStorageKey)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.incrNonce)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.addBal)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.setBal)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.addAccountToDelete)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply incorporateChildOnError_accGrow)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply incorporateChildOnSuccess_accGrow)

/-- Peel one bind of a success-only growth goal against the reference machine `pre`.  Every
unification is at reducible transparency: a wrong guess must fail fast instead of unfolding the
interpreter. -/
macro "acc_step " pre:term : tactic =>
  `(tactic| first
      | (with_reducible refine Except.OkOn.bind (P := fun _ : Unit => True) ?_ ?_
         · first
            | with_reducible exact Except.assert_okOn _ _
            | with_reducible exact assertDynamic_okOn _ _
            | with_reducible exact Except.OkOn.error
         intro _ _)
      | (with_reducible refine Except.OkOn.bind (P := fun r => Devm.AccGrow $pre (Prod.snd r)) ?_ ?_
         · first
            | with_reducible exact Devm.pop_okOn (by assumption)
            | with_reducible exact Devm.popToNat_okOn (by assumption)
            | with_reducible exact Devm.popToAdr_okOn (by assumption)
            | with_reducible exact Devm.popN_okOn _ (by assumption)
         intro _ _)
      | (with_reducible refine Except.OkOn.bind (P := Devm.AccGrow $pre) ?_ ?_
         · first
            | focus (with_reducible refine chargeGas_okOn _ ?_; acc_grow; done)
            | focus (with_reducible refine Devm.push_okOn _ ?_; acc_grow; done)
            | focus (with_reducible refine pushItem_okOn _ _ ?_; acc_grow; done)
            | focus (with_reducible refine applyUnary_okOn _ _ ?_; acc_grow; done)
            | focus (with_reducible refine applyBinary_okOn _ _ ?_; acc_grow; done)
            | focus (with_reducible refine applyTernary_okOn _ _ ?_; acc_grow; done)
            | with_reducible exact Devm.pop_map_okOn (by assumption)
            | focus (with_reducible refine Devm.subBal_okOn ?_ _ _ _; acc_grow; done)
         intro _ _))

/-- Walk one arm of an instruction against the reference machine `pre`. -/
macro "acc_walk " pre:term : tactic =>
  `(tactic| repeat (first
      | with_reducible exact Except.OkOn.error
      | split
      | (with_reducible refine Except.OkOn.bind_ok ?_)
      | focus (with_reducible apply Except.OkOn.ok; acc_grow; done)
      | focus (with_reducible apply Except.OkOn.pure; acc_grow; done)
      | acc_step $pre
      | focus (with_reducible refine chargeGas_okOn _ ?_; acc_grow; done)
      | focus (with_reducible refine Devm.push_okOn _ ?_; acc_grow; done)
      | focus (with_reducible refine pushItem_okOn _ _ ?_; acc_grow; done)
      | focus (with_reducible refine applyUnary_okOn _ _ ?_; acc_grow; done)
      | focus (with_reducible refine applyBinary_okOn _ _ ?_; acc_grow; done)
      | focus (with_reducible refine applyTernary_okOn _ _ ?_; acc_grow; done)))

example {pre d : Devm} (h : Devm.AccGrow pre d) (rules : ForkRules) (a : Adr) (i : Nat) (v : Bytes) :
    Except.OkOn (Devm.AccGrow pre) (Except.ok ((Devm.balReadAccount rules a d).memWrite i v) : Except (EvmError × Devm) Devm) := by
  acc_walk pre

theorem liftMachMetaExecution_okOn (core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit)
    {pre d : Devm} (h : Devm.AccGrow pre d)
    (hcore : ∀ m v m' v', core m v = .ok ((), (m', v')) →
      ∀ a, a ∈ v.accessedAddresses → a ∈ v'.accessedAddresses) :
    Except.OkOn (Devm.AccGrow pre) (liftMachMetaExecution core d) := by
  intro r hr
  unfold liftMachMetaExecution liftMachMeta Footprint.liftOutcome Footprint.toExecution at hr
  split at hr
  · cases hr
  · rename_i out hcase
    split at hcase
    · cases hcase
    · rename_i heq
      cases hcase
      obtain ⟨⟩ := hr
      intro a ha
      exact hcore _ _ _ _ heq a (h a ha)

theorem Rinst.balanceCore_acc (rules : ForkRules) (world : World) (mach : Mach) (view : Meta)
    (m' : Mach) (v' : Meta)
    (h : Rinst.balanceCore rules world mach view = .ok ((), (m', v'))) :
    ∀ a, a ∈ view.accessedAddresses → a ∈ v'.accessedAddresses := by
  unfold Rinst.balanceCore at h
  rcases hp : mach.pop with ⟨err, m1⟩ | ⟨x, m1⟩
  · rw [hp] at h; cases h
  · rw [hp] at h
    dsimp only at h
    rcases hc : Mach.chargeGas
        (if x.toAdr ∈ view.accessedAddresses then gasWarmAccess
          else rules.gas.coldAccountAccess) m1 with ⟨err, m2⟩ | ⟨u, m2⟩
    · rw [hc] at h; cases h
    · rw [hc] at h
      dsimp only at h
      rcases hpu : Mach.push (world.state.get x.toAdr).bal m2 with ⟨err, m3⟩ | ⟨u2, m3⟩
      · rw [hpu] at h; cases h
      · rw [hpu] at h
        dsimp only at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        intro a ha
        split <;> (try split) <;> simp_all [Meta.readAccount, Meta.addAccessedAddress]

theorem Rinst.balance_okOn (rules : ForkRules) (devm : Devm) :
    Except.OkOn (Devm.AccGrow devm) (liftMachMetaWorldExecution (Rinst.balanceCore rules) devm) :=
  liftMachMetaExecution_okOn _ Devm.AccGrow.rfl
    (fun _ _ _ _ h => Rinst.balanceCore_acc _ _ _ _ _ _ h)

theorem Rinst.runCore_accGrow (pc : Nat) (sevm : Sevm) (devm : Devm) (r : Rinst)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    Except.OkOn (Devm.AccGrow devm) (Rinst.runCore pc devm sevm r) := by
  have h : Devm.AccGrow devm devm := Devm.AccGrow.rfl
  cases r <;> simp only [Rinst.runCore, hsg]
  case balance => exact Rinst.balance_okOn _ _
  all_goals acc_walk devm

theorem Jinst.runCore_accGrow (pc : Nat) (sevm : Sevm) (devm : Devm) (j : Jinst) :
    Except.OkOn (fun r : Nat × Devm => Devm.AccGrow devm r.2) (Jinst.runCore pc devm sevm j) := by
  have h : Devm.AccGrow devm devm := Devm.AccGrow.rfl
  cases j <;> simp only [Jinst.runCore]
  all_goals acc_walk devm

theorem Linst.run_accGrow (sevm : Sevm) (devm : Devm) (l : Linst)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    Except.OkOn (Devm.AccGrow devm) (Linst.run sevm devm l) := by
  have h : Devm.AccGrow devm devm := Devm.AccGrow.rfl
  cases l <;> simp only [Linst.run, hsg]
  all_goals acc_walk devm

/-! ### Spawned frames and their resumption -/

theorem Resume.run_call_accGrow (parent : Devm) (oi os : Nat)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    Except.OkOn (Devm.AccGrow parent) ((Resume.call parent oi os).run r) := by
  have h : Devm.AccGrow parent parent := Devm.AccGrow.rfl
  simp only [Resume.run]
  refine Except.OkOn.bind (P := fun _ : Devm => True) (fun _ _ => trivial) ?_
  intro child _
  split
  · acc_walk parent
  · acc_walk parent

theorem Resume.run_create_accGrow (parent : Devm) (na : Adr)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    Except.OkOn (Devm.AccGrow parent) ((Resume.create parent na).run r) := by
  have h : Devm.AccGrow parent parent := Devm.AccGrow.rfl
  simp only [Resume.run]
  refine Except.OkOn.bind (P := fun _ : Devm => True) (fun _ _ => trivial) ?_
  intro child _
  split
  · acc_walk parent
  · acc_walk parent

/-! ### The outcome of a call-type instruction -/

/-- Growth of the outcome of a call-type step: a completed step grows the accessed set; a spawn
starts the child from a superset of it and resumes the parent in one. -/
def XStep.AccGrow (devm : Devm) : XStep → Prop
  | .done ex => Except.OkOn (Devm.AccGrow devm) ex
  | .spawn f rsm =>
      (∀ a, a ∈ devm.accessedAddresses → a ∈ f.inner.accessedAddresses) ∧
        ∀ r, Except.OkOn (Devm.AccGrow devm) (rsm.run r)

theorem XStep.AccGrow.done_ok {devm d : Devm} (h : Devm.AccGrow devm d) :
    XStep.AccGrow devm (.done (.ok d)) :=
  Except.OkOn.ok h

theorem XStep.AccGrow.ofExcept {devm : Devm} {e : Except (EvmError × Devm) XStep}
    (h : Except.OkOn (XStep.AccGrow devm) e) : XStep.AccGrow devm (XStep.ofExcept e) := by
  cases e with
  | error e => exact Except.OkOn.error
  | ok st => exact h st rfl

theorem XStep.AccGrow.spawn_call {devm evm1 : Devm} (h : Devm.AccGrow devm evm1)
    (sevm : Sevm) (gas : Nat) (value : B256) (caller target codeAddress : Adr)
    (stv isSt : Bool) (cd : Bytes) (code : ByteArray) (dp : Bool) (oi os : Nat) :
    XStep.AccGrow devm
      (.spawn (Frame.ofCall (callMsg sevm evm1 gas value caller target codeAddress stv isSt cd
        code dp)) (.call evm1 oi os)) :=
  ⟨fun a ha => h a ha, fun r => Except.OkOn.mono (Resume.run_call_accGrow evm1 oi os r)
    (fun _ hx => Devm.AccGrow.trans h hx)⟩

theorem XStep.AccGrow.spawn_create {devm d : Devm} (h : Devm.AccGrow devm d)
    (sevm : Sevm) (g : Nat) (v : B256) (na : Adr) (cd : Bytes) :
    XStep.AccGrow devm
      (.spawn (Frame.ofCreate (createMsg sevm d g v na cd)) (.create d na)) :=
  ⟨fun a ha => h a ha, fun r => Except.OkOn.mono (Resume.run_create_accGrow d na r)
    (fun _ hx => Devm.AccGrow.trans h hx)⟩

theorem Devm.AccGrow.gasAccessDelegation {pre d : Devm} (h : Devm.AccGrow pre d)
    (gas : GasSchedule) (adr : Adr) :
    Devm.AccGrow pre (gas.accessDelegation d adr).2.2.2.2 := by
  unfold GasSchedule.accessDelegation
  dsimp only
  split
  · exact h.warm _
  · exact h

macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply XStep.AccGrow.done_ok)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply XStep.AccGrow.spawn_call)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply XStep.AccGrow.spawn_create)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.accessDelegation)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply Devm.AccGrow.gasAccessDelegation)

theorem genericCall.step_accGrow {devm d : Devm} (h : Devm.AccGrow devm d)
    (sevm : Sevm) (gas : Nat) (value : B256) (caller target codeAddress : Adr)
    (stv isSt : Bool) (ii isz oi osz : Nat) (code : ByteArray) (dp : Bool) :
    XStep.AccGrow devm
      (genericCall.step sevm d gas value caller target codeAddress stv isSt ii isz oi osz code
        dp) := by
  unfold genericCall.step
  dsimp only
  split
  · with_reducible apply XStep.AccGrow.ofExcept
    acc_walk devm
  · acc_grow

theorem genericCreate.step_accGrow {devm d : Devm} (h : Devm.AccGrow devm d)
    (sevm : Sevm) (endowment : B256) (newAddress : Adr) (mi ms : Nat) :
    XStep.AccGrow devm (genericCreate.step sevm d endowment newAddress mi ms) := by
  unfold genericCreate.step
  dsimp only
  with_reducible apply XStep.AccGrow.ofExcept
  acc_walk devm

macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply genericCall.step_accGrow)
macro_rules | `(tactic| acc_grow1) => `(tactic| with_reducible apply genericCreate.step_accGrow)

theorem Xinst.step_accGrow (sevm : Sevm) (devm : Devm) (x : Xinst)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    XStep.AccGrow devm (Xinst.step sevm devm x) := by
  have h : Devm.AccGrow devm devm := Devm.AccGrow.rfl
  cases x <;> simp only [Xinst.step, hsg]
  all_goals with_reducible apply XStep.AccGrow.ofExcept
  all_goals acc_walk devm

/-! ### One interpreter step -/

/-- Growth across one interpreter step. -/
def Step.AccGrow (devm : Devm) : Step → Prop
  | .halt _ => True
  | .cont _ d => Devm.AccGrow devm d
  | .spawn f rsm _ =>
      (∀ a, a ∈ devm.accessedAddresses → a ∈ f.inner.accessedAddresses) ∧
        ∀ r, Except.OkOn (Devm.AccGrow devm) (rsm.run r)

theorem Step.AccGrow.ofExecution {devm : Devm} {pc : Nat} {e : Execution}
    (h : Except.OkOn (Devm.AccGrow devm) e) : Step.AccGrow devm (Step.ofExecution pc e) := by
  cases e with
  | error e => exact trivial
  | ok d => exact h d rfl

theorem Step.AccGrow.ofJump {devm : Devm} {j : Except (EvmError × Devm) (Nat × Devm)}
    (h : Except.OkOn (fun r : Nat × Devm => Devm.AccGrow devm r.2) j) :
    Step.AccGrow devm (Step.ofJump j) := by
  cases j with
  | error e => exact trivial
  | ok r => exact h r rfl

theorem Step.AccGrow.toStep {devm : Devm} {pc : Nat} {s : XStep}
    (h : XStep.AccGrow devm s) : Step.AccGrow devm (XStep.toStep pc s) := by
  cases s with
  | done ex => exact Step.AccGrow.ofExecution h
  | spawn f rsm => exact h

theorem Ninst.step_accGrow (evm : Evm) (n : Ninst)
    (hsg : evm.sta.benvStat.rules.stateGas = none) :
    Step.AccGrow evm.dyna (Ninst.step evm n) := by
  have h : Devm.AccGrow evm.dyna evm.dyna := Devm.AccGrow.rfl
  cases n with
  | reg r =>
    simp only [Ninst.step]
    exact Step.AccGrow.ofExecution (Rinst.runCore_accGrow _ _ _ r hsg)
  | exec x =>
    simp only [Ninst.step]
    exact Step.AccGrow.toStep (Xinst.step_accGrow _ _ x hsg)
  | push xs hxs =>
    simp only [Ninst.step]
    apply Step.AccGrow.ofExecution
    acc_walk evm.dyna
  | dupn imm =>
    simp only [Ninst.step]
    apply Step.AccGrow.ofExecution
    acc_walk evm.dyna
  | swapn imm =>
    simp only [Ninst.step]
    apply Step.AccGrow.ofExecution
    acc_walk evm.dyna
  | exchange imm =>
    simp only [Ninst.step]
    apply Step.AccGrow.ofExecution
    acc_walk evm.dyna

theorem Evm.step_accGrow (evm : Evm) (hsg : evm.sta.benvStat.rules.stateGas = none) :
    Step.AccGrow evm.dyna (Evm.step evm) := by
  unfold Evm.step
  split
  · exact trivial
  · exact Ninst.step_accGrow evm _ hsg
  · exact Step.AccGrow.ofJump (Jinst.runCore_accGrow _ _ _ _)
  · exact trivial

/-! ### Every entered frame of a warm derivation is warm -/

theorem Evm.step_cont_accGrow {pc : Nat} {sevm : Sevm} {pre d : Devm} {pc' : Nat}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' d) : Devm.AccGrow pre d := by
  have hg := Evm.step_accGrow ⟨pc, sevm, pre⟩ hsg
  rw [hstep] at hg
  exact hg

theorem Evm.step_resume_accGrow {pc : Nat} {sevm : Sevm} {pre : Devm} {f : Frame}
    {rsm : Resume} {pc' : Nat} (hsg : sevm.benvStat.rules.stateGas = none)
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {d : Devm}
    (hr : rsm.run r = .ok d) : Devm.AccGrow pre d := by
  have hg := Evm.step_accGrow ⟨pc, sevm, pre⟩ hsg
  rw [hstep] at hg
  exact hg.2 r d hr

/-- A child spawned by a step starts from a superset of the parent's accessed set. -/
theorem Evm.step_spawn_child_warm {pc : Nat} {sevm : Sevm} {pre : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc') (henter : f.enter = .run cevm) :
    Devm.AccGrow pre cevm.dyna ∧ cevm.sta.benvStat.rules.stateGas = none := by
  have hg := Evm.step_accGrow ⟨pc, sevm, pre⟩ hsg
  rw [hstep] at hg
  obtain ⟨x, _, hspawn, _⟩ := Evm.step_spawn_inv hstep
  have h1 : f.inner.benv.stat = sevm.benvStat := Xinst.step_spawn_benvStat hspawn
  have h2 := Frame.enter_run_benvStat henter
  refine ⟨?_, by rw [h2, h1]; exact hsg⟩
  obtain ⟨benv, _, rfl⟩ := Frame.enter_run_inv henter
  exact hg.1

/-- **Warmth of every entered frame.**  If an address is in the accessed set at the start of an
execution, it is in the accessed set at the start of every frame the execution enters,
including the frames inside subtrees that later revert. -/
theorem Exec.rawFrameRoots_warm (a : Adr) {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out)
    (hsg : sevm.benvStat.rules.stateGas = none) (ha : a ∈ pre.accessedAddresses) :
    ∀ root ∈ Exec.rawFrameRoots run, a ∈ root.devm.accessedAddresses := by
  revert hsg ha
  induction run with
  | halt hstep =>
      intro hsg ha root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact ha
  | cont hstep next ih =>
      intro hsg ha root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact ha
      · exact ih hsg (Evm.step_cont_accGrow hsg hstep a ha) root
          (by simp [Exec.rawFrameRoots, member])
  | doneErr hstep henter hresume =>
      intro hsg ha root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact ha
  | doneOk hstep henter hresume next ih =>
      intro hsg ha root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact ha
      · exact ih hsg (Evm.step_resume_accGrow hsg hstep hresume a ha) root
          (by simp [Exec.rawFrameRoots, member])
  | runErr hstep henter child hresume ih =>
      intro hsg ha root member
      obtain ⟨hgrow, hsgc⟩ := Evm.step_spawn_child_warm hsg hstep henter
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | rfl | member
      · exact ha
      · exact hgrow a ha
      · exact ih hsgc (hgrow a ha) root (by simp [Exec.rawFrameRoots, member])
  | runOk hstep henter child hresume next ihChild ihNext =>
      intro hsg ha root member
      obtain ⟨hgrow, hsgc⟩ := Evm.step_spawn_child_warm hsg hstep henter
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | rfl | member | member
      · exact ha
      · exact hgrow a ha
      · exact ihChild hsgc (hgrow a ha) root (by simp [Exec.rawFrameRoots, member])
      · exact ihNext hsg (Evm.step_resume_accGrow hsg hstep hresume a ha) root
          (by simp [Exec.rawFrameRoots, member])

end Blanc
