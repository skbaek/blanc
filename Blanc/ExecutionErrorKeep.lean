import Blanc.ExecutionWarmth

/-!
# A frame's settled-error field along its own execution

`Devm.error` is written only when a frame settles (`executeCode.handleError`, the message
settlement); no instruction, no resumption of a parent after a child and no halt touches it.  So
an execution that ends `.ok post` ends with the error field it started with
(`Exec.ok_error_eq`): a frame entered with `error = none` (`initDevm`) that executes to `.ok post`
settles cleanly, which is what a `CALL`/`STATICCALL` crossing into a callee known only by an
`Exec` derivation needs (`Ninst.runCompiled_call_zero_child`'s `cpost.error = none`).

The walk is `ExecutionWarmth.lean`'s, success-only, for the relation `Devm.ErrKeep pre d`
(`d.error = pre.error`) instead of accessed-set growth.

Nothing here mentions a contract.
-/

namespace Blanc

open Jaune

/-- The settled-error field is the reference machine's. -/
def Devm.ErrKeep (pre d : Devm) : Prop := d.error = pre.error

theorem Devm.ErrKeep.rfl {d : Devm} : Devm.ErrKeep d d := Eq.refl _

theorem Devm.ErrKeep.trans {a b c : Devm} (hab : Devm.ErrKeep a b) (hbc : Devm.ErrKeep b c) :
    Devm.ErrKeep a c := Eq.trans hbc hab

/-- Extend an error-keeping fact by a step that leaves the error field alone. -/
theorem Devm.ErrKeep.keep {pre d d' : Devm} (h : Devm.ErrKeep pre d)
    (e : d'.error = d.error) : Devm.ErrKeep pre d' := e.trans h

theorem liftMach_errKeep {α : Type} (core : Mach → Footprint.Outcome Mach α) {pre d : Devm}
    (h : Devm.ErrKeep pre d) :
    Except.OkOn (fun r : α × Devm => Devm.ErrKeep pre r.2) (liftMach core d) := by
  intro r hr
  unfold liftMach Footprint.liftOutcome at hr
  split at hr <;> cases hr
  exact h

theorem liftMachExecution_errKeep (core : Mach → Footprint.Outcome Mach Unit) {pre d : Devm}
    (h : Devm.ErrKeep pre d) :
    Except.OkOn (Devm.ErrKeep pre) (liftMachExecution core d) := by
  intro r hr
  unfold liftMachExecution Footprint.toExecution at hr
  split at hr
  · cases hr
  · rename_i x heq
    cases hr
    exact (liftMach_errKeep core h) _ heq

/-! ### Primitives -/

theorem Devm.pop_errKeep {pre d : Devm} (h : Devm.ErrKeep pre d) :
    Except.OkOn (fun r : B256 × Devm => Devm.ErrKeep pre r.2) (Devm.pop d) :=
  liftMach_errKeep _ h

theorem Devm.popToNat_errKeep {pre d : Devm} (h : Devm.ErrKeep pre d) :
    Except.OkOn (fun r : Nat × Devm => Devm.ErrKeep pre r.2) (Devm.popToNat d) :=
  liftMach_errKeep _ h

theorem Devm.popToAdr_errKeep {pre d : Devm} (h : Devm.ErrKeep pre d) :
    Except.OkOn (fun r : Adr × Devm => Devm.ErrKeep pre r.2) (Devm.popToAdr d) :=
  liftMach_errKeep _ h

theorem Devm.popN_errKeep {pre d : Devm} (n : Nat) (h : Devm.ErrKeep pre d) :
    Except.OkOn (fun r : List B256 × Devm => Devm.ErrKeep pre r.2) (Devm.popN d n) :=
  liftMach_errKeep _ h

theorem chargeGas_errKeep {pre d : Devm} (c : Nat) (h : Devm.ErrKeep pre d) :
    Except.OkOn (Devm.ErrKeep pre) (chargeGas c d) :=
  liftMachExecution_errKeep _ h

theorem Devm.push_errKeep {pre d : Devm} (x : B256) (h : Devm.ErrKeep pre d) :
    Except.OkOn (Devm.ErrKeep pre) (Devm.push x d) :=
  liftMachExecution_errKeep _ h

theorem pushItem_errKeep {pre d : Devm} (x : B256) (c : Nat) (h : Devm.ErrKeep pre d) :
    Except.OkOn (Devm.ErrKeep pre) (pushItem x c d) :=
  liftMachExecution_errKeep _ h

theorem applyUnary_errKeep {pre d : Devm} (f : B256 → B256) (c : Nat) (h : Devm.ErrKeep pre d) :
    Except.OkOn (Devm.ErrKeep pre) (applyUnary f c d) :=
  liftMachExecution_errKeep _ h

theorem applyBinary_errKeep {pre d : Devm} (f : B256 → B256 → B256) (c : Nat)
    (h : Devm.ErrKeep pre d) : Except.OkOn (Devm.ErrKeep pre) (applyBinary f c d) :=
  liftMachExecution_errKeep _ h

theorem applyTernary_errKeep {pre d : Devm} (f : B256 → B256 → B256 → B256) (c : Nat)
    (h : Devm.ErrKeep pre d) : Except.OkOn (Devm.ErrKeep pre) (applyTernary f c d) :=
  liftMachExecution_errKeep _ h

theorem Devm.pop_map_errKeep {pre d : Devm} (h : Devm.ErrKeep pre d) :
    Except.OkOn (Devm.ErrKeep pre) (Devm.pop d <&> Prod.snd) := by
  intro r hr
  have hx := Devm.pop_errKeep h
  cases hp : Devm.pop d with
  | error e => rw [hp] at hr; cases hr
  | ok a =>
    rw [hp] at hr
    cases hr
    exact hx a hp

theorem Devm.subBal_errKeep {pre d : Devm} (h : Devm.ErrKeep pre d) (a : Adr) (v : B256)
    (e : EvmError × Devm) :
    Except.OkOn (Devm.ErrKeep pre) ((d.subBal a v).toExcept e) := by
  intro r hr
  unfold Devm.subBal at hr
  cases hs : d.state.subBal a v with
  | none => simp only [Option.toExcept, hs, Option.bind_eq_bind, Option.bind_none,
    reduceCtorEq] at hr
  | some st =>
    simp only [hs, Option.toExcept] at hr
    cases hr
    exact h

theorem Devm.ErrKeep.warm {pre d : Devm} (h : Devm.ErrKeep pre d) (a : Adr) :
    Devm.ErrKeep pre (addAccessedAddress d a) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.balReadAccount {pre d : Devm} (h : Devm.ErrKeep pre d)
    (rules : ForkRules) (a : Adr) : Devm.ErrKeep pre (d.balReadAccount rules a) :=
  h.keep (by unfold Devm.balReadAccount; split <;> rfl)

theorem Devm.ErrKeep.balReadStorage {pre d : Devm} (h : Devm.ErrKeep pre d)
    (rules : ForkRules) (a : Adr) (k : B256) : Devm.ErrKeep pre (d.balReadStorage rules a k) :=
  h.keep (by unfold Devm.balReadStorage; split <;> rfl)

theorem Devm.ErrKeep.memWrite {pre d : Devm} (h : Devm.ErrKeep pre d) (i : Nat) (v : Bytes) :
    Devm.ErrKeep pre (d.memWrite i v) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.memRead {pre d : Devm} (h : Devm.ErrKeep pre d) (i n : Nat) :
    Devm.ErrKeep pre (d.memRead i n).2 := h.keep (Eq.refl _)

theorem Devm.ErrKeep.memExtends {pre d : Devm} (h : Devm.ErrKeep pre d) (ps : List (Nat × Nat)) :
    Devm.ErrKeep pre (d.memExtends ps) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.withStack {pre d : Devm} (h : Devm.ErrKeep pre d) (s : List B256) :
    Devm.ErrKeep pre (d.withStack s) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.withGasLeft {pre d : Devm} (h : Devm.ErrKeep pre d) (g : Nat) :
    Devm.ErrKeep pre (d.withGasLeft g) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.withReturnData {pre d : Devm} (h : Devm.ErrKeep pre d) (r : Bytes) :
    Devm.ErrKeep pre (d.withReturnData r) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.withOutput {pre d : Devm} (h : Devm.ErrKeep pre d) (r : Bytes) :
    Devm.ErrKeep pre (d.withOutput r) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.withRefundCounter {pre d : Devm} (h : Devm.ErrKeep pre d) (r : Int) :
    Devm.ErrKeep pre (d.withRefundCounter r) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.addLog {pre d : Devm} (h : Devm.ErrKeep pre d) (l : Log) :
    Devm.ErrKeep pre (d.addLog l) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.setStorVal {pre d : Devm} (h : Devm.ErrKeep pre d) (a : Adr) (k v : B256) :
    Devm.ErrKeep pre (d.setStorVal a k v) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.setTransVal {pre d : Devm} (h : Devm.ErrKeep pre d) (a : Adr) (k v : B256) :
    Devm.ErrKeep pre (d.setTransVal a k v) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.addStorageKey {pre d : Devm} (h : Devm.ErrKeep pre d) (a : Adr) (k : B256) :
    Devm.ErrKeep pre (addAccessedStorageKey d a k) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.incrNonce {pre d : Devm} (h : Devm.ErrKeep pre d) (a : Adr) :
    Devm.ErrKeep pre (d.incrNonce a) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.addBal {pre d : Devm} (h : Devm.ErrKeep pre d) (a : Adr) (v : B256) :
    Devm.ErrKeep pre (d.addBal a v) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.setBal {pre d : Devm} (h : Devm.ErrKeep pre d) (a : Adr) (v : B256) :
    Devm.ErrKeep pre (d.setBal a v) := h.keep (Eq.refl _)

theorem Devm.ErrKeep.addAccountToDelete {pre d : Devm} (h : Devm.ErrKeep pre d) (a : Adr) :
    Devm.ErrKeep pre (addAccountToDelete d a) := h.keep (Eq.refl _)

/-- A failed child is dropped without touching the parent's error field. -/
theorem Devm.ErrKeep.childOnError {pre d : Devm} (h : Devm.ErrKeep pre d) (child : Devm)
    (rd : Bytes) : Devm.ErrKeep pre (incorporateChildOnError d child rd) := h.keep (Eq.refl _)

/-- A successful child is incorporated without touching the parent's error field. -/
theorem Devm.ErrKeep.childOnSuccess {pre d : Devm} (h : Devm.ErrKeep pre d) (child : Devm)
    (rd : Bytes) : Devm.ErrKeep pre (incorporateChildOnSuccess d child rd) := h.keep (Eq.refl _)

/-- One step of proving that a machine built from a known one keeps its error field. -/
syntax "err_keep1" : tactic

/-- Prove the error field kept, from the hypotheses in scope. -/
macro "err_keep" : tactic => `(tactic| repeat err_keep1)

macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible assumption)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.balReadAccount)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.balReadStorage)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.warm)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.memWrite)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.memRead)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.memExtends)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.withStack)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.withGasLeft)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.withReturnData)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.withOutput)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.withRefundCounter)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.addLog)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.setStorVal)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.setTransVal)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.addStorageKey)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.incrNonce)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.addBal)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.setBal)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.addAccountToDelete)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.childOnError)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.childOnSuccess)

/-- Peel one bind of a success-only error-keeping goal against the reference machine `pre`. -/
macro "err_step " pre:term : tactic =>
  `(tactic| first
      | (with_reducible refine Except.OkOn.bind (P := fun _ : Unit => True) ?_ ?_
         · first
            | with_reducible exact Except.assert_okOn _ _
            | with_reducible exact assertDynamic_okOn _ _
            | with_reducible exact Except.OkOn.error
         intro _ _)
      | (with_reducible refine Except.OkOn.bind (P := fun r => Devm.ErrKeep $pre (Prod.snd r)) ?_ ?_
         · first
            | with_reducible exact Devm.pop_errKeep (by assumption)
            | with_reducible exact Devm.popToNat_errKeep (by assumption)
            | with_reducible exact Devm.popToAdr_errKeep (by assumption)
            | with_reducible exact Devm.popN_errKeep _ (by assumption)
         intro _ _)
      | (with_reducible refine Except.OkOn.bind (P := Devm.ErrKeep $pre) ?_ ?_
         · first
            | focus (with_reducible refine chargeGas_errKeep _ ?_; err_keep; done)
            | focus (with_reducible refine Devm.push_errKeep _ ?_; err_keep; done)
            | focus (with_reducible refine pushItem_errKeep _ _ ?_; err_keep; done)
            | focus (with_reducible refine applyUnary_errKeep _ _ ?_; err_keep; done)
            | focus (with_reducible refine applyBinary_errKeep _ _ ?_; err_keep; done)
            | focus (with_reducible refine applyTernary_errKeep _ _ ?_; err_keep; done)
            | with_reducible exact Devm.pop_map_errKeep (by assumption)
            | focus (with_reducible refine Devm.subBal_errKeep ?_ _ _ _; err_keep; done)
         intro _ _))

/-- Walk one arm of an instruction against the reference machine `pre`. -/
macro "err_walk " pre:term : tactic =>
  `(tactic| repeat (first
      | with_reducible exact Except.OkOn.error
      | split
      | (with_reducible refine Except.OkOn.bind_ok ?_)
      | focus (with_reducible apply Except.OkOn.ok; err_keep; done)
      | focus (with_reducible apply Except.OkOn.pure; err_keep; done)
      | err_step $pre
      | focus (with_reducible refine chargeGas_errKeep _ ?_; err_keep; done)
      | focus (with_reducible refine Devm.push_errKeep _ ?_; err_keep; done)
      | focus (with_reducible refine pushItem_errKeep _ _ ?_; err_keep; done)
      | focus (with_reducible refine applyUnary_errKeep _ _ ?_; err_keep; done)
      | focus (with_reducible refine applyBinary_errKeep _ _ ?_; err_keep; done)
      | focus (with_reducible refine applyTernary_errKeep _ _ ?_; err_keep; done)))

theorem liftMachMetaExecution_errKeep (core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit)
    {pre d : Devm} (h : Devm.ErrKeep pre d)
    (hcore : ∀ m v m' v', core m v = .ok ((), (m', v')) → v'.error = v.error) :
    Except.OkOn (Devm.ErrKeep pre) (liftMachMetaExecution core d) := by
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
      exact (hcore _ _ _ _ heq).trans h

theorem Rinst.balanceCore_err (rules : ForkRules) (world : World) (mach : Mach) (view : Meta)
    (m' : Mach) (v' : Meta)
    (h : Rinst.balanceCore rules world mach view = .ok ((), (m', v'))) :
    v'.error = view.error := by
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
        split <;> (try split) <;> rfl

theorem Rinst.balance_errKeep (rules : ForkRules) (devm : Devm) :
    Except.OkOn (Devm.ErrKeep devm) (liftMachMetaWorldExecution (Rinst.balanceCore rules) devm) :=
  liftMachMetaExecution_errKeep _ Devm.ErrKeep.rfl
    (fun _ _ _ _ h => Rinst.balanceCore_err _ _ _ _ _ _ h)

theorem Rinst.runCore_errKeep (pc : Nat) (sevm : Sevm) (devm : Devm) (r : Rinst)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    Except.OkOn (Devm.ErrKeep devm) (Rinst.runCore pc devm sevm r) := by
  have h : Devm.ErrKeep devm devm := Devm.ErrKeep.rfl
  cases r <;> simp only [Rinst.runCore, hsg]
  case balance => exact Rinst.balance_errKeep _ _
  all_goals err_walk devm

theorem Jinst.runCore_errKeep (pc : Nat) (sevm : Sevm) (devm : Devm) (j : Jinst) :
    Except.OkOn (fun r : Nat × Devm => Devm.ErrKeep devm r.2) (Jinst.runCore pc devm sevm j) := by
  have h : Devm.ErrKeep devm devm := Devm.ErrKeep.rfl
  cases j <;> simp only [Jinst.runCore]
  all_goals err_walk devm

theorem Linst.run_errKeep (sevm : Sevm) (devm : Devm) (l : Linst)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    Except.OkOn (Devm.ErrKeep devm) (Linst.run sevm devm l) := by
  have h : Devm.ErrKeep devm devm := Devm.ErrKeep.rfl
  cases l <;> simp only [Linst.run, hsg]
  all_goals err_walk devm

/-! ### Spawned frames and their resumption -/

theorem Resume.run_call_errKeep (parent : Devm) (oi os : Nat)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    Except.OkOn (Devm.ErrKeep parent) ((Resume.call parent oi os).run r) := by
  have h : Devm.ErrKeep parent parent := Devm.ErrKeep.rfl
  simp only [Resume.run]
  refine Except.OkOn.bind (P := fun _ : Devm => True) (fun _ _ => trivial) ?_
  intro child _
  split
  · err_walk parent
  · err_walk parent

theorem Resume.run_create_errKeep (parent : Devm) (na : Adr)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    Except.OkOn (Devm.ErrKeep parent) ((Resume.create parent na).run r) := by
  have h : Devm.ErrKeep parent parent := Devm.ErrKeep.rfl
  simp only [Resume.run]
  refine Except.OkOn.bind (P := fun _ : Devm => True) (fun _ _ => trivial) ?_
  intro child _
  split
  · err_walk parent
  · err_walk parent

/-- The error field across a call-type step: a completed step keeps it; a spawn resumes the
parent keeping it. -/
def XStep.ErrKeep (devm : Devm) : XStep → Prop
  | .done ex => Except.OkOn (Devm.ErrKeep devm) ex
  | .spawn _ rsm => ∀ r, Except.OkOn (Devm.ErrKeep devm) (rsm.run r)

theorem XStep.ErrKeep.done_ok {devm d : Devm} (h : Devm.ErrKeep devm d) :
    XStep.ErrKeep devm (.done (.ok d)) :=
  Except.OkOn.ok h

theorem XStep.ErrKeep.ofExcept {devm : Devm} {e : Except (EvmError × Devm) XStep}
    (h : Except.OkOn (XStep.ErrKeep devm) e) : XStep.ErrKeep devm (XStep.ofExcept e) := by
  cases e with
  | error e => exact Except.OkOn.error
  | ok st => exact h st rfl

theorem XStep.ErrKeep.spawn_call {devm evm1 : Devm} (h : Devm.ErrKeep devm evm1)
    (f : Frame) (oi os : Nat) : XStep.ErrKeep devm (.spawn f (.call evm1 oi os)) :=
  fun r => Except.OkOn.mono (Resume.run_call_errKeep evm1 oi os r)
    (fun _ hx => Devm.ErrKeep.trans h hx)

theorem XStep.ErrKeep.spawn_create {devm d : Devm} (h : Devm.ErrKeep devm d)
    (f : Frame) (na : Adr) : XStep.ErrKeep devm (.spawn f (.create d na)) :=
  fun r => Except.OkOn.mono (Resume.run_create_errKeep d na r)
    (fun _ hx => Devm.ErrKeep.trans h hx)

theorem Devm.ErrKeep.accessDelegation {pre d : Devm} (h : Devm.ErrKeep pre d) (adr : Adr) :
    Devm.ErrKeep pre (Jaune.accessDelegation d adr).2.2.2.2 := by
  unfold Jaune.accessDelegation
  dsimp only
  split
  · exact h.warm _
  · exact h

theorem Devm.ErrKeep.gasAccessDelegation {pre d : Devm} (h : Devm.ErrKeep pre d)
    (gas : GasSchedule) (adr : Adr) :
    Devm.ErrKeep pre (gas.accessDelegation d adr).2.2.2.2 := by
  unfold GasSchedule.accessDelegation
  dsimp only
  split
  · exact h.warm _
  · exact h

macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply XStep.ErrKeep.done_ok)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply XStep.ErrKeep.spawn_call)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply XStep.ErrKeep.spawn_create)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.accessDelegation)
macro_rules
  | `(tactic| err_keep1) => `(tactic| with_reducible apply Devm.ErrKeep.gasAccessDelegation)

theorem genericCall.step_errKeep {devm d : Devm} (h : Devm.ErrKeep devm d)
    (sevm : Sevm) (gas : Nat) (value : B256) (caller target codeAddress : Adr)
    (stv isSt : Bool) (ii isz oi osz : Nat) (code : ByteArray) (dp : Bool) :
    XStep.ErrKeep devm
      (genericCall.step sevm d gas value caller target codeAddress stv isSt ii isz oi osz code
        dp) := by
  unfold genericCall.step
  dsimp only
  split
  · with_reducible apply XStep.ErrKeep.ofExcept
    err_walk devm
  · err_keep

theorem genericCreate.step_errKeep {devm d : Devm} (h : Devm.ErrKeep devm d)
    (sevm : Sevm) (endowment : B256) (newAddress : Adr) (mi ms : Nat) :
    XStep.ErrKeep devm (genericCreate.step sevm d endowment newAddress mi ms) := by
  unfold genericCreate.step
  dsimp only
  with_reducible apply XStep.ErrKeep.ofExcept
  err_walk devm

macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply genericCall.step_errKeep)
macro_rules | `(tactic| err_keep1) => `(tactic| with_reducible apply genericCreate.step_errKeep)

theorem Xinst.step_errKeep (sevm : Sevm) (devm : Devm) (x : Xinst)
    (hsg : sevm.benvStat.rules.stateGas = none) :
    XStep.ErrKeep devm (Xinst.step sevm devm x) := by
  have h : Devm.ErrKeep devm devm := Devm.ErrKeep.rfl
  cases x <;> simp only [Xinst.step, hsg]
  all_goals with_reducible apply XStep.ErrKeep.ofExcept
  all_goals err_walk devm

/-! ### One interpreter step -/

/-- The error field across one interpreter step, success-only. -/
def Step.ErrKeep (devm : Devm) : Step → Prop
  | .halt ex => Except.OkOn (Devm.ErrKeep devm) ex
  | .cont _ d => Devm.ErrKeep devm d
  | .spawn _ rsm _ => ∀ r, Except.OkOn (Devm.ErrKeep devm) (rsm.run r)

theorem Step.ErrKeep.ofExecution {devm : Devm} {pc : Nat} {e : Execution}
    (h : Except.OkOn (Devm.ErrKeep devm) e) : Step.ErrKeep devm (Step.ofExecution pc e) := by
  cases e with
  | error e => exact Except.OkOn.error
  | ok d => exact h d rfl

theorem Step.ErrKeep.ofJump {devm : Devm} {j : Except (EvmError × Devm) (Nat × Devm)}
    (h : Except.OkOn (fun r : Nat × Devm => Devm.ErrKeep devm r.2) j) :
    Step.ErrKeep devm (Step.ofJump j) := by
  cases j with
  | error e => exact Except.OkOn.error
  | ok r => exact h r rfl

theorem Step.ErrKeep.toStep {devm : Devm} {pc : Nat} {s : XStep}
    (h : XStep.ErrKeep devm s) : Step.ErrKeep devm (XStep.toStep pc s) := by
  cases s with
  | done ex => exact Step.ErrKeep.ofExecution h
  | spawn f rsm => exact h

theorem Ninst.step_errKeep (evm : Evm) (n : Ninst)
    (hsg : evm.sta.benvStat.rules.stateGas = none) :
    Step.ErrKeep evm.dyna (Ninst.step evm n) := by
  have h : Devm.ErrKeep evm.dyna evm.dyna := Devm.ErrKeep.rfl
  cases n with
  | reg r =>
    simp only [Ninst.step]
    exact Step.ErrKeep.ofExecution (Rinst.runCore_errKeep _ _ _ r hsg)
  | exec x =>
    simp only [Ninst.step]
    exact Step.ErrKeep.toStep (Xinst.step_errKeep _ _ x hsg)
  | push xs hxs =>
    simp only [Ninst.step]
    apply Step.ErrKeep.ofExecution
    err_walk evm.dyna
  | dupn imm =>
    simp only [Ninst.step]
    apply Step.ErrKeep.ofExecution
    err_walk evm.dyna
  | swapn imm =>
    simp only [Ninst.step]
    apply Step.ErrKeep.ofExecution
    err_walk evm.dyna
  | exchange imm =>
    simp only [Ninst.step]
    apply Step.ErrKeep.ofExecution
    err_walk evm.dyna

theorem Evm.step_errKeep (evm : Evm) (hsg : evm.sta.benvStat.rules.stateGas = none) :
    Step.ErrKeep evm.dyna (Evm.step evm) := by
  unfold Evm.step
  split
  · exact Except.OkOn.error
  · exact Ninst.step_errKeep evm _ hsg
  · exact Step.ErrKeep.ofJump (Jinst.runCore_errKeep _ _ _ _)
  · exact Linst.run_errKeep _ _ _ hsg

/-! ### A successful execution keeps its error field -/

/-- **A frame's execution that ends `.ok post` ends with the error field it started with.** -/
theorem Exec.ok_error_eq {pc : Nat} {sevm : Sevm} {pre post : Devm}
    (run : Exec pc sevm pre (.ok post)) (hsg : sevm.benvStat.rules.stateGas = none) :
    post.error = pre.error := by
  revert hsg
  generalize hout : (Except.ok post : Execution) = out at run
  induction run with
  | @halt p e d ex hstep =>
      intro hsg
      have hg := Evm.step_errKeep ⟨p, e, d⟩ hsg
      rw [hstep] at hg
      exact hg post hout.symm
  | @cont p e d p' d' ex hstep next ih =>
      intro hsg
      have hg := Evm.step_errKeep ⟨p, e, d⟩ hsg
      rw [hstep] at hg
      exact Eq.trans (ih hout hsg) hg
  | doneErr hstep henter hresume => intro _; cases hout
  | @doneOk p e d f rsm p' r d' ex hstep henter hresume next ih =>
      intro hsg
      have hg := Evm.step_errKeep ⟨p, e, d⟩ hsg
      rw [hstep] at hg
      exact Eq.trans (ih hout hsg) (hg _ _ hresume)
  | runErr hstep henter child hresume ih => intro _; cases hout
  | @runOk p e d f rsm p' cevm raw d' ex hstep henter child hresume next ihChild ihNext =>
      intro hsg
      have hg := Evm.step_errKeep ⟨p, e, d⟩ hsg
      rw [hstep] at hg
      exact Eq.trans (ihNext hout hsg) (hg _ _ hresume)

end Blanc
