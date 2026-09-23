-- RevertCause.lean : which step of a reverting compiled walk caused it, and
-- the exec-to-walk inversion for reverting frames.

import Blanc.Reverts
import Blanc.CompiledWalkInversion

namespace Blanc

open Jaune

/-- A gas-exact compiled walk that settles at `ex` and runs, on its way, at
least one `.next` instruction step satisfying `P`.  Rule for rule this is
`Func.RunCompiledTo` (`Blanc/Reverts.lean`); `here` designates the visited
step and continues with an ordinary walk. -/
inductive Func.RunCompiledToVisiting (P : Sevm → Devm → Ninst → Devm → Prop) :
    List Func → Sevm → Devm → Func → Execution → Prop
  | here :
    ∀ {fs sevm devm i devm' f ex},
      Ninst.RunCompiled sevm devm i devm' →
      P sevm devm i devm' →
      Func.RunCompiledTo fs sevm devm' f ex →
      Func.RunCompiledToVisiting P fs sevm devm (next i f) ex
  | next :
    ∀ {fs sevm devm i devm' f ex},
      Ninst.RunCompiled sevm devm i devm' →
      Func.RunCompiledToVisiting P fs sevm devm' f ex →
      Func.RunCompiledToVisiting P fs sevm devm (next i f) ex
  | zero :
    ∀ {fs sevm devm devm' f g ex},
      devm.stack.length < 1024 →
      Devm.PopBurnBy [0] (gVerylow + gHigh) devm devm' →
      Func.RunCompiledToVisiting P fs sevm devm' f ex →
      Func.RunCompiledToVisiting P fs sevm devm (branch f g) ex
  | succ :
    ∀ {fs sevm devm w devm' f g ex},
      w ≠ 0 →
      devm.stack.length < 1024 →
      Devm.PopBurnBy [w] (gVerylow + gHigh + gJumpdest) devm devm' →
      Func.RunCompiledToVisiting P fs sevm devm' g ex →
      Func.RunCompiledToVisiting P fs sevm devm (branch f g) ex
  | call :
    ∀ {fs sevm devm devm' k f ex},
      fs[k]? = some f →
      devm.stack.length < 1024 →
      Devm.BurnBy (gVerylow + gMid + gJumpdest) devm devm' →
      Func.RunCompiledToVisiting P fs sevm devm' f ex →
      Func.RunCompiledToVisiting P fs sevm devm (call k) ex

/-- The program-altitude visiting walk, entered at pc 0 exactly as
`Prog.RunCompiledTo` is. -/
def Prog.RunCompiledToVisiting (P : Sevm → Devm → Ninst → Devm → Prop)
    (sevm : Sevm) (devm : Devm) (p : Prog) (ex : Execution) : Prop :=
  ∃ mid, Devm.BurnBy gJumpdest devm mid ∧
    Func.RunCompiledToVisiting P (p.main :: p.aux) sevm mid p.main ex

/-- A visiting walk is a walk: forget the designation. -/
theorem Func.RunCompiledToVisiting.toRunCompiledTo
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func} {sevm : Sevm}
    {devm : Devm} {f : Func} {ex : Execution}
    (h : Func.RunCompiledToVisiting P fs sevm devm f ex) :
    Func.RunCompiledTo fs sevm devm f ex := by
  induction h with
  | here h_step _ h_tail => exact .next h_step h_tail
  | next h_step _ ih => exact .next h_step ih
  | zero h_room h_pop _ ih => exact .zero h_room h_pop ih
  | succ h_ne h_room h_pop _ ih => exact .succ h_ne h_room h_pop ih
  | call h_get h_room h_burn _ ih => exact .call h_get h_room h_burn ih

/-- A visiting walk really runs a `P`-step.  This is the anti-vacuity face of
the relation: a constructor that designated nothing would break this proof. -/
theorem Func.RunCompiledToVisiting.exists_step
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func} {sevm : Sevm}
    {devm : Devm} {f : Func} {ex : Execution}
    (h : Func.RunCompiledToVisiting P fs sevm devm f ex) :
    ∃ (stepPre : Devm) (instruction : Ninst) (stepPost : Devm),
      Ninst.RunCompiled sevm stepPre instruction stepPost ∧
        P sevm stepPre instruction stepPost := by
  induction h with
  | here h_step h_pred _ => exact ⟨_, _, _, h_step, h_pred⟩
  | next _ _ ih => exact ih
  | zero _ _ _ ih => exact ih
  | succ _ _ _ _ ih => exact ih
  | call _ _ _ _ ih => exact ih

/-- The program-altitude inclusion. -/
theorem Prog.RunCompiledToVisiting.toRunCompiledTo
    {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {devm : Devm}
    {p : Prog} {ex : Execution}
    (h : Prog.RunCompiledToVisiting P sevm devm p ex) :
    Prog.RunCompiledTo sevm devm p ex := by
  rcases h with ⟨mid, h_burn, h_run⟩
  exact ⟨mid, h_burn, h_run.toRunCompiledTo⟩

/-- A visiting walk of the deployed code is the frame's actual execution. -/
theorem Prog.RunCompiledToVisiting.exec_eq
    {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {pre : Devm}
    {p : Prog} {ex : Execution}
    (h : Prog.RunCompiledToVisiting P sevm pre p ex)
    (h_eq : some sevm.code.toList = p.compile) :
    exec ⟨0, sevm, pre⟩ = ex := by
  exact Prog.exec_of_runCompiledTo h.toRunCompiledTo h_eq

/-! ## G1: the exec-to-walk inversion for reverting frames

Jaune's `EvmError.revert` has exactly one producer, `Linst.run .revert`.  The
lemmas below discharge that fact, by tag, for every other way an `Exec`
derivation can end in an error: an `Rinst`, a `PUSH`, a jump, an `Xinst`
step, and a child frame's resumption. -/

/-! #### The tag predicate and its primitive facts

The pinned Jaune states the halt obligation as `HaltOut`/`MachHaltOut`, which
also tracks the state-gas meter.  The walk below needs only the tag half, so it
keeps the tag-only predicates and derives each primitive fact from Jaune's
`HaltOut` form. -/

/-- No branch of this outcome reports the `"Revert"` tag. -/
def NoRevertOut {α : Type} : Except (EvmError × Devm) α → Prop
  | .error p => p.1 ≠ .revert
  | .ok _ => True

/-- The `Mach`-level analogue, for the footprint-lifted primitives. -/
def MachNoRevert {α : Type} : Footprint.Outcome Mach α → Prop
  | .error q => q.1 ≠ .revert
  | .ok _ => True

theorem HaltOut.noRevertOut {α : Type} {proj : α → Devm} {s : StateGasMeter}
    {e : Except (EvmError × Devm) α} (h : HaltOut proj s e) : NoRevertOut e := by
  cases e with
  | error p => exact h.1
  | ok _ => trivial

theorem MachHaltOut.machNoRevert {α : Type} {s : StateGasMeter}
    {o : Footprint.Outcome Mach α} (h : MachHaltOut s o) : MachNoRevert o := by
  cases o with
  | error q => exact h.1
  | ok _ => trivial

theorem liftMach_noRevert {α : Type} {core : Mach → Footprint.Outcome Mach α}
    {devm : Devm} (h : MachNoRevert (core devm.mach)) :
    NoRevertOut (liftMach core devm) := by
  unfold liftMach Footprint.liftOutcome
  rcases hc : core devm.mach with ⟨err, m⟩ | ⟨v, m⟩ <;> rw [hc] at h
  · exact h
  · trivial

theorem liftMachExecution_noRevert {core : Mach → Footprint.Outcome Mach Unit}
    {devm : Devm} (h : MachNoRevert (core devm.mach)) :
    NoRevertOut (liftMachExecution core devm) := by
  unfold liftMachExecution Footprint.toExecution liftMach Footprint.liftOutcome
  rcases hc : core devm.mach with ⟨err, m⟩ | ⟨v, m⟩ <;> rw [hc] at h
  · exact h
  · trivial

theorem Mach.pop_noRevert (mach : Mach) : MachNoRevert mach.pop :=
  MachHaltOut.machNoRevert (Mach.pop_haltOut rfl)

theorem Mach.push_noRevert (x : B256) (mach : Mach) :
    MachNoRevert (Mach.push x mach) :=
  MachHaltOut.machNoRevert (Mach.push_haltOut rfl)

theorem Mach.chargeGas_noRevert (c : Nat) (mach : Mach) :
    MachNoRevert (Mach.chargeGas c mach) :=
  MachHaltOut.machNoRevert (Mach.chargeGas_haltOut rfl)

theorem Devm.pop_noRevert (devm : Devm) : NoRevertOut devm.pop :=
  HaltOut.noRevertOut (Devm.pop_haltOut rfl)

theorem Devm.popToNat_noRevert (devm : Devm) : NoRevertOut devm.popToNat :=
  HaltOut.noRevertOut (Devm.popToNat_haltOut rfl)

theorem Devm.popToAdr_noRevert (devm : Devm) : NoRevertOut devm.popToAdr :=
  HaltOut.noRevertOut (Devm.popToAdr_haltOut rfl)

theorem Devm.push_noRevert (x : B256) (devm : Devm) : NoRevertOut (devm.push x) :=
  HaltOut.noRevertOut (Devm.push_haltOut rfl)

theorem chargeGas_noRevert (c : Nat) (devm : Devm) :
    NoRevertOut (chargeGas c devm) :=
  HaltOut.noRevertOut (chargeGas_haltOut rfl)

theorem assert_noRevert {p : Prop} [Decidable p] {msg : EvmError} {devm : Devm}
    (h : msg ≠ .revert) :
    NoRevertOut (Except.assert p (⟨msg, devm⟩ : EvmError × Devm)) :=
  HaltOut.noRevertOut (assert_haltOut h rfl)

theorem assertDynamic_noRevert (sevm : Sevm) (devm : Devm) :
    NoRevertOut (assertDynamic sevm devm) :=
  HaltOut.noRevertOut (assertDynamic_haltOut sevm rfl)

/-- A finished `Xinst` step never reports the `"Revert"` tag: the tag half of
Jaune's `Xinst.step_halt`, taken at the step's own meter and measure. -/
theorem Xinst.step_done_noRevert (sevm : Sevm) (devm : Devm) (x : Xinst)
    (y : Execution) (h : Xinst.step sevm devm x = .done y) : NoRevertOut y := by
  have hh := Xinst.step_halt sevm devm x (s := devm.mach.stateGas)
    (n := devm.gasMeasure) rfl (Devm.spill_le_gasMeasure devm) (Nat.le_refl _)
  rw [h] at hh
  cases y with
  | error p => exact (hh p rfl).1
  | ok _ => trivial

theorem noRevertOut_bind {α β : Type} {e : Except (EvmError × Devm) α}
    {f : α → Except (EvmError × Devm) β}
    (he : NoRevertOut e) (hf : ∀ a, NoRevertOut (f a)) :
    NoRevertOut (e >>= f) := by
  cases e with
  | error p => exact he
  | ok a => exact hf a

theorem noRevertOut_toExcept {α : Type} {p : EvmError × Devm}
    (h : p.1 ≠ .revert) (o : Option α) : NoRevertOut (o.toExcept p) := by
  cases o
  · exact h
  · trivial

theorem noRevertOut_ok {α : Type} (a : α) :
    NoRevertOut (.ok a : Except (EvmError × Devm) α) := trivial

theorem noRevertOut_halt {α : Type} (r : ExceptionalHalt) (d : Devm) :
    NoRevertOut (.error (.halt r, d) : Except (EvmError × Devm) α) := by
  show EvmError.halt r ≠ .revert
  exact fun h => nomatch h

/-- The footprint-generic form of the tag obligation. -/
def OutcomeNoRevert {σ α : Type} : Footprint.Outcome σ α → Prop
  | .error q => q.1 ≠ .revert
  | .ok _ => True

theorem liftOutcome_noRevert {σ α : Type} {get : Devm → σ}
    {set : Devm → σ → Devm} {core : σ → Footprint.Outcome σ α} {devm : Devm}
    (h : OutcomeNoRevert (core (get devm))) :
    NoRevertOut (Footprint.liftOutcome get set core devm) := by
  unfold Footprint.liftOutcome
  rcases hc : core (get devm) with ⟨e, v⟩ | ⟨a, v⟩ <;> rw [hc] at h <;> try dsimp only
  · exact h
  · trivial

theorem toExecution_noRevert {o : Except (EvmError × Devm) (Unit × Devm)}
    (h : NoRevertOut o) : NoRevertOut (Footprint.toExecution o) := by
  unfold Footprint.toExecution
  rcases o with e | ⟨_, d⟩
  · exact h
  · trivial

theorem noRevertOut_mapRev {α β : Type} {e : Except (EvmError × Devm) α}
    (f : α → β) (h : NoRevertOut e) : NoRevertOut (e <&> f) := by
  cases e with
  | error p => exact h
  | ok a => trivial

theorem Mach.pushItem_noRevert (x : B256) (c : Nat) (mach : Mach) :
    MachNoRevert (Mach.pushItem x c mach) := by
  unfold Mach.pushItem
  have h := Mach.chargeGas_noRevert c mach
  rcases hc : Mach.chargeGas c mach with ⟨e, m⟩ | ⟨a, m⟩ <;> rw [hc] at h <;> try dsimp only
  · exact h
  · exact Mach.push_noRevert _ _

theorem Mach.applyUnary_noRevert (f : B256 → B256) (c : Nat) (mach : Mach) :
    MachNoRevert (Mach.applyUnary f c mach) := by
  unfold Mach.applyUnary
  have h := Mach.pop_noRevert mach
  rcases hc : mach.pop with ⟨e, m⟩ | ⟨a, m⟩ <;> rw [hc] at h <;> try dsimp only
  · exact h
  · exact Mach.pushItem_noRevert _ _ _

theorem Mach.applyBinary_noRevert (f : B256 → B256 → B256) (c : Nat)
    (mach : Mach) : MachNoRevert (Mach.applyBinary f c mach) := by
  unfold Mach.applyBinary
  have h := Mach.pop_noRevert mach
  rcases hc : mach.pop with ⟨e, m⟩ | ⟨a, m⟩ <;> rw [hc] at h <;> try dsimp only
  · exact h
  have h' := Mach.pop_noRevert m
  rcases hc' : m.pop with ⟨e', m'⟩ | ⟨a', m'⟩ <;> rw [hc'] at h' <;> try dsimp only
  · exact h'
  · exact Mach.pushItem_noRevert _ _ _

theorem Mach.applyTernary_noRevert (f : B256 → B256 → B256 → B256) (c : Nat)
    (mach : Mach) : MachNoRevert (Mach.applyTernary f c mach) := by
  unfold Mach.applyTernary
  have h := Mach.pop_noRevert mach
  rcases hc : mach.pop with ⟨e, m⟩ | ⟨a, m⟩ <;> rw [hc] at h <;> try dsimp only
  · exact h
  have h' := Mach.pop_noRevert m
  rcases hc' : m.pop with ⟨e', m'⟩ | ⟨a', m'⟩ <;> rw [hc'] at h' <;> try dsimp only
  · exact h'
  have h'' := Mach.pop_noRevert m'
  rcases hc'' : m'.pop with ⟨e'', m''⟩ | ⟨a'', m''⟩ <;> rw [hc''] at h'' <;> try dsimp only
  · exact h''
  · exact Mach.pushItem_noRevert _ _ _

theorem Mach.popN_noRevert (mach : Mach) (n : Nat) :
    MachNoRevert (mach.popN n) := by
  induction n generalizing mach with
  | zero => trivial
  | succ n ih =>
    unfold Mach.popN
    have h := Mach.pop_noRevert mach
    rcases hc : mach.pop with ⟨e, m⟩ | ⟨a, m⟩ <;> rw [hc] at h <;> try dsimp only
    · exact h
    have h' := ih m
    rcases hc' : m.popN n with ⟨e', m'⟩ | ⟨a', m'⟩ <;> rw [hc'] at h' <;> try dsimp only
    · exact h'
    · trivial

theorem pushItem_noRevert (x : B256) (c : Nat) (devm : Devm) :
    NoRevertOut (pushItem x c devm) :=
  liftMachExecution_noRevert (Mach.pushItem_noRevert x c devm.mach)

theorem applyUnary_noRevert (f : B256 → B256) (c : Nat) (devm : Devm) :
    NoRevertOut (applyUnary f c devm) :=
  liftMachExecution_noRevert (Mach.applyUnary_noRevert f c devm.mach)

theorem applyBinary_noRevert (f : B256 → B256 → B256) (c : Nat) (devm : Devm) :
    NoRevertOut (applyBinary f c devm) :=
  liftMachExecution_noRevert (Mach.applyBinary_noRevert f c devm.mach)

theorem applyTernary_noRevert (f : B256 → B256 → B256 → B256) (c : Nat)
    (devm : Devm) : NoRevertOut (applyTernary f c devm) :=
  liftMachExecution_noRevert (Mach.applyTernary_noRevert f c devm.mach)

theorem Devm.popN_noRevert (devm : Devm) (n : Nat) :
    NoRevertOut (devm.popN n) :=
  liftMach_noRevert (Mach.popN_noRevert devm.mach n)

theorem Rinst.balanceCore_noRevert (rules : ForkRules) (world : World)
    (mach : Mach) (view : Meta) :
    OutcomeNoRevert (Rinst.balanceCore rules world mach view) := by
  unfold Rinst.balanceCore
  have h := Mach.pop_noRevert mach
  rcases hc : mach.pop with ⟨e, m⟩ | ⟨x, m⟩ <;> rw [hc] at h <;> try dsimp only
  · exact h
  generalize (if x.toAdr ∈ view.accessedAddresses then gasWarmAccess
    else rules.gas.coldAccountAccess) = cost
  have h' := Mach.chargeGas_noRevert cost m
  rcases hc' : Mach.chargeGas cost m with ⟨e', m'⟩ | ⟨a', m'⟩ <;> rw [hc'] at h' <;> try dsimp only
  · exact h'
  have h'' := Mach.push_noRevert ((world.state.get x.toAdr).bal) m'
  rcases hc'' : Mach.push ((world.state.get x.toAdr).bal) m' with
    ⟨e'', m''⟩ | ⟨a'', m''⟩ <;> rw [hc''] at h'' <;> try dsimp only
  · exact h''
  · trivial

theorem balance_noRevert (rules : ForkRules) (devm : Devm) :
    NoRevertOut (liftMachMetaWorldExecution (Rinst.balanceCore rules) devm) :=
  toExecution_noRevert (liftOutcome_noRevert (Rinst.balanceCore_noRevert _ _ _ _))

theorem HaltLe.noRevertOut {α : Type} {n : Nat} {P : α → Prop}
    {e : Except (EvmError × Devm) α} (h : HaltLe n P e) : NoRevertOut e := by
  cases e with
  | error p => exact h.1
  | ok _ => trivial

/-- A state-gas charge halts only out of gas, never with the revert tag. -/
theorem chargeStateGas_noRevert (amount : Nat) (devm : Devm) :
    NoRevertOut (chargeStateGas amount devm) :=
  HaltLe.noRevertOut (chargeStateGas_haltLe amount (Nat.le_refl devm.gasMeasure))

theorem Rinst.runCore_noRevert (pc : Nat) (devm : Devm) (sevm : Sevm)
    (r : Rinst) : NoRevertOut (Rinst.runCore pc devm sevm r) := by
  cases r <;> simp only [Rinst.runCore]
  all_goals
    repeat' (first
      | with_reducible exact pushItem_noRevert _ _ _
      | with_reducible exact applyUnary_noRevert _ _ _
      | with_reducible exact applyBinary_noRevert _ _ _
      | with_reducible exact applyTernary_noRevert _ _ _
      | with_reducible exact balance_noRevert _ _
      | with_reducible exact chargeStateGas_noRevert _ _
      | with_reducible exact chargeGas_noRevert _ _
      | with_reducible exact Devm.push_noRevert _ _
      | with_reducible exact Devm.pop_noRevert _
      | with_reducible exact Devm.popToNat_noRevert _
      | with_reducible exact Devm.popToAdr_noRevert _
      | with_reducible exact Devm.popN_noRevert _ _
      | with_reducible exact noRevertOut_mapRev _ (Devm.pop_noRevert _)
      | with_reducible exact assertDynamic_noRevert _ _
      | with_reducible exact noRevertOut_ok _
      | with_reducible exact noRevertOut_halt _ _
      | with_reducible exact assert_noRevert (fun h => nomatch h)
      | (with_reducible refine noRevertOut_bind ?_ ?_)
      | (rintro ⟨_, _⟩)
      | intro _
      | split)

theorem Jinst.runCore_noRevert (pc : Nat) (devm : Devm) (sevm : Sevm)
    (j : Jinst) : NoRevertOut (Jinst.runCore pc devm sevm j) := by
  cases j <;> simp only [Jinst.runCore]
  all_goals
    repeat' (first
      | with_reducible exact chargeGas_noRevert _ _
      | with_reducible exact Devm.pop_noRevert _
      | with_reducible exact noRevertOut_ok _
      | with_reducible exact assert_noRevert (fun h => nomatch h)
      | (with_reducible refine noRevertOut_bind ?_ ?_)
      | (rintro ⟨_, _⟩)
      | intro _
      | split)

/-- A settled child result that carries no `"Revert"` tag on its error
channel. -/
def SettledNoRevert : Except (EvmError × State × AdrSet × Tra) Devm → Prop
  | .error p => p.1 ≠ .revert
  | .ok _ => True

theorem handleError_noRevert (raw : Execution) :
    SettledNoRevert (executeCode.handleError raw) := by
  rcases raw with ⟨e, d⟩ | d
  · cases e <;> simp [executeCode.handleError, SettledNoRevert]
  · trivial

theorem handleErrorAmsterdam_noRevert (raw : Execution) :
    SettledNoRevert (executeCode.handleErrorAmsterdam raw) := by
  rcases raw with ⟨e, d⟩ | d
  · cases e <;> simp [executeCode.handleErrorAmsterdam, SettledNoRevert]
  · trivial

theorem handleErrorWith_noRevert (stateGas : Option StateGasRules)
    (raw : Execution) :
    SettledNoRevert (executeCode.handleErrorWith stateGas raw) := by
  cases stateGas
  · exact handleError_noRevert raw
  · exact handleErrorAmsterdam_noRevert raw

theorem processMessage.settle_noRevert (msg : Msg)
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : SettledNoRevert r) : SettledNoRevert (processMessage.settle msg r) := by
  rcases r with p | d
  · exact h
  · unfold processMessage.settle
    simp only [bind, Except.bind]
    split <;> trivial

theorem processCreateMessage.chargeCodeGas_noRevert (rules : ForkRules)
    (devm : Devm) :
    NoRevertOut (processCreateMessage.chargeCodeGas rules devm) := by
  unfold processCreateMessage.chargeCodeGas
  dsimp only
  split
  · split
    · exact noRevertOut_halt _ _
    · refine noRevertOut_bind (chargeGas_noRevert _ _) fun _ => ?_
      split
      · exact noRevertOut_halt _ _
      · trivial
  · split
    · exact noRevertOut_halt _ _
    · split
      · exact noRevertOut_halt _ _
      · exact noRevertOut_bind (chargeGas_noRevert _ _) fun _ =>
          chargeStateGas_noRevert _ _

theorem processCreateMessage.settle_noRevert (msg : Msg)
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : SettledNoRevert r) :
    SettledNoRevert (processCreateMessage.settle msg r) := by
  rcases r with p | d
  · exact h
  · unfold processCreateMessage.settle
    simp only [bind, Except.bind]
    split
    · have hc := processCreateMessage.chargeCodeGas_noRevert
        msg.benv.stat.rules d
      split <;> rename_i heq <;> rw [heq] at hc <;>
        simp_all [SettledNoRevert, NoRevertOut]
    · trivial

theorem Frame.settleMsg_noRevert (f : Frame)
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : SettledNoRevert r) : SettledNoRevert (f.settleMsg r) := by
  unfold Frame.settleMsg
  have h' := processMessage.settle_noRevert f.inner h
  split
  · exact processCreateMessage.settle_noRevert f.outer h'
  · exact h'

theorem Frame.settle_noRevert (f : Frame) (raw : Execution) :
    SettledNoRevert (f.settle raw) :=
  Frame.settleMsg_noRevert f (handleErrorWith_noRevert _ raw)

theorem Msg.benvAfterTransfer_noRevert (msg : Msg) {e}
    (h : msg.benvAfterTransfer = .error e) : e.1 ≠ .revert := by
  unfold Msg.benvAfterTransfer at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h
    · rename_i heq
      unfold Option.toExcept at heq
      split at heq <;> cases heq
      cases h
      exact fun h => nomatch h
    · cases h
  · cases h

theorem Frame.enter_done_noRevert {f : Frame} {r}
    (h : f.enter = .done r) : SettledNoRevert r := by
  unfold Frame.enter at h
  split at h
  · rename_i e he
    cases h
    exact Frame.settleMsg_noRevert f (Msg.benvAfterTransfer_noRevert _ he)
  · split at h
    · cases h
    · cases h
      exact Frame.settle_noRevert _ _

theorem liftToExecution_noRevert (devm : Devm)
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : SettledNoRevert r) : NoRevertOut (liftToExecution devm r) := by
  rcases r with ⟨e, st, ac, tra⟩ | d
  · exact h
  · trivial

theorem Resume.run_noRevert (rsm : Resume)
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : SettledNoRevert r) : NoRevertOut (rsm.run r) := by
  cases rsm with
  | create parent newAddress =>
    refine noRevertOut_bind (liftToExecution_noRevert parent h) fun child => ?_
    split
    · exact Devm.push_noRevert _ _
    · exact Devm.push_noRevert _ _
  | call parent outputIndex outputSize =>
    refine noRevertOut_bind (liftToExecution_noRevert parent h) fun child => ?_
    split
    · exact noRevertOut_bind (Devm.push_noRevert _ _) fun _ => trivial
    · exact noRevertOut_bind (Devm.push_noRevert _ _) fun _ => trivial
  | createAmsterdam state parent newAddress charged =>
    refine noRevertOut_bind (liftToExecution_noRevert parent h) fun child => ?_
    split
    · refine noRevertOut_bind (assert_noRevert (fun h => nomatch h)) fun _ => ?_
      exact Devm.push_noRevert _ _
    · refine noRevertOut_bind (assert_noRevert (fun h => nomatch h)) fun _ => ?_
      exact Devm.push_noRevert _ _
  | callAmsterdam state parent outputIndex outputSize charged =>
    refine noRevertOut_bind (liftToExecution_noRevert parent h) fun child => ?_
    split
    · refine noRevertOut_bind (assert_noRevert (fun h => nomatch h)) fun _ => ?_
      exact noRevertOut_bind (Devm.push_noRevert _ _) fun _ => trivial
    · refine noRevertOut_bind (assert_noRevert (fun h => nomatch h)) fun _ => ?_
      exact noRevertOut_bind (Devm.push_noRevert _ _) fun _ => trivial

theorem Resume.run_error_noRevert {rsm : Resume}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {e : EvmError × Devm}
    (h : SettledNoRevert r) (hr : rsm.run r = .error e) : e.1 ≠ .revert := by
  have hn := Resume.run_noRevert rsm h
  rw [hr] at hn
  exact hn

/-! ### The outcome class the inversion runs over -/

/-- An outcome that is a success or a revert: the class of frame results whose
every intermediate step succeeded. -/
def RevertOrOk (ex : Execution) : Prop :=
  ∀ e d, ex = .error (e, d) → e = .revert

theorem RevertOrOk.not_noRevert_error {ex : Execution} {p : EvmError × Devm}
    (h : RevertOrOk ex) (heq : ex = .error p) (hn : p.1 ≠ .revert) : False :=
  hn (h p.1 p.2 heq)

theorem Step.ofExecution_halt {pc : Nat} {x ex : Execution}
    (h : Step.ofExecution pc x = .halt ex) : ∃ p, x = .error p ∧ ex = .error p := by
  cases x with
  | error p => cases h; exact ⟨p, rfl, rfl⟩
  | ok d => cases h

theorem NoRevertOut.error_ne {α : Type} {x : Except (EvmError × Devm) α}
    {p : EvmError × Devm} (hn : NoRevertOut x) (hx : x = .error p) :
    p.1 ≠ .revert := by
  subst hx
  exact hn

/-- Every halting step of an ordinary instruction halts with an error that is
not a revert. -/
theorem Ninst.step_halt_noRevert {evm : Evm} {n : Ninst} {ex : Execution}
    (h : Ninst.step evm n = .halt ex) : ∃ p, ex = .error p ∧ p.1 ≠ .revert := by
  rcases n with r | x | ⟨xs, hxs⟩
  · rw [Ninst.step_reg] at h
    obtain ⟨p, hx, rfl⟩ := Step.ofExecution_halt h
    have hn := Rinst.runCore_noRevert evm.pc evm.dyna evm.sta r
    exact ⟨p, rfl, by
      have : NoRevertOut (Rinst.run evm r) := hn
      rw [hx] at this; exact this⟩
  · rw [Ninst.step_exec] at h
    have hn := Xinst.step_done_noRevert evm.sta evm.dyna x
    revert hn h
    generalize Xinst.step evm.sta evm.dyna x = s
    intro h hn
    cases s with
    | done y =>
      obtain ⟨p, hx, rfl⟩ := Step.ofExecution_halt h
      refine ⟨p, rfl, ?_⟩
      have : NoRevertOut y := hn y rfl
      rw [hx] at this; exact this
    | spawn f rsm => cases h
  · rw [Ninst.step_push] at h
    obtain ⟨p, hx, rfl⟩ := Step.ofExecution_halt h
    refine ⟨p, rfl, ?_⟩
    have := noRevertOut_bind (chargeGas_noRevert
      (if xs = [] then gBase else gVerylow) evm.dyna)
      (fun d => Devm.push_noRevert xs.toB256 d)
    rw [hx] at this; exact this
  -- EIP-8024 `DUPN`/`SWAPN`/`EXCHANGE`: every halt is a charge, decode, stack,
  -- or availability fault.
  all_goals
    simp only [Ninst.step] at h
    obtain ⟨p, hx, rfl⟩ := Step.ofExecution_halt h
    refine ⟨p, rfl, NoRevertOut.error_ne ?_ hx⟩
    repeat' (first
      | with_reducible exact chargeGas_noRevert _ _
      | with_reducible exact Devm.push_noRevert _ _
      | with_reducible exact noRevertOut_ok _
      | with_reducible exact noRevertOut_halt _ _
      | (with_reducible refine noRevertOut_bind ?_ ?_)
      | intro _
      | split)

/-! ### The `Exec` inversion steps, for a revert-or-success outcome

`Blanc/CommonCore.lean`'s `Ninst.run_of_at`/`Jinst.run_of_at` and
`Blanc/Compiled.lean`'s `pushAt_exact`, `jumpdest_at_exact`, `jump_at_exact`
and `jumpi_at_exact` are stated at `.ok post`.  Their siblings below take any
`RevertOrOk` outcome: the only new cases are the halting and child-error
ones, and each is refuted by the tag lemmas above. -/

theorem Ninst.run_of_at_revertOrOk {pc sevm pre n exn}
    (exc : Exec pc sevm pre exn) (hro : RevertOrOk exn)
    (nat : Ninst.At sevm.code pc n) :
    ∃ (inter : Devm) (exc' : Exec (pc + n.size) sevm inter exn),
      Ninst.Run sevm pre n inter ∧
      Exec.Deriv.Prec
        ⟨(pc + n.size), sevm, inter, exn, exc'⟩
        ⟨pc, sevm, pre, exn, exc⟩ := by
  have hstep : Evm.step ⟨pc, sevm, pre⟩ = Ninst.step ⟨pc, sevm, pre⟩ n :=
    Evm.step_next nat
  cases exc with
  | halt h =>
    obtain ⟨p, rfl, hn⟩ := Ninst.step_halt_noRevert (hstep.symm.trans h)
    exact (hro.not_noRevert_error rfl hn).elim
  | cont h exc' =>
    have hs := hstep.symm.trans h
    cases Ninst.step_cont_pc hs
    refine ⟨_, exc', ⟨.none, trivial, pc, ?_⟩, Exec.Deriv.Prec.cont h exc'⟩
    simp only [Ninst.StepRun, hs, Step.Run]
    exact ⟨trivial, trivial⟩
  | doneErr h henter hr =>
    exact (hro.not_noRevert_error rfl
      (Resume.run_error_noRevert (Frame.enter_done_noRevert henter) hr)).elim
  | doneOk h henter hr exc' =>
    have hs := hstep.symm.trans h
    cases Ninst.step_spawn_pc hs
    refine ⟨_, exc', ⟨.none, trivial, pc, ?_⟩,
      Exec.Deriv.Prec.doneOk h henter hr exc'⟩
    simp only [Ninst.StepRun, hs, Step.Run]
    exact ⟨_, RunFrame.of_done henter, hr.symm⟩
  | runErr h henter excChild hr =>
    exact (hro.not_noRevert_error rfl
      (Resume.run_error_noRevert (Frame.settle_noRevert _ _) hr)).elim
  | runOk h henter excChild hr exc' =>
    have hs := hstep.symm.trans h
    cases Ninst.step_spawn_pc hs
    refine ⟨_, exc', ⟨.some ⟨_, _⟩, ⟨excChild⟩, pc, ?_⟩,
      Exec.Deriv.Prec.runOkCont h henter excChild hr exc'⟩
    simp only [Ninst.StepRun, hs, Step.Run]
    exact ⟨_, RunFrame.of_run henter, hr.symm⟩

theorem Step.ofJump_halt {j : Except (EvmError × Devm) (Nat × Devm)}
    {ex : Execution} (h : Step.ofJump j = .halt ex) :
    ∃ p, j = .error p ∧ ex = .error p := by
  cases j with
  | error p => cases h; exact ⟨p, rfl, rfl⟩
  | ok v => cases h

theorem Jinst.run_of_at_revertOrOk {pc sevm pre j exn}
    (exc : Exec pc sevm pre exn) (hro : RevertOrOk exn)
    (jat : Jinst.At sevm.code pc j) :
    ∃ (pc' : Nat) (inter : Devm), ∃ (exc' : Exec pc' sevm inter exn),
      Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) ∧
      ⟨pc', sevm, inter, exn, exc'⟩ ≺ ⟨pc, sevm, pre, exn, exc⟩ := by
  have hstep : Evm.step ⟨pc, sevm, pre⟩ = Step.ofJump (j.run ⟨pc, sevm, pre⟩) :=
    Evm.step_jump jat
  cases exc with
  | halt h =>
    obtain ⟨p, hj, rfl⟩ := Step.ofJump_halt (hstep.symm.trans h)
    have hn : NoRevertOut (j.run ⟨pc, sevm, pre⟩) :=
      Jinst.runCore_noRevert pc pre sevm j
    rw [hj] at hn
    exact (hro.not_noRevert_error rfl hn).elim
  | cont h exc' =>
    exact ⟨_, _, exc', Step.ofJump_cont (hstep.symm.trans h),
      Exec.Deriv.Prec.cont h exc'⟩
  | doneErr h _ _ => cases Step.ofJump_ne_spawn (hstep.symm.trans h)
  | doneOk h _ _ _ => cases Step.ofJump_ne_spawn (hstep.symm.trans h)
  | runErr h _ _ _ => cases Step.ofJump_ne_spawn (hstep.symm.trans h)
  | runOk h _ _ _ _ => cases Step.ofJump_ne_spawn (hstep.symm.trans h)

theorem pushAt_exact_revertOrOk {pc sevm pre xs exn}
    (exc : Exec pc sevm pre exn) (hro : RevertOrOk exn)
    (h_at : PushAt sevm.code pc xs) (hne : xs ≠ []) :
    ∃ (inter : Devm) (exc' : Exec (pc + xs.length + 1) sevm inter exn),
      Devm.PushBurn [xs.toB256] pre inter ∧
      pre.stack.length < 1024 ∧
      pre.gasLeft = inter.gasLeft + gVerylow ∧
      ⟨pc + xs.length + 1, sevm, inter, exn, exc'⟩ ≺
        ⟨pc, sevm, pre, exn, exc⟩ := by
  rcases h_at with ⟨le, h_at⟩
  have hstep : Evm.step ⟨pc, sevm, pre⟩ =
      Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) := Evm.step_next h_at
  cases exc with
  | halt h =>
    obtain ⟨p, rfl, hn⟩ := Ninst.step_halt_noRevert (hstep.symm.trans h)
    exact (hro.not_noRevert_error rfl hn).elim
  | cont h exc' =>
    have hs := hstep.symm.trans h
    rw [Ninst.step_push, if_neg hne] at hs
    obtain ⟨hpc, hrun⟩ := Step.ofExecution_cont hs
    cases hpc
    rcases Devm.pushRun_exact hrun with ⟨hroom, hgas⟩
    exact ⟨_, exc', Devm.pushBurn_of_run hrun, hroom, hgas,
      Exec.Deriv.Prec.cont h exc'⟩
  | doneErr h _ _ =>
    have hs := hstep.symm.trans h
    rw [Ninst.step_push] at hs
    cases Step.ofExecution_ne_spawn hs
  | doneOk h _ _ _ =>
    have hs := hstep.symm.trans h
    rw [Ninst.step_push] at hs
    cases Step.ofExecution_ne_spawn hs
  | runErr h _ _ _ =>
    have hs := hstep.symm.trans h
    rw [Ninst.step_push] at hs
    cases Step.ofExecution_ne_spawn hs
  | runOk h _ _ _ _ =>
    have hs := hstep.symm.trans h
    rw [Ninst.step_push] at hs
    cases Step.ofExecution_ne_spawn hs

theorem jumpdest_at_exact_revertOrOk {pc sevm pre exn}
    (exc : Exec pc sevm pre exn) (hro : RevertOrOk exn)
    (jat : Jinst.At sevm.code pc .jumpdest) :
    ∃ (inter : Devm) (exc' : Exec (pc + 1) sevm inter exn),
      Devm.Burn pre inter ∧
      pre.gasLeft = inter.gasLeft + gJumpdest ∧
      ⟨pc + 1, sevm, inter, exn, exc'⟩ ≺ ⟨pc, sevm, pre, exn, exc⟩ := by
  rcases Jinst.run_of_at_revertOrOk exc hro jat with ⟨pc', inter, exc', run, prec⟩
  have hgas := Devm.gasLeft_of_jumpdest_run run
  rcases of_jumpdest_run run with ⟨eq_pc, burn⟩
  cases eq_pc
  exact ⟨inter, exc', burn, hgas, prec⟩

theorem jump_at_exact_revertOrOk {pc sevm pre exn}
    (exc : Exec pc sevm pre exn) (hro : RevertOrOk exn)
    (jat : Jinst.At sevm.code pc .jump) :
    ∃ (x : B256) (inter : Devm) (exc' : Exec x.toNat sevm inter exn),
      Devm.PopBurn [x] pre inter ∧
      pre.gasLeft = inter.gasLeft + gMid ∧
      jumpable sevm.code x.toNat = true ∧
      ⟨x.toNat, sevm, inter, exn, exc'⟩ ≺ ⟨pc, sevm, pre, exn, exc⟩ := by
  rcases Jinst.run_of_at_revertOrOk exc hro jat with ⟨pc', inter, exc', run, prec⟩
  have hgas := Devm.gasLeft_of_jump_run run
  rcases of_jump_run run with ⟨x, eq_pc, pb, jp⟩
  cases eq_pc
  exact ⟨x, inter, exc', pb, hgas, jp, prec⟩

theorem jumpi_at_exact_revertOrOk {pc sevm pre exn}
    (exc : Exec pc sevm pre exn) (hro : RevertOrOk exn)
    (jat : Jinst.At sevm.code pc .jumpi) :
    ( ∃ (x : B256) (inter : Devm) (exc' : Exec (pc + 1) sevm inter exn),
        Devm.PopBurn [x, 0] pre inter ∧
        pre.gasLeft = inter.gasLeft + gHigh ∧
        ⟨pc + 1, sevm, inter, exn, exc'⟩ ≺ ⟨pc, sevm, pre, exn, exc⟩ ) ∨
    ( ∃ (x y : B256) (inter : Devm) (exc' : Exec x.toNat sevm inter exn),
        Devm.PopBurn [x, y] pre inter ∧
        pre.gasLeft = inter.gasLeft + gHigh ∧
        jumpable sevm.code x.toNat = true ∧ y ≠ 0 ∧
        ⟨x.toNat, sevm, inter, exn, exc'⟩ ≺ ⟨pc, sevm, pre, exn, exc⟩ ) := by
  rcases Jinst.run_of_at_revertOrOk exc hro jat with ⟨pc', inter, exc', run, prec⟩
  have hgas := Devm.gasLeft_of_jumpi_run run
  rcases of_jumpi_run run with ⟨x, pc_eq, pb⟩ | ⟨x, y, pc_eq, pb, je, ne⟩
  · left; cases pc_eq; exact ⟨x, inter, exc', pb, hgas, prec⟩
  · right; cases pc_eq; exact ⟨x, y, inter, exc', pb, hgas, je, ne, prec⟩


/-! ### The inversion

`Blanc/Compiled.lean`'s `Func.runCompiled_of_exec_core` with the outcome
generalised from `.ok post` to any `RevertOrOk` outcome.  The recursion
(`Exec.Deriv.strongRec` over `Prec`), the `subcode` invariant and every
structural step are that proof's; each `.ok` step lemma is replaced by its
`RevertOrOk` sibling above, and `.last` closes with the outcome-generic
`Linst.run_of_at`.  The audited `.ok` theorem is left as it stands, the same
discipline `Blanc/Reverts.lean` states for its bridge. -/

theorem Func.runCompiledTo_of_exec_core (f : Func) (fs : List Func) :
    ∀ (pk : Exec.Deriv) (p : Func),
      Func.pcFree (f :: fs) p = true →
      some pk.sevm.code.toList = Prog.compile ⟨f, fs⟩ →
      subcode pk.sevm.code.toList pk.pc (Func.compile (table 0 (f :: fs)) pk.pc p) →
      RevertOrOk pk.exn →
      Func.RunCompiledTo (f :: fs) pk.sevm pk.devm p pk.exn := by
  apply Exec.Deriv.strongRec; intro pk ih p h_pcf h_eq sub hro
  rcases pk with ⟨pc, sevm, pre, exn, exc⟩
  simp only at hro ⊢
  match p with
  | .last l =>
    exact Func.RunCompiledTo.last <| Linst.run_of_at exc <| Linst.at_of_slice sub
  | .next n p =>
    rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩
    rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩; clear h_eq'
    rcases of_bind_eq_some h_rw with ⟨pbs, h_pbs, h⟩; clear h_rw
    rw [← of_pure_eq_some h] at h_slice
    clear h cd
    have h_at : Ninst.At sevm.code pc n := by
      apply Ninst.at_of_slice
      apply List.slice_prefix h_slice
    rcases Ninst.run_of_at_revertOrOk exc hro h_at with
      ⟨inter, exc', h_run, h_prec⟩
    rcases Func.pcFree_next h_pcf with ⟨h_n, h_p⟩
    apply Func.RunCompiledTo.next (Ninst.runCompiled_of_run h_n h_run)
    have quz :
      subcode sevm.code.toList (pc + n.size)
        (Func.compile (table 0 (f :: fs)) (pc + n.size) p) := by
      rw [h_pbs]
      simp only [subcode]
      rw [Ninst.size_eq_length_toBytes]
      apply List.slice_suffix h_slice
    exact ih ⟨pc + n.size, sevm, inter, exn, exc'⟩
      (Exec.Deriv.lt_of_prec h_prec) p h_p h_eq quz hro
  | .branch p q =>
    rcases subcode_compile_branch sub with
      ⟨loc, h_loc, pushAt, h_jumpi, h_scp, h_jumpdest, h_scq⟩
    rcases Func.pcFree_branch h_pcf with ⟨h_pp, h_pq⟩
    have h :
        ∃ (devm' : Devm) (exc' : Exec (pc + 3) sevm devm' exn),
          Devm.PushBurn [Nat.toB256 loc] pre devm' ∧
          pre.stack.length < 1024 ∧
          pre.gasLeft = devm'.gasLeft + gVerylow ∧
          ⟨pc + 3, sevm, devm', exn, exc'⟩ ≺ ⟨pc, sevm, pre, exn, exc⟩ := by
      simp at pushAt
      rcases pushAt_exact_revertOrOk exc hro ⟨_, pushAt⟩ (by simp) with
        ⟨s', cr', h, h_room, h_gas, h_prec⟩
      rw [List.toB256_pair _ h_loc] at h
      exact ⟨s', cr', h, h_room, h_gas, h_prec⟩
    rcases h with ⟨devm', exc', pushBurn, h_room, h_gas1, h_prec⟩
    rcases jumpi_at_exact_revertOrOk exc' hro h_jumpi with
        ⟨x, devm'', exc'', popBurn, h_gas2, prec⟩
      | ⟨x, y, devm'', exc'', popBurn, h_gas2, jumpable, ne, prec⟩ <;> clear h_jumpi
    · clear h_scq h_jumpdest
      have h_pop' : Devm.PopBurn [0] pre devm'' := by
        rcases (Devm.pushBurn_cons_popBurn_cons pushBurn popBurn).right
          with ⟨st, pushBurn', popBurn'⟩
        apply Devm.popBurn_of_burn_of_popBurn _ popBurn'
        apply Devm.burn_of_pushBurn_nil pushBurn'
      apply Func.RunCompiledTo.zero h_room
        (Devm.PopBurnBy.of_popBurn h_pop' (by omega))
      have h_lt :
          Exec.Deriv.lt ⟨pc + 4, sevm, devm'', exn, exc''⟩
            ⟨pc, sevm, pre, exn, exc⟩ := by
        refine' ⟨_, _, h_prec⟩
        apply Exec.Deriv.le.step _ prec
        apply Exec.Deriv.le.refl _
      exact ih ⟨pc + 4, sevm, devm'', exn, exc''⟩ h_lt p h_pp h_eq h_scp hro
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
      rcases jumpdest_at_exact_revertOrOk exc'' hro h_jumpdest with
        ⟨inter_jd, exc_jd, burn_jd, h_gas3, prec_jd⟩
      have run : Func.RunCompiledTo (f :: fs) sevm inter_jd q exn := by
        have h_lt :
            Exec.Deriv.lt ⟨x.toNat + 1, sevm, inter_jd, exn, exc_jd⟩
              ⟨pc, sevm, pre, exn, exc⟩ := by
          refine' ⟨_, _, h_prec⟩
          apply Exec.Deriv.le.step _ prec
          apply Exec.Deriv.le.step _ prec_jd
          apply Exec.Deriv.le.refl _
        rw [← hx] at h_scq
        exact ih ⟨x.toNat + 1, sevm, inter_jd, exn, exc_jd⟩ h_lt q h_pq h_eq h_scq hro
      exact Func.RunCompiledTo.succ ne h_room
        (Devm.PopBurnBy.of_popBurn
          (Devm.popBurn_of_popBurn_of_pop popBurn' burn_jd) (by omega)) run
  | .call k =>
    rcases subcode_compile_call sub with ⟨loc, p, h_get, h_loc, pushAt, h_jump⟩
    have h_get' : (f :: fs)[k]? = some p := by
      rw [← @Prog.get?_table 0 k (f :: fs), h_get]; rfl
    have hd :
      ∃ (devm' : Devm) (exc' : Exec (pc + 3) sevm devm' exn),
        Devm.PushBurn [loc.toB256] pre devm' ∧
        pre.stack.length < 1024 ∧
        pre.gasLeft = devm'.gasLeft + gVerylow ∧
        ⟨pc + 3, sevm, devm', exn, exc'⟩ ≺ ⟨pc, sevm, pre, exn, exc⟩ := by
      rcases pushAt_exact_revertOrOk exc hro pushAt (by simp) with
        ⟨inter, exc', h, h_room, h_gas, h_prec⟩
      rw [List.toB256_pair _ h_loc] at h
      exact ⟨inter, exc', h, h_room, h_gas, h_prec⟩
    rcases hd with ⟨devm', exc', h_push, h_room, h_gas1, h_prec⟩
    rcases jump_at_exact_revertOrOk exc' hro h_jump with
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
    rcases jumpdest_at_exact_revertOrOk exc'' hro h_jd with
      ⟨inter_jd, exc''', burn_jd, h_gas3, h_prec''⟩
    rw [h_rw] at hp
    have h_lt :
        Exec.Deriv.lt ⟨x.toNat + 1, sevm, inter_jd, exn, exc'''⟩
          ⟨pc, sevm, pre, exn, exc⟩ := by
      refine' ⟨_, _, h_prec⟩
      apply Exec.Deriv.le.step _ h_prec'
      apply Exec.Deriv.le.step _ h_prec''
      apply Exec.Deriv.le.refl _
    have run : Func.RunCompiledTo (f :: fs) sevm inter_jd p exn :=
      ih ⟨x.toNat + 1, sevm, inter_jd, exn, exc'''⟩ h_lt p
        (Func.pcFree_call h_pcf h_get') h_eq hp hro
    exact Func.RunCompiledTo.call h_get' h_room
      (Devm.BurnBy.of_burn (Devm.burn_trans h_burn burn_jd) (by omega)) run

/-- **Inversion for reverting frames.**  If the total interpreter settles the
compiled code of a pc-free program with `REVERT`, that frame has a gas-exact
compiled walk settling at the same outcome.  Only `Linst.run .revert` raises
`EvmError.revert`, so every step before the terminal one succeeded. -/
theorem Prog.runCompiledTo_of_exec_revert {sevm : Sevm} {pre d : Devm}
    {p : Prog}
    (h_pcf : Prog.pcFree p = true)
    (h_eq : some sevm.code.toList = p.compile)
    (h_exec : exec ⟨0, sevm, pre⟩ = .error (.revert, d)) :
    Prog.RunCompiledTo sevm pre p (.error (.revert, d)) := by
  have hro : RevertOrOk (.error (.revert, d)) := by
    intro e d' h; cases h; rfl
  obtain ⟨exc⟩ := (exec_iff_exec_eq 0 sevm pre _).mpr h_exec
  rcases @subcode_of_get?_eq_some p.main p.aux sevm.code 0 _ p.main h_eq rfl
    with ⟨h_at, h_sub⟩
  rcases jumpdest_at_exact_revertOrOk exc hro h_at with
    ⟨inter, exc', burn, h_gas, prec⟩
  refine ⟨inter, Devm.BurnBy.of_burn burn h_gas, ?_⟩
  exact Func.runCompiledTo_of_exec_core p.main p.aux
    ⟨1, sevm, inter, _, exc'⟩ p.main h_pcf h_eq h_sub hro

/-! ## Terminal inventory

A revert-cause statement speaks only about `EvmError.revert`.  A guard coded
as some other terminal (`STOP`, `SELFDESTRUCT`, a bare `REVERT` that halts on a
garbage operand) would escape it.  `Func.TerminalsReturnOrRevert` is the
structural companion: every terminal of the tree is `RETURN`, or is the
`REVERT` of a `Func.revert` node.  `.call` leaves are table indices, checked
where the table is. -/

/-- Every `.last` terminal of `f` reached through `.next` and `.branch` is
`RETURN`, or lies inside a `Func.revert` node. -/
def Func.TerminalsReturnOrRevert : Func → Prop
  | .last l => l = .return_
  | .next n f => Func.next n f = Func.revert ∨ Func.TerminalsReturnOrRevert f
  | .branch f g => Func.TerminalsReturnOrRevert f ∧ Func.TerminalsReturnOrRevert g
  | .call _ => True

/-- `PUSH0`, by shape. -/
def Ninst.isPush0 : Ninst → Bool
  | .push [] _ => true
  | _ => false

theorem Ninst.eq_pushB256_zero_of_isPush0 {n : Ninst}
    (h : Ninst.isPush0 n = true) :
    n = Ninst.pushB256 0 := by
  unfold Ninst.isPush0 at h
  split at h
  · rfl
  · cases h

/-- Recognise `Func.revert` (`PUSH0 PUSH0 REVERT`) by shape.  The terminal is
matched first, so a checker run over a whole program inspects push operands
only at `REVERT` sites. -/
def Func.isRevert : Func → Bool
  | .next n (.next m (.last .revert)) => Ninst.isPush0 n && Ninst.isPush0 m
  | _ => false

theorem Func.eq_revert_of_isRevert {f : Func} (h : f.isRevert = true) :
    f = Func.revert := by
  unfold Func.isRevert at h
  split at h
  · rw [Bool.and_eq_true] at h
    rw [Ninst.eq_pushB256_zero_of_isPush0 h.1,
      Ninst.eq_pushB256_zero_of_isPush0 h.2]
    rfl
  · cases h

/-- The executable checker for `Func.TerminalsReturnOrRevert`. -/
def Func.terminalsReturnOrRevert : Func → Bool
  | .last l => l == .return_
  | .next n f => (Func.next n f).isRevert || f.terminalsReturnOrRevert
  | .branch f g => f.terminalsReturnOrRevert && g.terminalsReturnOrRevert
  | .call _ => true

theorem Func.terminalsReturnOrRevert_sound :
    ∀ {f : Func}, f.terminalsReturnOrRevert = true → f.TerminalsReturnOrRevert
  | .last l, h => by
    simpa [Func.terminalsReturnOrRevert, Func.TerminalsReturnOrRevert] using h
  | .next n f, h => by
    simp only [Func.terminalsReturnOrRevert, Bool.or_eq_true] at h
    rcases h with h | h
    · exact Or.inl (Func.eq_revert_of_isRevert h)
    · exact Or.inr (Func.terminalsReturnOrRevert_sound h)
  | .branch f g, h => by
    simp only [Func.terminalsReturnOrRevert, Bool.and_eq_true] at h
    exact ⟨Func.terminalsReturnOrRevert_sound h.1,
      Func.terminalsReturnOrRevert_sound h.2⟩
  | .call _, _ => trivial

/-! ## Avoiding walks

`Func.RunCompiledToVisiting` is proved by contradiction: a walk that visits no
`P`-step is a `Func.RunCompiledToAvoiding` walk, whose inversions below keep the
fact at every step they peel.  An instruction step peeled from an avoiding walk
is itself not a `P`-step, and its tail is again avoiding.  Nothing here is
specific to a contract or to `P`. -/

/-- A gas-exact compiled walk that runs no `P`-step. -/
def Func.RunCompiledToAvoiding (P : Sevm → Devm → Ninst → Devm → Prop)
    (fs : List Func) (sevm : Sevm) (devm : Devm) (f : Func)
    (ex : Execution) : Prop :=
  Func.RunCompiledTo fs sevm devm f ex ∧
    ¬ Func.RunCompiledToVisiting P fs sevm devm f ex

namespace Func.RunCompiledToAvoiding

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func}
  {sevm : Sevm}

theorem next_inv {devm : Devm} {i : Ninst} {f : Func} {ex : Execution}
    (h : Func.RunCompiledToAvoiding P fs sevm devm (Func.next i f) ex) :
    ∃ mid, Ninst.RunCompiled sevm devm i mid ∧ ¬ P sevm devm i mid ∧
      Func.RunCompiledToAvoiding P fs sevm mid f ex := by
  obtain ⟨mid, hn, hrest⟩ := runCompiledTo_next_inv h.1
  exact ⟨mid, hn, fun hp => h.2 (.here hn hp hrest), hrest,
    fun hv => h.2 (.next hn hv)⟩

theorem branch_inv {devm : Devm} {f g : Func} {ex : Execution}
    (h : Func.RunCompiledToAvoiding P fs sevm devm (Func.branch f g) ex) :
    (∃ armPre, devm.stack = 0 :: armPre.stack ∧
        Devm.PopBurnBy [0] (gVerylow + gHigh) devm armPre ∧
        Func.RunCompiledToAvoiding P fs sevm armPre f ex) ∨
      (∃ (w : B256) (armPre : Devm), w ≠ 0 ∧
        devm.stack = w :: armPre.stack ∧
        Devm.PopBurnBy [w] (gVerylow + gHigh + gJumpdest) devm armPre ∧
        Func.RunCompiledToAvoiding P fs sevm armPre g ex) := by
  rcases h with ⟨walk, avoid⟩
  cases walk with
  | zero hroom hpop harm =>
    exact Or.inl ⟨_, hpop.stack, hpop, harm,
      fun hv => avoid (.zero hroom hpop hv)⟩
  | succ hne hroom hpop harm =>
    exact Or.inr ⟨_, _, hne, hpop.stack, hpop, harm,
      fun hv => avoid (.succ hne hroom hpop hv)⟩

theorem call_inv {devm : Devm} {k : Nat} {f : Func} {ex : Execution}
    (h_get : fs[k]? = some f)
    (h : Func.RunCompiledToAvoiding P fs sevm devm (Func.call k) ex) :
    ∃ mid, Devm.BurnBy (gVerylow + gMid + gJumpdest) devm mid ∧
      Func.RunCompiledToAvoiding P fs sevm mid f ex := by
  rcases h with ⟨walk, avoid⟩
  cases walk with
  | call hget hroom hburn hrest =>
    cases Option.some.inj (hget.symm.trans h_get)
    exact ⟨_, hburn, hrest, fun hv => avoid (.call hget hroom hburn hv)⟩

theorem prepend_inv {l : Line} {f : Func} {ex : Execution} :
    ∀ {devm : Devm}, Func.RunCompiledToAvoiding P fs sevm devm (l +++ f) ex →
      ∃ mid, Line.Run sevm devm l mid ∧
        Func.RunCompiledToAvoiding P fs sevm mid f ex := by
  induction l with
  | nil => exact fun h => ⟨_, Line.Run.nil, h⟩
  | cons i l ih =>
    intro devm h
    obtain ⟨mid, hn, -, hrest⟩ := next_inv h
    obtain ⟨fin, hline, hf⟩ := ih hrest
    exact ⟨fin, Line.Run.cons (Ninst.Run.of_runCompiled hn) hline, hf⟩

/-- A known zero stack head forces the fall-through arm. -/
theorem zero_branch_of_prefix {pre : Devm} {left right : Func}
    {ex : Execution} {xs : Stack}
    (hp : (0 : B256) :: xs <<+ pre.stack)
    (h : Func.RunCompiledToAvoiding P fs sevm pre (Func.branch left right) ex) :
    ∃ armPre, Devm.PopBurnBy [0] (gVerylow + gHigh) pre armPre ∧
      Func.RunCompiledToAvoiding P fs sevm armPre left ex ∧
      xs <<+ armPre.stack := by
  rcases branch_inv h with ⟨armPre, -, hpop, harm⟩ | ⟨w, armPre, hw, hstack, -, -⟩
  · exact ⟨armPre, hpop, harm,
      (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hp).2⟩
  · have pw : w :: ([] : Stack) <<+ pre.stack :=
      ⟨armPre.stack, by simpa [Split] using hstack⟩
    exact (hw (pref_head_unique hp pw).symm).elim

/-- A known nonzero stack head forces the jumped arm. -/
theorem succ_branch_of_prefix {pre : Devm} {left right : Func}
    {ex : Execution} {w : B256} {xs : Stack}
    (hw : w ≠ 0) (hp : w :: xs <<+ pre.stack)
    (h : Func.RunCompiledToAvoiding P fs sevm pre (Func.branch left right) ex) :
    ∃ armPre, Devm.PopBurnBy [w] (gVerylow + gHigh + gJumpdest) pre armPre ∧
      Func.RunCompiledToAvoiding P fs sevm armPre right ex ∧
      xs <<+ armPre.stack := by
  rcases branch_inv h with ⟨armPre, hstack, -, -⟩ |
      ⟨w', armPre, -, hstack, hpop, harm⟩
  · have pzero : (0 : B256) :: ([] : Stack) <<+ pre.stack :=
      ⟨armPre.stack, by simpa [Split] using hstack⟩
    exact (hw (pref_head_unique hp pzero)).elim
  · have pword : w' :: ([] : Stack) <<+ pre.stack :=
      ⟨armPre.stack, by simpa [Split] using hstack⟩
    obtain rfl : w' = w := pref_head_unique pword hp
    exact ⟨armPre, hpop, harm,
      (popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hp).2⟩

end Func.RunCompiledToAvoiding

/-- **Visiting by contradiction.**  A program walk whose every avoiding
continuation is impossible visits a `P`-step. -/
theorem Prog.RunCompiledToVisiting.of_not_avoiding
    {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {pre : Devm}
    {p : Prog} {ex : Execution}
    (walk : Prog.RunCompiledTo sevm pre p ex)
    (impossible : ∀ mid, Devm.BurnBy gJumpdest pre mid →
      Func.RunCompiledToAvoiding P (p.main :: p.aux) sevm mid p.main ex →
        False) :
    Prog.RunCompiledToVisiting P sevm pre p ex := by
  obtain ⟨mid, burn, run⟩ := walk
  by_contra notVisiting
  exact impossible mid burn ⟨run, fun visiting => notVisiting ⟨mid, burn, visiting⟩⟩

/-- With no step predicate at all, every walk avoids. -/
theorem Func.RunCompiledToAvoiding.of_bot {fs : List Func} {sevm : Sevm}
    {devm : Devm} {f : Func} {ex : Execution}
    (walk : Func.RunCompiledTo fs sevm devm f ex) :
    Func.RunCompiledToAvoiding (fun _ _ _ _ => False) fs sevm devm f ex :=
  ⟨walk, fun visiting => by
    obtain ⟨_, _, _, _, impossible⟩ := visiting.exists_step
    exact impossible⟩

/-! ## Revert-free continuations

A compiled walk can end in `REVERT` only at a `.last .revert`.  A body with no
such terminal, whose table calls land only in entries of the same kind, has no
reverting walk.  `STOP`, `RETURN` and `SELFDESTRUCT` raise only halts. -/

/-- No `.last .revert` in `f`, and every `.call` index is in `safe`. -/
def Func.revertFreeIn (safe : List Nat) : Func → Bool
  | .last l => l != .revert
  | .next _ f => Func.revertFreeIn safe f
  | .branch f g => Func.revertFreeIn safe f && Func.revertFreeIn safe g
  | .call k => safe.contains k

theorem Linst.run_noRevert_of_ne {sevm : Sevm} {devm : Devm} {l : Linst}
    (hl : l ≠ .revert) : NoRevertOut (Linst.run sevm devm l) := by
  cases l
  · trivial
  · simp only [Linst.run]
    repeat' (first
      | with_reducible exact chargeGas_noRevert _ _
      | with_reducible exact Devm.popToNat_noRevert _
      | with_reducible exact noRevertOut_ok _
      | (with_reducible refine noRevertOut_bind ?_ ?_)
      | (rintro ⟨_, _⟩))
  · exact (hl rfl).elim
  · simp only [Linst.run]
    repeat' (first
      | with_reducible exact chargeGas_noRevert _ _
      | with_reducible exact Devm.popToAdr_noRevert _
      | with_reducible exact assertDynamic_noRevert _ _
      | with_reducible exact chargeStateGas_noRevert _ _
      | with_reducible exact assert_noRevert (fun h => nomatch h)
      | with_reducible exact noRevertOut_ok _
      | with_reducible exact noRevertOut_halt _ _
      | with_reducible exact noRevertOut_toExcept (fun h => nomatch h) _
      | (with_reducible refine noRevertOut_bind ?_ ?_)
      | (rintro ⟨_, _⟩)
      | intro _
      | split)

theorem Linst.Run.not_revert_of_revertFreeIn {safe : List Nat} {sevm : Sevm}
    {devm : Devm} {l : Linst} {ex : Execution}
    (run : Linst.Run sevm devm l ex)
    (free : Func.revertFreeIn safe (.last l) = true) :
    ∀ d, ex ≠ .error (.revert, d) := by
  intro d hex
  have hl : l ≠ .revert := by
    simpa [Func.revertFreeIn] using free
  have hn := Linst.run_noRevert_of_ne (sevm := sevm) (devm := devm) hl
  have run' : Linst.run sevm devm l = ex := run
  rw [run', hex] at hn
  exact hn rfl

theorem Func.RunCompiledTo.not_revert_of_revertFreeIn {fs : List Func}
    {safe : List Nat}
    (tableSafe : ∀ k ∈ safe, ∀ g, fs[k]? = some g →
      Func.revertFreeIn safe g = true)
    {sevm : Sevm} {devm : Devm} {f : Func} {ex : Execution}
    (walk : Func.RunCompiledTo fs sevm devm f ex)
    (free : Func.revertFreeIn safe f = true) :
    ∀ d, ex ≠ .error (.revert, d) := by
  induction walk with
  | zero _ _ _ ih =>
    simp only [Func.revertFreeIn, Bool.and_eq_true] at free
    exact ih free.1
  | succ _ _ _ _ ih =>
    simp only [Func.revertFreeIn, Bool.and_eq_true] at free
    exact ih free.2
  | last hrun =>
    exact Linst.Run.not_revert_of_revertFreeIn hrun free
  | next _ _ ih =>
    exact ih (by simpa [Func.revertFreeIn] using free)
  | call hget _ _ _ ih =>
    exact ih (tableSafe _ (by simpa [Func.revertFreeIn] using free) _ hget)

/-! ## Entry through the shared wrappers, for avoiding walks

The shared nonpayable guard and the sorted binary dispatcher, peeled from an
avoiding walk at an arbitrary outcome.  They follow
`Func.RunCompiledTo.nonpayable_body_of_value_zero` and the vault family's
compiled dispatch reach step for step; the difference is that each peeled
tail is again avoiding, which is what lets a caller conclude a visiting walk
of the whole frame. -/

namespace Func.RunCompiledToAvoiding

open Jaune.Ninst Ninst

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func}
  {sevm : Sevm}

theorem nonpayable_body_of_value_zero {pre : Devm} {out : Execution}
    {body : Func} {tail : Stack}
    (valueZero : sevm.value = 0)
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre (nonpayable body) out) :
    ∃ bodyPre,
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out ∧
      tail <<+ bodyPre.stack ∧
      pre.state = bodyPre.state ∧ pre.memory = bodyPre.memory := by
  unfold nonpayable at run
  obtain ⟨afterValue, qvalue, -, run⟩ := next_inv run
  obtain ⟨testPre, qzero, -, branchRun⟩ := next_inv run
  have rvalue := Ninst.Run.of_runCompiled qvalue
  have rzero := Ninst.Run.of_runCompiled qzero
  have pValue := prefix_of_push (of_run_callvalue rvalue) hp
  have pTest := prefix_of_iszero rzero pValue
  have pOne : (1 : B256) :: tail <<+ testPre.stack := by
    simpa [valueZero, B256.eqCheck] using pTest
  obtain ⟨bodyPre, hpop, bodyRun, pBody⟩ :=
    succ_branch_of_prefix (by decide : (1 : B256) ≠ 0) pOne branchRun
  exact ⟨bodyPre, bodyRun, pBody,
    (Ninst.Hinv.inv (f := Devm.state) rvalue).trans
      ((Ninst.Hinv.inv (f := Devm.state) rzero).trans hpop.state),
    (Ninst.Hinv.inv (f := Devm.memory) rvalue).trans
      ((Ninst.Hinv.inv (f := Devm.memory) rzero).trans hpop.memory)⟩

private theorem reach_of_dispatchWith_leaf
    {sig w : B256} {f p : Func} {k : Nat}
    {s : Devm} {out : Execution} {tail : Stack}
    (hmember : (sig, f) ∈ [(w, p)])
    (hp : sig :: tail <<+ s.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm s
      (dispatchWith k (DispatchTree.leaf w p)) out) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧ s.state = bodyPre.state ∧
      s.memory = bodyPre.memory ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre f out := by
  have heq : (sig, f) = (w, p) := List.mem_singleton.mp hmember
  injection heq with hsig hbody
  subst hsig
  subst hbody
  change Func.RunCompiledToAvoiding P fs sevm s
    ([pushB256 sig, eq] +++ (f <?> .call k)) out at run
  obtain ⟨testPre, testRun, branchRun⟩ := prepend_inv run
  rcases Line.of_run_cons testRun with ⟨afterPush, qpush, testRun⟩
  rcases Line.of_run_cons testRun with ⟨afterEq, qeq, hnil⟩
  cases hnil
  have p1 : [sig, sig] ++ tail <<+ afterPush.stack := by
    have pushed := prefix_of_push (of_run_pushB256 qpush) hp
    simpa only [List.cons_append, List.nil_append] using pushed
  have p2 : (1 : B256) :: tail <<+ testPre.stack := by
    have compared := prefix_of_eq qeq p1
    simpa [B256.eqCheck] using compared
  obtain ⟨bodyPre, hpop, bodyRun, bodyStack⟩ :=
    succ_branch_of_prefix (by decide : (1 : B256) ≠ 0) p2 branchRun
  refine ⟨bodyPre, bodyStack, ?_, ?_, bodyRun⟩
  · exact (Line.of_inv Devm.state (by line_inv)
      (Line.Run.cons qpush (Line.Run.cons qeq Line.Run.nil))).trans hpop.state
  · exact (Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons qpush (Line.Run.cons qeq Line.Run.nil))).trans hpop.memory

private theorem reach_of_dispatchWith_build :
    ∀ {n : Nat} {entries : List (B256 × Func)} {sig : B256} {body : Func}
      {k : Nat} {s : Devm} {out : Execution} {tail : Stack},
      DispatchTree.sorted entries = true →
      entries.length ≤ n + 1 →
      (sig, body) ∈ entries →
      (sig :: tail <<+ s.stack) →
      Func.RunCompiledToAvoiding P fs sevm s
        (dispatchWith k (DispatchTree.build n entries)) out →
      ∃ bodyPre,
        tail <<+ bodyPre.stack ∧ s.state = bodyPre.state ∧
        s.memory = bodyPre.memory ∧
        Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  intro n
  induction n with
  | zero =>
    intro entries sig body k s out tail hsorted hlen hmember hp run
    rcases entries with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
    · cases hmember
    · exact reach_of_dispatchWith_leaf hmember hp run
    · exfalso
      simp only [List.length_cons] at hlen
      omega
  | succ n ih =>
    intro entries sig body k s out tail hsorted hlen hmember hp run
    rcases entries with _ | ⟨⟨w, p⟩, _ | ⟨y, ys⟩⟩
    · cases hmember
    · exact reach_of_dispatchWith_leaf hmember hp run
    · simp only [List.length_cons] at hlen
      let all := (w, p) :: y :: ys
      let split := (all.length + 1) / 2
      have htakeLen : (all.take split).length ≤ n + 1 := by
        simp only [all, split, List.length_take, List.length_cons]
        omega
      have hdropLen : (all.drop split).length ≤ n + 1 := by
        simp only [all, split, List.length_drop, List.length_cons]
        omega
      obtain ⟨z, zs, hdrop⟩ : ∃ z zs, all.drop split = z :: zs := by
        rcases hd : all.drop split with _ | ⟨z, zs⟩
        · exfalso
          have hl := congrArg List.length hd
          simp only [all, split, List.length_drop, List.length_cons,
            List.length_nil] at hl
          omega
        · exact ⟨z, zs, rfl⟩
      have hsortedSplit :
          DispatchTree.sorted (all.take split ++ all.drop split) = true := by
        rw [List.take_append_drop]
        exact hsorted
      have hsortedTake := DispatchTree.sorted_append_left hsortedSplit
      have hsortedDrop := DispatchTree.sorted_append_right hsortedSplit
      have hmemberSplit :
          (sig, body) ∈ all.take split ∨
            (sig, body) ∈ all.drop split := by
        apply List.mem_append.mp
        rw [List.take_append_drop]
        exact hmember
      change Func.RunCompiledToAvoiding P fs sevm s
        ([dup 0, pushB256 (leftmostFsig (DispatchTree.build n
            (all.drop split))), gt] +++
          (dispatchWith k (DispatchTree.build n (all.take split)) <?>
            dispatchWith k (DispatchTree.build n (all.drop split)))) out at run
      obtain ⟨branchPre, testRun, branchRun⟩ := prepend_inv run
      have ptest :
          (leftmostFsig (DispatchTree.build n (all.drop split)) >? sig) ::
            sig :: tail <<+ branchPre.stack := by
        generalize_line_prefix
      rw [hdrop, DispatchTree.leftmostFsig_build] at ptest
      have testState : s.state = branchPre.state :=
        Line.of_inv Devm.state (by line_inv) testRun
      have testMemory : s.memory = branchPre.memory :=
        Line.of_inv Devm.memory (by line_inv) testRun
      rcases branch_inv branchRun with hzero | hsucc
      · rcases hzero with ⟨rightPre, -, hpop, rightRun⟩
        have popped := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) ptest
        have hle : z.fst ≤ sig := by
          rw [← B256.not_lt]
          intro hlt
          have hgt : z.fst > sig := hlt
          rw [B256.gtCheck, if_pos hgt] at popped
          exact B256.zero_ne_one popped.1
        have hmemberDrop : (sig, body) ∈ all.drop split := by
          rcases hmemberSplit with hin | hin
          · exfalso
            have hz : z ∈ all.drop split := by
              rw [hdrop]
              exact List.mem_cons_self ..
            have hlt :=
              DispatchTree.fst_lt_of_sorted_append hsortedSplit hin hz
            have h1 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat hlt
            have h2 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat hle
            omega
          · exact hin
        rcases ih hsortedDrop hdropLen hmemberDrop popped.2 rightRun with
          ⟨bodyPre, bodyStack, bodyState, bodyMemory, bodyRun⟩
        exact ⟨bodyPre, bodyStack, testState.trans (hpop.state.trans bodyState),
          testMemory.trans (hpop.memory.trans bodyMemory), bodyRun⟩
      · rcases hsucc with ⟨flag, leftPre, hflag, -, hpop, leftRun⟩
        have popped := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) ptest
        have hlt : sig < z.fst := by
          by_contra hnlt
          rw [B256.gtCheck, if_neg (fun hgt => hnlt hgt)] at popped
          exact hflag popped.1
        have hmemberTake : (sig, body) ∈ all.take split := by
          rcases hmemberSplit with hin | hin
          · exact hin
          · exfalso
            rw [hdrop] at hin
            have hsortedZ : DispatchTree.sorted (z :: zs) = true := by
              rw [← hdrop]
              exact hsortedDrop
            have hle := DispatchTree.fst_le_of_sorted_mem hsortedZ hin
            have h1 : z.fst.toNat ≤ sig.toNat := B256.toNat_le_toNat hle
            have h2 : sig.toNat < z.fst.toNat := B256.toNat_lt_toNat hlt
            omega
        rcases ih hsortedTake htakeLen hmemberTake popped.2 leftRun with
          ⟨bodyPre, bodyStack, bodyState, bodyMemory, bodyRun⟩
        exact ⟨bodyPre, bodyStack, testState.trans (hpop.state.trans bodyState),
          testMemory.trans (hpop.memory.trans bodyMemory), bodyRun⟩

/-- An avoiding walk of a sorted binary dispatcher, entered with the selector
on the stack, reaches the selected body as an avoiding walk. -/
theorem reach_of_dispatchWith
    {entries : List (B256 × Func)} {sig : B256} {body : Func}
    {k : Nat} {s : Devm} {out : Execution} {tail : Stack}
    (hsorted : DispatchTree.sorted entries = true)
    (hmember : (sig, body) ∈ entries)
    (hp : sig :: tail <<+ s.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm s
      (dispatchWith k (DispatchTree.ofSorted entries)) out) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧ s.state = bodyPre.state ∧
      s.memory = bodyPre.memory ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out :=
  reach_of_dispatchWith_build hsorted (Nat.le_succ _) hmember hp run

end Func.RunCompiledToAvoiding

/-! ## Line facts through a `STOP`-terminated source run

A `Func.WalkInv` trace of a line-prefixed body `l +++ body` may be read at any
`Line.Run` of `l`: instantiate it at the source relation with `body := STOP`,
build that run from the line, and identify the trace's continuation state with
the line's end state through the `STOP`.  This lets a revert-aware walk reuse
the family's proved line traces instead of restating them. -/

theorem Func.Run.prepend_stop {fs : List Func} {sevm : Sevm} {pre mid : Devm}
    {l : Line} (line : Line.Run sevm pre l mid) :
    Func.Run fs sevm pre (l +++ Func.stop) mid := by
  induction line with
  | nil => exact Func.Run.last rfl
  | cons step _ ih => exact Func.Run.next step ih

theorem Func.Run.stop_inv {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (run : Func.Run fs sevm pre Func.stop post) : post = pre := by
  cases run with
  | last h =>
    have h' : Linst.run sevm pre .stop = .ok post := h
    simp only [Linst.run, Except.ok.injEq] at h'
    exact h'.symm

/-- `revertFreeIn` looks through a line prefix. -/
theorem Func.revertFreeIn_prepend (safe : List Nat) (l : Line) (f : Func) :
    Func.revertFreeIn safe (l +++ f) = Func.revertFreeIn safe f := by
  induction l with
  | nil => rfl
  | cons i l ih => exact ih

/-! ## Source runs cut at one continuation call

A revert-cause walk often reaches a known continuation `call k` after a
stretch whose success traces are stated for `Func.WalkInv` relations.  The
stretch is replayed as a source run in `Func.stopTable k`, where entry `k` is
`STOP`: the source run ends exactly where the walk entered the continuation,
and any family trace instantiated at `Func.Run` over that table reads the
stretch without restating it.  The walk itself continues, still avoiding, in
the real table. -/

/-- A table whose entry `k` (and every earlier one) is `STOP`. -/
def Func.stopTable (k : Nat) : List Func := List.replicate (k + 1) Func.stop

theorem Func.stopTable_get (k : Nat) :
    (Func.stopTable k)[k]? = some Func.stop := by
  simp [Func.stopTable]

/-- The straight-line prefix of a body that ends in one `call`. -/
def Func.lineCall : Func → Option (Line × Nat)
  | .next i f => (Func.lineCall f).map fun p => (i :: p.1, p.2)
  | .call k => some ([], k)
  | _ => none

theorem Func.eq_of_lineCall {f : Func} :
    ∀ {l : Line} {k : Nat}, f.lineCall = some (l, k) → f = l +++ .call k := by
  induction f with
  | next i f ih =>
    intro l k h
    simp only [Func.lineCall, Option.map_eq_some_iff] at h
    obtain ⟨⟨l', k'⟩, h', hp⟩ := h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    rw [ih h']
    rfl
  | call k =>
    intro l k' h
    simp only [Func.lineCall, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | last _ => intro l k h; simp [Func.lineCall] at h
  | branch _ _ _ _ => intro l k h; simp [Func.lineCall] at h

theorem Func.lineCall_prepend (l : Line) (f : Func) :
    (l +++ f).lineCall = f.lineCall.map fun p => (l ++ p.1, p.2) := by
  induction l with
  | nil => cases h : f.lineCall <;> simp [prepend, h]
  | cons i l ih =>
    change ((l +++ f).lineCall).map _ = _
    rw [ih, Option.map_map]
    rfl

theorem Func.Run.prepend_line {fs : List Func} {sevm : Sevm}
    {pre mid post : Devm} {l : Line} {f : Func}
    (line : Line.Run sevm pre l mid) (run : Func.Run fs sevm mid f post) :
    Func.Run fs sevm pre (l +++ f) post := by
  induction line with
  | nil => exact run
  | cons step _ ih => exact Func.Run.next step (ih run)

theorem Func.Run.zero_of_popBurnBy {fs : List Func} {sevm : Sevm}
    {pre mid post : Devm} {cost : Nat} {f g : Func}
    (pop : Devm.PopBurnBy [0] cost pre mid) (run : Func.Run fs sevm mid f post) :
    Func.Run fs sevm pre (Func.branch f g) post :=
  Func.Run.zero (Devm.PopBurn.of_popBurnBy pop) run

theorem Func.Run.succ_of_popBurnBy {fs : List Func} {sevm : Sevm}
    {pre mid post : Devm} {cost : Nat} {w : B256} {f g : Func}
    (hw : w ≠ 0) (pop : Devm.PopBurnBy [w] cost pre mid)
    (run : Func.Run fs sevm mid g post) :
    Func.Run fs sevm pre (Func.branch f g) post :=
  Func.Run.succ hw (Devm.PopBurn.of_popBurnBy pop) Devm.Burn.refl run

/-- A straight-line stretch ending in `call k`, peeled from an avoiding walk:
the stretch is a source run in the `STOP` table, and the walk continues,
still avoiding, in the continuation body. -/
theorem Func.RunCompiledToAvoiding.lineCall_inv
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func} {sevm : Sevm}
    {pre : Devm} {out : Execution} {f body : Func} {l : Line} {k : Nat}
    (shape : f.lineCall = some (l, k))
    (lookup : fs[k]? = some body)
    (run : Func.RunCompiledToAvoiding P fs sevm pre f out) :
    ∃ mid, Func.Run (Func.stopTable k) sevm pre f mid ∧
      Func.RunCompiledToAvoiding P fs sevm mid body out := by
  rw [Func.eq_of_lineCall shape] at run ⊢
  obtain ⟨callPre, line, callRun⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨mid, burn, bodyRun⟩ :=
    Func.RunCompiledToAvoiding.call_inv lookup callRun
  exact ⟨mid, Func.Run.prepend_line line
    (Func.Run.call (Func.stopTable_get k) (Devm.Burn.of_burnBy burn)
      (Func.Run.last rfl)), bodyRun⟩

end Blanc
