-- CommonProofs/Frames.lean : outcome-aware effects, instruction frames and world-equivalence frame laws.

import Blanc.CommonProofs.Base

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

/-! ## Outcome-aware effects for the EVM semantic layers -/

namespace Outcome

/-- Outcome-aware lifting of a state relation across both `Except` branches. -/
def Rel {σ ε α : Type}
    (errState : ε → σ) (okState : α → σ)
    (R : σ → σ → Prop) (pre : σ) : Except ε α → Prop
  | .error err => R pre (errState err)
  | .ok value => R pre (okState value)

/-
This is the generic weakening rule for both success and error outcomes.
-/
lemma Rel.mono {σ ε α : Type}
    {errState : ε → σ} {okState : α → σ} {R S : σ → σ → Prop}
    {pre : σ} {out : Except ε α}
    (hrefine : ∀ ⦃s t⦄, R s t → S s t)
    (h : Rel errState okState R pre out) :
    Rel errState okState S pre out := by
  cases out <;> exact hrefine h

end Outcome

/-- Canonical outcome-aware preservation statement for dynamic EVM execution. -/
def Execution.Rel (R : Devm → Devm → Prop) (pre : Devm) (out : Execution) : Prop :=
  Outcome.Rel Prod.snd id R pre out

lemma outcomeRel_toExecution {R : Devm → Devm → Prop} {pre : Devm}
    {out : Except (EvmError × Devm) (Unit × Devm)}
    (h : Outcome.Rel Prod.snd Prod.snd R pre out) :
    Execution.Rel R pre (Footprint.toExecution out) := by
  cases out <;> exact h

-- The full-frame infrastructure and master regular-instruction theorem are
-- declared here so that the legacy observation lemmas below can be stated as
-- projections of them.

-- Paired projection of the two deletion-relevant sets
def Devm.delSets (d : Devm) : AdrSet × AdrSet :=
  (d.accountsToDelete, d.createdAccounts)

/-! ## Full-frame relations for instruction preservation -/

/-- A Mach-only step may change exactly the four `Mach` fields. -/
def Devm.Rels.machFrame : Devm.Rels :=
  { Devm.Rels.eq with
    stack := fun _ _ => True
    memory := fun _ _ => True
    gasLeft := fun _ _ => True
    stateGas := fun _ _ => True }

/-- Coarse instruction frame: state, deletion and created-account sets,
    transient storage, and storage-write annotations remain equal. Other metadata,
    including touched accounts, is unobserved; exact `Pop`/`Burn` relations and
    the Mach-only frame retain touched-account equality. -/
def Devm.Rels.instructionFrame : Devm.Rels :=
  {
    stack := fun _ _ => True
    memory := fun _ _ => True
    gasLeft := fun _ _ => True
    logs := fun _ _ => True
    refundCounter := fun _ _ => True
    output := fun _ _ => True
    accountsToDelete := _root_.Eq
    returnData := fun _ _ => True
    error := fun _ _ => True
    accessedAddresses := fun _ _ => True
    accessedStorageKeys := fun _ _ => True
    state := _root_.Eq
    createdAccounts := _root_.Eq
    transientStorage := _root_.Eq
    stateGas := fun _ _ => True
    accountReads := fun _ _ => True
    storageReads := fun _ _ => True, storageWrites := _root_.Eq,
    touchedAccounts := fun _ _ => True }

abbrev Devm.MachFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.machFrame

abbrev Devm.InstructionFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.instructionFrame

/-- The part of `Meta` that an instruction-frame lift must preserve. -/
def Meta.InstructionFrame (a b : Meta) : Prop :=
  a.accountsToDelete = b.accountsToDelete ∧
    a.createdAccounts = b.createdAccounts

lemma Devm.Rels.instructionFrame_refl :
    Devm.Rels.Refl Devm.Rels.instructionFrame := by
  simp only [Devm.Rels.Refl, ReflexiveRel, instructionFrame, implies_true, and_self]

lemma Devm.Rels.instructionFrame_trans :
    Devm.Rels.Trans Devm.Rels.instructionFrame := by
  simp only [Devm.Rels.Trans, TransitiveRel, instructionFrame, imp_self, implies_true,
    forall_apply_eq_imp_iff, and_self]

lemma Devm.instructionFrame_refl : ReflexiveRel Devm.InstructionFrame :=
  Devm.rel_refl Devm.Rels.instructionFrame_refl

lemma Devm.instructionFrame_trans : TransitiveRel Devm.InstructionFrame :=
  Devm.rel_trans Devm.Rels.instructionFrame_trans

lemma Devm.machFrame_refines_instructionFrame :
    ∀ ⦃d d'⦄, Devm.MachFrame d d' → Devm.InstructionFrame d d' := by
  intro d d' h
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := h.accountsToDelete
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := h.state
    createdAccounts := h.createdAccounts
    transientStorage := h.transientStorage
    stateGas := trivial
    accountReads := trivial
    storageReads := trivial, storageWrites := h.storageWrites, touchedAccounts := trivial }

lemma Devm.InstructionFrame.getBal {d d' : Devm}
    (h : Devm.InstructionFrame d d') (a : Adr) :
    d.getBal a = d'.getBal a := by
  unfold Devm.getBal Devm.getAcct
  rw [h.state]

lemma Devm.InstructionFrame.getStor {d d' : Devm}
    (h : Devm.InstructionFrame d d') (a : Adr) :
    Devm.getStor d a = Devm.getStor d' a := by
  unfold Devm.getStor Devm.getAcct
  rw [h.state]

lemma Devm.InstructionFrame.getCode {d d' : Devm}
    (h : Devm.InstructionFrame d d') (a : Adr) :
    d.getCode a = d'.getCode a := by
  unfold Devm.getCode Devm.getAcct
  rw [h.state]

lemma Devm.InstructionFrame.delSets {d d' : Devm}
    (h : Devm.InstructionFrame d d') :
    Devm.delSets d = Devm.delSets d' :=
  Prod.ext h.accountsToDelete h.createdAccounts

lemma Devm.machFrame_setMach (d : Devm) (mach : Mach) :
    Devm.MachFrame d (d.setMach mach) := by
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := rfl
    refundCounter := rfl
    output := rfl
    accountsToDelete := rfl
    returnData := rfl
    error := rfl
    accessedAddresses := rfl
    accessedStorageKeys := rfl
    state := rfl
    createdAccounts := rfl
    transientStorage := rfl
    stateGas := trivial
    accountReads := rfl
    storageReads := rfl, storageWrites := rfl, touchedAccounts := rfl }

lemma Devm.instructionFrame_setMachMeta (d : Devm) (view : Mach × Meta)
    (h : Meta.InstructionFrame d.meta view.2) :
    Devm.InstructionFrame d
      { d with mach := view.1, «meta» := view.2 } := by
  rcases h with ⟨hdel, hcreated⟩
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := hdel
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := rfl
    createdAccounts := hcreated
    transientStorage := rfl
    stateGas := trivial
    accountReads := trivial
    storageReads := trivial, storageWrites := rfl, touchedAccounts := trivial }

/-! ### Full-frame lift rules -/

lemma liftMach_machFrame (core : Mach → Footprint.Outcome Mach α) (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (liftMach core d) := by
  unfold liftMach Footprint.liftOutcome
  cases core d.mach <;> exact Devm.machFrame_setMach d _

lemma liftMachPure_machFrame (core : Mach → Mach) (d : Devm) :
    Devm.MachFrame d (liftMachPure core d) := by
  exact Devm.machFrame_setMach d _

lemma liftMachExecution_machFrame
    (core : Mach → Footprint.Outcome Mach Unit) (d : Devm) :
    Execution.Rel Devm.MachFrame d (liftMachExecution core d) := by
  unfold liftMachExecution
  exact outcomeRel_toExecution (liftMach_machFrame core d)

lemma liftMachMetaPure_instructionFrame
    (core : Mach → Meta → Mach × Meta) (d : Devm)
    (hcore : Meta.InstructionFrame d.meta (core d.mach d.meta).2) :
    Devm.InstructionFrame d (liftMachMetaPure core d) := by
  exact Devm.instructionFrame_setMachMeta d _ hcore

/-! ### Full-frame primitive facts -/

lemma Devm.pop_machFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.pop d) := by
  exact liftMach_machFrame Mach.pop d

lemma Devm.pop_instructionFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.pop d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.pop_machFrame d)

lemma Devm.push_machFrame (x : B256) (d : Devm) :
    Execution.Rel Devm.MachFrame d (Devm.push x d) := by
  exact liftMachExecution_machFrame (Mach.push x) d

lemma Devm.push_instructionFrame (x : B256) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (Devm.push x d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.push_machFrame x d)

lemma pushItem_machFrame (x : B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (pushItem x cost d) := by
  exact liftMachExecution_machFrame (Mach.pushItem x cost) d

lemma chargeGas_machFrame (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (chargeGas cost d) := by
  exact liftMachExecution_machFrame (Mach.chargeGas cost) d

lemma chargeGas_instructionFrame (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (chargeGas cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (chargeGas_machFrame cost d)

lemma chargeStateGas_instructionFrame (amount : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (chargeStateGas amount d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (liftMachExecution_machFrame (Mach.chargeStateGas amount) d)

/-- A successful state-gas charge preserves the operand stack: only the gas
pools move. The `instructionFrame`/`machFrame` relations both relax `stack`,
so walks that track it need this equation. -/
lemma Devm.chargeStateGas_stack {amount : Nat} {d d' : Devm}
    (h : chargeStateGas amount d = .ok d') : d'.stack = d.stack := by
  dsimp only [ExceptT.stM_eq, chargeStateGas, liftMachExecution, Footprint.toExecution, liftMach,
    Footprint.liftOutcome, Mach.chargeStateGas, Lean.Elab.WF.paramLet, tsub_le_iff_right] at h
  by_cases h1 : amount ≤ d.mach.stateGas.left
  · simp only [h1] at h
    injection h with heq; subst heq; rfl
  · simp only [h1] at h
    by_cases h2 : amount - d.mach.stateGas.left ≤ d.mach.gasLeft
    · simp only [h2] at h
      injection h with heq; subst heq; rfl
    · simp only [h2] at h
      cases h

/-- A successful state-gas charge preserves memory, for the same walks. -/
lemma Devm.chargeStateGas_memory {amount : Nat} {d d' : Devm}
    (h : chargeStateGas amount d = .ok d') : d'.memory = d.memory := by
  dsimp only [ExceptT.stM_eq, chargeStateGas, liftMachExecution, Footprint.toExecution, liftMach,
    Footprint.liftOutcome, Mach.chargeStateGas, Lean.Elab.WF.paramLet, tsub_le_iff_right] at h
  by_cases h1 : amount ≤ d.mach.stateGas.left
  · simp only [h1] at h
    injection h with heq; subst heq; rfl
  · simp only [h1] at h
    by_cases h2 : amount - d.mach.stateGas.left ≤ d.mach.gasLeft
    · simp only [h2] at h
      injection h with heq; subst heq; rfl
    · simp only [h2] at h
      cases h

/-- A successful state-gas charge preserves the log list. -/
lemma Devm.chargeStateGas_logs {amount : Nat} {d d' : Devm}
    (h : chargeStateGas amount d = .ok d') : d'.logs = d.logs := by
  dsimp only [ExceptT.stM_eq, chargeStateGas, liftMachExecution, Footprint.toExecution, liftMach,
    Footprint.liftOutcome, Mach.chargeStateGas, Lean.Elab.WF.paramLet, tsub_le_iff_right] at h
  by_cases h1 : amount ≤ d.mach.stateGas.left
  · simp only [h1] at h
    injection h with heq; subst heq; rfl
  · simp only [h1] at h
    by_cases h2 : amount - d.mach.stateGas.left ≤ d.mach.gasLeft
    · simp only [h2] at h
      injection h with heq; subst heq; rfl
    · simp only [h2] at h
      cases h

/-- A successful state-gas charge preserves the output buffer. -/
lemma Devm.chargeStateGas_output {amount : Nat} {d d' : Devm}
    (h : chargeStateGas amount d = .ok d') : d'.output = d.output := by
  dsimp only [ExceptT.stM_eq, chargeStateGas, liftMachExecution, Footprint.toExecution, liftMach,
    Footprint.liftOutcome, Mach.chargeStateGas, Lean.Elab.WF.paramLet, tsub_le_iff_right] at h
  by_cases h1 : amount ≤ d.mach.stateGas.left
  · simp only [h1] at h
    injection h with heq; subst heq; rfl
  · simp only [h1] at h
    by_cases h2 : amount - d.mach.stateGas.left ≤ d.mach.gasLeft
    · simp only [h2] at h
      injection h with heq; subst heq; rfl
    · simp only [h2] at h
      cases h

/-- A successful state-gas charge preserves loaded storage. -/
lemma Devm.chargeStateGas_getStor {amount : Nat} {d d' : Devm}
    (h : chargeStateGas amount d = .ok d') : Devm.getStor d = Devm.getStor d' := by
  dsimp only [ExceptT.stM_eq, chargeStateGas, liftMachExecution, Footprint.toExecution, liftMach,
    Footprint.liftOutcome, Mach.chargeStateGas, Lean.Elab.WF.paramLet, tsub_le_iff_right] at h
  by_cases h1 : amount ≤ d.mach.stateGas.left
  · simp only [h1] at h
    injection h with heq; subst heq; rfl
  · simp only [h1] at h
    by_cases h2 : amount - d.mach.stateGas.left ≤ d.mach.gasLeft
    · simp only [h2] at h
      injection h with heq; subst heq; rfl
    · simp only [h2] at h
      cases h

/-- State-gas charging leaves the world state untouched. -/
lemma Devm.chargeStateGas_state {amount : Nat} {d d' : Devm}
    (h : chargeStateGas amount d = .ok d') : d'.state = d.state := by
  dsimp only [ExceptT.stM_eq, chargeStateGas, liftMachExecution, Footprint.toExecution, liftMach,
    Footprint.liftOutcome, Mach.chargeStateGas, Lean.Elab.WF.paramLet, tsub_le_iff_right] at h
  by_cases h1 : amount ≤ d.mach.stateGas.left
  · simp only [h1] at h
    injection h with heq; subst heq; rfl
  · simp only [h1] at h
    by_cases h2 : amount - d.mach.stateGas.left ≤ d.mach.gasLeft
    · simp only [h2] at h
      injection h with heq; subst heq; rfl
    · simp only [h2] at h
      cases h

lemma Devm.popToNat_machFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.popToNat d) := by
  exact liftMach_machFrame Mach.popToNat d

lemma Devm.popToNat_instructionFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.popToNat d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.popToNat_machFrame d)

lemma Devm.popToAdr_machFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.popToAdr d) := by
  exact liftMach_machFrame Mach.popToAdr d

lemma Devm.popToAdr_instructionFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.popToAdr d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.popToAdr_machFrame d)

lemma Devm.popN_machFrame (d : Devm) (n : Nat) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.popN d n) := by
  exact liftMach_machFrame (Mach.popN · n) d

lemma applyUnary_machFrame (f : B256 → B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (applyUnary f cost d) := by
  exact liftMachExecution_machFrame (Mach.applyUnary f cost) d

lemma applyBinary_machFrame (f : B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (applyBinary f cost d) := by
  exact liftMachExecution_machFrame (Mach.applyBinary f cost) d

lemma applyTernary_machFrame (f : B256 → B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (applyTernary f cost d) := by
  exact liftMachExecution_machFrame (Mach.applyTernary f cost) d

lemma Devm.memWrite_machFrame (d : Devm) (idx : Nat) (val : Bytes) :
    Devm.MachFrame d (Devm.memWrite d idx val) := by
  exact liftMachPure_machFrame (Mach.memWrite · idx val) d

lemma Devm.memWrite_instructionFrame (d : Devm) (idx : Nat) (val : Bytes) :
    Devm.InstructionFrame d (Devm.memWrite d idx val) := by
  exact Devm.machFrame_refines_instructionFrame
    (Devm.memWrite_machFrame d idx val)

lemma Devm.memExtends_machFrame (d : Devm) (ranges : List (Nat × Nat)) :
    Devm.MachFrame d (Devm.memExtends d ranges) := by
  exact liftMachPure_machFrame (Mach.memExtends · ranges) d

lemma Devm.memExtends_instructionFrame (d : Devm)
    (ranges : List (Nat × Nat)) :
    Devm.InstructionFrame d (Devm.memExtends d ranges) := by
  exact Devm.machFrame_refines_instructionFrame
    (Devm.memExtends_machFrame d ranges)

lemma addAccessedAddress_instructionFrame (d : Devm) (a : Adr) :
    Devm.InstructionFrame d (addAccessedAddress d a) := by
  exact liftMachMetaPure_instructionFrame _ d ⟨rfl, rfl⟩

/-- Access-delegation resolves an EOA delegation without touching the world or
    the deletion sets, so it stays inside the instruction frame. -/
lemma accessDelegation_instructionFrame (d : Devm) (adr : Adr) :
    Devm.InstructionFrame d (accessDelegation d adr).2.2.2.2 := by
  rw [accessDelegation]
  cases getDelegatedCodeAddress (d.state.getCode adr)
  · exact Devm.instructionFrame_refl d
  · exact addAccessedAddress_instructionFrame d _

/-- Schedule-parameterized access-delegation resolves an EOA delegation without
    touching the world or the deletion sets, so it stays inside the instruction
    frame. -/
lemma GasSchedule.accessDelegation_instructionFrame (gas : GasSchedule)
    (d : Devm) (adr : Adr) :
    Devm.InstructionFrame d (gas.accessDelegation d adr).2.2.2.2 := by
  rw [GasSchedule.accessDelegation]
  cases getDelegatedCodeAddress (d.state.getCode adr)
  · exact Devm.instructionFrame_refl d
  · exact addAccessedAddress_instructionFrame d _

/-- Fork-gated delegation changes only access metadata, including when disabled. -/
lemma ForkRules.accessDelegation_instructionFrame (rules : ForkRules)
    (d : Devm) (adr : Adr) :
    Devm.InstructionFrame d (rules.accessDelegation d adr).2.2.2.2 := by
  unfold ForkRules.accessDelegation
  split
  · exact GasSchedule.accessDelegation_instructionFrame rules.gas d adr
  · exact Devm.instructionFrame_refl d

/-- Draining the state-gas reservoir only reorganizes `Mach` gas fields, so it
    stays inside the instruction frame. -/
lemma Devm.drainStateGasReservoir_instructionFrame (d : Devm) :
    Devm.InstructionFrame d (d.drainStateGasReservoir.2) := by
  have h : d.drainStateGasReservoir.2
      = d.setMach (d.mach.drainStateGasReservoir.2) := by
    unfold Devm.drainStateGasReservoir
    cases h : d.mach.drainStateGasReservoir with
    | mk r m => rfl
  rw [h]
  exact Devm.machFrame_refines_instructionFrame
    (Devm.machFrame_setMach d (d.mach.drainStateGasReservoir.2))

lemma Devm.creditStateGasRefund_instructionFrame (amount : Nat) (d : Devm) :
    Devm.InstructionFrame d (Devm.creditStateGasRefund amount d) := by
  unfold Devm.creditStateGasRefund
  exact Devm.machFrame_refines_instructionFrame (Devm.machFrame_setMach d _)

lemma Devm.restoreChildGas_instructionFrame (gas reservoir : Nat) (d : Devm) :
    Devm.InstructionFrame d (Devm.restoreChildGas gas reservoir d) := by
  unfold Devm.restoreChildGas
  exact Devm.machFrame_refines_instructionFrame (Devm.machFrame_setMach d _)

lemma Devm.withholdCreateGas_instructionFrame (d : Devm) :
    Devm.InstructionFrame d (d.withholdCreateGas.2) := by
  have h : d.withholdCreateGas.2
      = d.setMach (d.mach.withholdCreateGas.2) := by
    unfold Devm.withholdCreateGas
    cases h : d.mach.withholdCreateGas with
    | mk c m => rfl
  rw [h]
  exact Devm.machFrame_refines_instructionFrame
    (Devm.machFrame_setMach d (d.mach.withholdCreateGas.2))

/-- Amsterdam delegation completion at most warms one address, so it stays
    inside the instruction frame. -/
lemma completeDelegationAccess_instructionFrame (d : Devm) (dp : Bool)
    (adr : Adr) :
    Devm.InstructionFrame d (completeDelegationAccess d dp adr).2 := by
  cases dp
  · exact Devm.instructionFrame_refl d
  · exact addAccessedAddress_instructionFrame d adr

lemma Devm.addLog_instructionFrame (d : Devm) (log : Log) :
    Devm.InstructionFrame d (Devm.addLog d log) := by
  exact liftMachMetaPure_instructionFrame _ d ⟨rfl, rfl⟩

lemma Devm.emitTransferLog_instructionFrame (d : Devm) (sender recipient : Adr)
    (amount : B256) :
    Devm.InstructionFrame d (Devm.emitTransferLog d sender recipient amount) := by
  unfold Devm.emitTransferLog
  split
  · exact Devm.instructionFrame_refl _
  · exact Devm.addLog_instructionFrame _ _

/-! ### Bind composition for frame relations -/

lemma Outcome.Rel.bindExecution
    {R : Devm → Devm → Prop} (htrans : TransitiveRel R)
    {pre : Devm} {out : Except (EvmError × Devm) (α × Devm)}
    {next : α → Devm → Execution}
    (hout : Outcome.Rel Prod.snd Prod.snd R pre out)
    (hnext : ∀ x d, Execution.Rel R d (next x d)) :
    Execution.Rel R pre (out >>= fun x => next x.1 x.2) := by
  cases out with
  | error e => exact hout
  | ok x =>
      cases hn : next x.1 x.2 with
      | error e =>
          have h := hnext x.1 x.2
          rw [hn] at h
          simpa only [Except.bind_ok, hn, Execution.Rel, Outcome.Rel] using htrans hout h
      | ok d =>
          have h := hnext x.1 x.2
          rw [hn] at h
          simpa only [Except.bind_ok, hn, id_eq, Execution.Rel, Outcome.Rel] using htrans hout h

lemma Execution.Rel.bind
    {R : Devm → Devm → Prop} (htrans : TransitiveRel R)
    {pre : Devm} {out : Execution} {next : Devm → Execution}
    (hout : Execution.Rel R pre out)
    (hnext : ∀ d, Execution.Rel R d (next d)) :
    Execution.Rel R pre (out >>= next) := by
  cases out with
  | error e => exact hout
  | ok d =>
      cases hn : next d with
      | error e =>
          have h := hnext d
          rw [hn] at h
          simpa only [Except.bind_ok, hn, Execution.Rel, Outcome.Rel] using htrans hout h
      | ok d' =>
          have h := hnext d
          rw [hn] at h
          simpa only [Except.bind_ok, hn, id_eq, Execution.Rel, Outcome.Rel] using htrans hout h

/-! ## Master regular-instruction frame theorem -/

/-- Equality of the balance/code observations of two world states.  Storage is
    deliberately absent: it is the component written by `SSTORE`. -/
def State.BalCodeEq (a b : Jaune.State) : Prop :=
  (fun adr => ((a.get adr).bal, (a.get adr).code)) =
    fun adr => ((b.get adr).bal, (b.get adr).code)

/-- Canonical precise effect of the persistent-storage writer: balances and
code are unchanged at every address. -/
lemma State.setStorVal_balCodeEq (st : Jaune.State)
    (adr : Adr) (key value : B256) :
    State.BalCodeEq st (st.setStorVal adr key value) := by
  unfold State.BalCodeEq
  funext address
  by_cases h : adr = address
  · subst address
    rw [State.setStorVal_get_self]
  · rw [State.setStorVal_get_ne _ h]

/-- `SSTORE` may change storage in `state` and record the written key in
    `storageWrites`, but preserves balances, code, and the other world/frame
    fields. -/
def Devm.Rels.stateWriteFrame : Devm.Rels :=
  { Devm.Rels.instructionFrame with
    state := State.BalCodeEq
    storageWrites := fun _ _ => True }

/-- `TSTORE` may change `transientStorage`, but preserves the other
    world/frame fields. -/
def Devm.Rels.transientWriteFrame : Devm.Rels :=
  { Devm.Rels.instructionFrame with transientStorage := fun _ _ => True }

abbrev Devm.StateWriteFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.stateWriteFrame

abbrev Devm.TransientWriteFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.transientWriteFrame

lemma Devm.Rels.stateWriteFrame_refl :
    Devm.Rels.Refl Devm.Rels.stateWriteFrame := by
  simp only [Devm.Rels.Refl, ReflexiveRel, stateWriteFrame, instructionFrame, implies_true,
    State.BalCodeEq, and_self]

lemma Devm.Rels.stateWriteFrame_trans :
    Devm.Rels.Trans Devm.Rels.stateWriteFrame := by
  simp_all only [Devm.Rels.Trans, TransitiveRel, stateWriteFrame, instructionFrame, imp_self,
    implies_true, State.BalCodeEq, and_self]

lemma Devm.Rels.transientWriteFrame_refl :
    Devm.Rels.Refl Devm.Rels.transientWriteFrame := by
  simp only [Devm.Rels.Refl, ReflexiveRel, transientWriteFrame, instructionFrame, implies_true,
    and_self]

lemma Devm.Rels.transientWriteFrame_trans :
    Devm.Rels.Trans Devm.Rels.transientWriteFrame := by
  simp only [Devm.Rels.Trans, TransitiveRel, transientWriteFrame, instructionFrame, imp_self,
    implies_true, forall_apply_eq_imp_iff, and_self]

lemma Devm.stateWriteFrame_refl : ReflexiveRel Devm.StateWriteFrame :=
  Devm.rel_refl Devm.Rels.stateWriteFrame_refl

lemma Devm.stateWriteFrame_trans : TransitiveRel Devm.StateWriteFrame :=
  Devm.rel_trans Devm.Rels.stateWriteFrame_trans

lemma Devm.transientWriteFrame_refl : ReflexiveRel Devm.TransientWriteFrame :=
  Devm.rel_refl Devm.Rels.transientWriteFrame_refl

lemma Devm.transientWriteFrame_trans : TransitiveRel Devm.TransientWriteFrame :=
  Devm.rel_trans Devm.Rels.transientWriteFrame_trans

lemma Devm.instructionFrame_refines_stateWriteFrame :
    ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → Devm.StateWriteFrame d d' := by
  intro d d' h
  refine { h with state := ?_, storageWrites := trivial }
  change State.BalCodeEq d.state d'.state
  rw [h.state]
  rfl

lemma Devm.instructionFrame_refines_transientWriteFrame :
    ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → Devm.TransientWriteFrame d d' := by
  intro d d' h
  exact { h with transientStorage := trivial }

lemma Devm.instructionFrame_of_world_eq {d d' : Devm}
    (hdel : d.accountsToDelete = d'.accountsToDelete)
    (hstate : d.state = d'.state)
    (hcreated : d.createdAccounts = d'.createdAccounts)
    (htransient : d.transientStorage = d'.transientStorage)
    (hwrites : d.world.storageWrites = d'.world.storageWrites) :
    Devm.InstructionFrame d d' := by
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := hdel
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := hstate
    createdAccounts := hcreated
    transientStorage := htransient
    stateGas := trivial
    accountReads := trivial
    storageReads := trivial, storageWrites := hwrites, touchedAccounts := trivial }

/-- EIP-7928 account-read recording touches only the read set, so it stays
    inside the instruction frame. -/
lemma Devm.balReadAccount_instructionFrame (rules : ForkRules) (a : Adr)
    (d : Devm) :
    Devm.InstructionFrame d (Devm.balReadAccount rules a d) := by
  unfold Devm.balReadAccount Meta.readAccount
  split
  · exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl
  · exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl

/-- EIP-7928 storage-read recording touches only the read set, so it stays
    inside the instruction frame. -/
lemma Devm.balReadStorage_instructionFrame (rules : ForkRules) (a : Adr)
    (k : B256) (d : Devm) :
    Devm.InstructionFrame d (Devm.balReadStorage rules a k d) := by
  unfold Devm.balReadStorage Meta.readStorage
  split
  · exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl
  · exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl rfl

/-- `ForkRules.Valid` does not tie `stateGas` to `bal`, but `BenvStat.rules` is
`Fork.ruleSet` of a five-constructor `Fork`, and Amsterdam is the only fork
carrying either. So a machine in the one-dimensional metering lane also builds
no block access list, and every EIP-7928 recorder on it is the identity. This
is what lets a single `stateGas = none` premise carry a whole proof through
Jaune's Amsterdam-series insertions. -/
lemma BenvStat.bal_none_of_stateGas_none {s : BenvStat}
    (h : s.rules.stateGas = none) : s.rules.bal = none := by
  have key : ∀ f : Fork,
      (Fork.ruleSet f).stateGas = none → (Fork.ruleSet f).bal = none := by
    intro f hf
    cases f <;> first | rfl | exact absurd hf (by decide)
  exact key s.fork h

/-- Under `bal = none` the account-read recorder is the identity. -/
lemma Devm.balReadAccount_of_bal_none {rules : ForkRules} {a : Adr} {d : Devm}
    (h : rules.bal = none) : Devm.balReadAccount rules a d = d := by
  unfold Devm.balReadAccount
  rw [h]
  rfl

/-- Under `bal = none` the storage-read recorder is the identity. -/
lemma Devm.balReadStorage_of_bal_none {rules : ForkRules} {a : Adr} {k : B256}
    {d : Devm} (h : rules.bal = none) : Devm.balReadStorage rules a k d = d := by
  unfold Devm.balReadStorage
  rw [h]
  rfl

/-- EIP-7928 storage-read recording leaves the log list alone: `logs` is a
`Meta` field, so the equation needs the `bal`-presence split rather than
`rfl`. Jaune names the `mach`/`world` projections; the log/output cases
live here beside their use sites. -/
lemma Devm.balReadStorage_logs {rules : ForkRules} {a : Adr} {k : B256}
    {devm : Devm} :
    (Devm.balReadStorage rules a k devm).logs = devm.logs := by
  unfold Devm.balReadStorage Meta.readStorage; split <;> rfl

lemma Devm.balReadStorage_output {rules : ForkRules} {a : Adr} {k : B256}
    {devm : Devm} :
    (Devm.balReadStorage rules a k devm).output = devm.output := by
  unfold Devm.balReadStorage Meta.readStorage; split <;> rfl

lemma Devm.balReadAccount_output {rules : ForkRules} {a : Adr}
    {devm : Devm} :
    (Devm.balReadAccount rules a devm).output = devm.output := by
  unfold Devm.balReadAccount Meta.readAccount; split <;> rfl

lemma Execution.Rel.trans_left {R : Devm → Devm → Prop}
    (htrans : TransitiveRel R) {a b : Devm} {out : Execution}
    (hab : R a b) (hout : Execution.Rel R b out) :
    Execution.Rel R a out := by
  cases out <;> exact htrans hab hout

/-- Jaune's world frame (`Devm.WorldFrame`: world and the two deletion sets)
is exactly what the instruction frame pins. -/
lemma Devm.WorldFrame.instructionFrame {d d' : Devm} (h : d.WorldFrame d') :
    Devm.InstructionFrame d d' :=
  Devm.instructionFrame_of_world_eq h.accountsToDelete h.state h.createdAccounts
    h.transientStorage (congrArg (·.storageWrites) h.world)

/-- Jaune's two-channel world-frame result gives the instruction frame. -/
lemma Execution.Rel.of_worldFrame {pre : Devm} {x : Execution} (h : x.WorldFrame pre) :
    Execution.Rel Devm.InstructionFrame pre x := by
  cases x <;> exact Devm.WorldFrame.instructionFrame h

/-- Every regular instruction other than `SSTORE`/`TSTORE` keeps the instruction
frame: a corollary of Jaune's single world-frame walk `Rinst.runCore_worldFrame`. -/
theorem Rinst.runCore_instructionFrame
    (pc : Nat) (sevm : Sevm) (pre : Devm) (r : Rinst)
    (h_not_sstore : r ≠ .sstore) (h_not_tstore : r ≠ .tstore) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm r) :=
  Execution.Rel.of_worldFrame
    (Rinst.runCore_worldFrame pc sevm pre r h_not_sstore h_not_tstore)

lemma Devm.stateWriteFrame_of_world_eq {d d' : Devm}
    (hdel : d.accountsToDelete = d'.accountsToDelete)
    (hstate : d.state = d'.state)
    (hcreated : d.createdAccounts = d'.createdAccounts)
    (htransient : d.transientStorage = d'.transientStorage) :
    Devm.StateWriteFrame d d' := by
  exact {
    stack := trivial, memory := trivial, gasLeft := trivial, logs := trivial
    refundCounter := trivial, output := trivial, accountsToDelete := hdel
    returnData := trivial, error := trivial, accessedAddresses := trivial
    accessedStorageKeys := trivial, state := by
      change State.BalCodeEq d.state d'.state
      rw [hstate]
      rfl
    createdAccounts := hcreated, transientStorage := htransient
    stateGas := trivial, accountReads := trivial,
    storageReads := trivial, storageWrites := trivial, touchedAccounts := trivial }

/-- The state-writer frame implies the pre-existing `SSTORE` balance fact. -/
lemma Devm.StateWriteFrame.getBal_eq {d d' : Devm}
    (h : Devm.StateWriteFrame d d') (adr : Adr) :
    d.getBal adr = d'.getBal adr := by
  have hstate : State.BalCodeEq d.state d'.state := h.state
  unfold State.BalCodeEq at hstate
  exact congrArg Prod.fst (congrFun hstate adr)

/-- The state-writer frame implies the pre-existing `SSTORE` code fact. -/
lemma Devm.StateWriteFrame.getCode_eq {d d' : Devm}
    (h : Devm.StateWriteFrame d d') (adr : Adr) :
    d.getCode adr = d'.getCode adr := by
  have hstate : State.BalCodeEq d.state d'.state := h.state
  unfold State.BalCodeEq at hstate
  exact congrArg Prod.snd (congrFun hstate adr)

lemma Devm.setStorVal_stateWriteFrame (d : Devm)
    (adr : Adr) (key value : B256) :
    Devm.StateWriteFrame d (d.setStorVal adr key value) := by
  exact {
    stack := trivial, memory := trivial, gasLeft := trivial, logs := trivial
    refundCounter := trivial, output := trivial, accountsToDelete := rfl
    returnData := trivial, error := trivial, accessedAddresses := trivial
    accessedStorageKeys := trivial, state := by
      change State.BalCodeEq d.state (d.state.setStorVal adr key value)
      exact State.setStorVal_balCodeEq d.state adr key value
    createdAccounts := rfl, transientStorage := rfl
    stateGas := trivial, accountReads := trivial,
    storageReads := trivial, storageWrites := trivial, touchedAccounts := trivial }

lemma Devm.transientWriteFrame_of_world_eq {d d' : Devm}
    (hdel : d.accountsToDelete = d'.accountsToDelete)
    (hstate : d.state = d'.state)
    (hcreated : d.createdAccounts = d'.createdAccounts)
    (hwrites : d.world.storageWrites = d'.world.storageWrites) :
    Devm.TransientWriteFrame d d' := by
  exact {
    stack := trivial, memory := trivial, gasLeft := trivial, logs := trivial
    refundCounter := trivial, output := trivial, accountsToDelete := hdel
    returnData := trivial, error := trivial, accessedAddresses := trivial
    accessedStorageKeys := trivial, state := hstate
    createdAccounts := hcreated, transientStorage := trivial
    stateGas := trivial, accountReads := trivial,
    storageReads := trivial, storageWrites := hwrites, touchedAccounts := trivial }

lemma Rinst.tstore_runCore_transientWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.TransientWriteFrame pre
      (Rinst.runCore pc pre sevm .tstore) := by
  simp only [Rinst.runCore]
  split
  · cases hgas : sevm.benvStat.rules.stateGas with
    | none =>
      dsimp only
      refine Outcome.Rel.bindExecution Devm.transientWriteFrame_trans
        (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
          (Devm.pop_instructionFrame pre)) (next := fun key d => do
            let ⟨value, d⟩ ← d.pop
            let d ← chargeGas gasWarmAccess d
            assertDynamic sevm d
            .ok (d.setTransVal sevm.currentTarget key value)) ?_
      intro key d
      refine Outcome.Rel.bindExecution Devm.transientWriteFrame_trans
        (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
          (Devm.pop_instructionFrame d)) (next := fun value d => do
            let d ← chargeGas gasWarmAccess d
            assertDynamic sevm d
            .ok (d.setTransVal sevm.currentTarget key value)) ?_
      intro value d
      apply Execution.Rel.bind Devm.transientWriteFrame_trans
        (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
          (chargeGas_instructionFrame gasWarmAccess d))
      intro d'
      unfold assertDynamic Except.assert
      split
      · exact Devm.transientWriteFrame_of_world_eq rfl rfl rfl rfl
      · exact Devm.transientWriteFrame_refl d'
    | some state =>
      dsimp only
      unfold assertDynamic Except.assert
      split
      · simp only [Except.bind_ok]
        refine Outcome.Rel.bindExecution Devm.transientWriteFrame_trans
          (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
            (Devm.pop_instructionFrame pre)) (next := fun key d => do
              let ⟨value, d⟩ ← d.pop
              let d ← chargeGas gasWarmAccess d
              .ok (d.setTransVal sevm.currentTarget key value)) ?_
        intro key d
        refine Outcome.Rel.bindExecution Devm.transientWriteFrame_trans
          (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
            (Devm.pop_instructionFrame d)) (next := fun value d => do
              let d ← chargeGas gasWarmAccess d
              .ok (d.setTransVal sevm.currentTarget key value)) ?_
        intro value d
        apply Execution.Rel.bind Devm.transientWriteFrame_trans
          (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
            (chargeGas_instructionFrame gasWarmAccess d))
        intro d'
        exact Devm.transientWriteFrame_of_world_eq rfl rfl rfl rfl
      · exact Devm.transientWriteFrame_refl pre
  · exact Devm.transientWriteFrame_refl pre

lemma Rinst.sstore_runCore_stateWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.StateWriteFrame pre
      (Rinst.runCore pc pre sevm .sstore) := by
  simp only [Rinst.runCore]
  cases hgas : sevm.benvStat.rules.stateGas with
  | none =>
      dsimp only
      split
      · refine Outcome.Rel.bindExecution Devm.stateWriteFrame_trans
          (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
            (Devm.pop_instructionFrame pre)) (next := fun key d => do
              let ⟨value, d⟩ ← d.pop
              .assert (gCallStipend < d.gasLeft) ⟨.halt (.outOfGas .none), d⟩
              let ct := sevm.currentTarget
              let original := d.getOrigStorVal sevm ct key
              let d := Devm.balReadStorage sevm.benvStat.rules ct key d
              let current := d.getStorVal ct key
              let ⟨d3, gas2⟩ ← .ok <|
                if (ct, key) ∉ d.accessedStorageKeys then
                  (addAccessedStorageKey d ct key, gasColdSload) else (d, 0)
              let gas3 ← .ok <|
                if original = current ∧ current ≠ value then
                  if original = 0 then gas2 + gasStorageSet
                  else gas2 + (gasStorageUpdate - gasColdSload)
                else gas2 + gasWarmAccess
              let d4 ← .ok <| d3.withRefundCounter
                (sstoreNewRefundCounter sevm.benvStat.rules.gas value original
                  current d3.refundCounter)
              let d5 ← chargeGas gas3 d4
              assertDynamic sevm d5
              .ok ((Devm.balReadAccount sevm.benvStat.rules ct d5).setStorVal
                ct key value)) ?_
        intro key d
        refine Outcome.Rel.bindExecution Devm.stateWriteFrame_trans
          (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
            (Devm.pop_instructionFrame d)) (next := fun value d => do
              .assert (gCallStipend < d.gasLeft) ⟨.halt (.outOfGas .none), d⟩
              let ct := sevm.currentTarget
              let original := d.getOrigStorVal sevm ct key
              let d := Devm.balReadStorage sevm.benvStat.rules ct key d
              let current := d.getStorVal ct key
              let ⟨d3, gas2⟩ ← .ok <|
                if (ct, key) ∉ d.accessedStorageKeys then
                  (addAccessedStorageKey d ct key, gasColdSload) else (d, 0)
              let gas3 ← .ok <|
                if original = current ∧ current ≠ value then
                  if original = 0 then gas2 + gasStorageSet
                  else gas2 + (gasStorageUpdate - gasColdSload)
                else gas2 + gasWarmAccess
              let d4 ← .ok <| d3.withRefundCounter
                (sstoreNewRefundCounter sevm.benvStat.rules.gas value original
                  current d3.refundCounter)
              let d5 ← chargeGas gas3 d4
              assertDynamic sevm d5
              .ok ((Devm.balReadAccount sevm.benvStat.rules ct d5).setStorVal
                ct key value)) ?_
        intro value d
        unfold Except.assert
        dsimp only
        split
        · simp only [Except.bind_ok]
          let d2 : Devm :=
            Devm.balReadStorage sevm.benvStat.rules sevm.currentTarget key d
          let d3gas : Devm × Nat :=
            if (sevm.currentTarget, key) ∉ d2.accessedStorageKeys then
              (addAccessedStorageKey d2 sevm.currentTarget key, gasColdSload)
            else (d2, 0)
          let gas3 :=
            if d.getOrigStorVal sevm sevm.currentTarget key =
                d2.getStorVal sevm.currentTarget key ∧
                d2.getStorVal sevm.currentTarget key ≠ value then
              if d.getOrigStorVal sevm sevm.currentTarget key = 0 then
                d3gas.2 + gasStorageSet
              else d3gas.2 + (gasStorageUpdate - gasColdSload)
            else d3gas.2 + gasWarmAccess
          let d4 : Devm := d3gas.1.withRefundCounter (
            sstoreNewRefundCounter sevm.benvStat.rules.gas value
              (d.getOrigStorVal sevm sevm.currentTarget key)
              (d2.getStorVal sevm.currentTarget key) d3gas.1.refundCounter)
          change Execution.Rel Devm.StateWriteFrame d
            (chargeGas gas3 d4 >>= fun d5 =>
              assertDynamic sevm d5 >>= fun _ =>
                .ok ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
                  d5).setStorVal sevm.currentTarget key value))
          have hd4 : Devm.StateWriteFrame d d4 := by
            have h2 : Devm.StateWriteFrame d d2 :=
              Devm.instructionFrame_refines_stateWriteFrame
                (Devm.balReadStorage_instructionFrame sevm.benvStat.rules
                  sevm.currentTarget key d)
            have h3 : Devm.StateWriteFrame d2 d3gas.1 := by
              unfold d3gas
              split <;> exact Devm.stateWriteFrame_of_world_eq rfl rfl rfl rfl
            exact Devm.stateWriteFrame_trans (Devm.stateWriteFrame_trans h2 h3)
              (Devm.stateWriteFrame_of_world_eq rfl rfl rfl rfl)
          apply Execution.Rel.bind Devm.stateWriteFrame_trans
            (Execution.Rel.trans_left Devm.stateWriteFrame_trans hd4
              (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
                (chargeGas_instructionFrame gas3 d4)))
          intro d5
          unfold assertDynamic Except.assert
          split
          · apply Execution.Rel.trans_left Devm.stateWriteFrame_trans
              (Devm.instructionFrame_refines_stateWriteFrame
                (Devm.balReadAccount_instructionFrame sevm.benvStat.rules
                  sevm.currentTarget d5))
            exact Devm.setStorVal_stateWriteFrame _ _ _ _
          · exact Devm.stateWriteFrame_refl d5
        · exact Devm.stateWriteFrame_refl d
      · refine Outcome.Rel.bindExecution Devm.stateWriteFrame_trans
          (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
            (Devm.pop_instructionFrame pre)) (next := fun key d => do
              let ⟨value, d⟩ ← d.pop
              .assert (sevm.benvStat.rules.sstore.stipendSentry → gCallStipend < d.gasLeft) ⟨.halt (.outOfGas .none), d⟩
              let ct := sevm.currentTarget
              let original := d.getOrigStorVal sevm ct key
              let d := Devm.balReadStorage sevm.benvStat.rules ct key d
              let current := d.getStorVal ct key
              let ⟨d3, gas2⟩ ← .ok <|
                match sevm.benvStat.rules.access with
                | .flat _ => (d, 0)
                | .eip2929 => if (ct, key) ∉ d.accessedStorageKeys then
                    (addAccessedStorageKey d ct key, gasColdSload) else (d, 0)
              let gas3 ← .ok <|
                sstoreRegimeGasCost sevm.benvStat.rules.sstore
                  sevm.benvStat.rules.access gas2 value original current
              let d4 ← .ok <| d3.withRefundCounter
                (match sevm.benvStat.rules.sstore.netMetering, sevm.benvStat.rules.access with
                | false, _ => sstoreLegacyRefundCounter sevm.benvStat.rules.gas value original current d3.refundCounter
                | true, .flat g => sstoreFlatRefundCounter sevm.benvStat.rules.gas g.sload value original current d3.refundCounter
                | true, .eip2929 => sstoreNewRefundCounter sevm.benvStat.rules.gas value original current d3.refundCounter)
              let d5 ← chargeGas gas3 d4
              assertDynamic sevm d5
              .ok ((Devm.balReadAccount sevm.benvStat.rules ct d5).setStorVal
                ct key value)) ?_
        intro key d
        refine Outcome.Rel.bindExecution Devm.stateWriteFrame_trans
          (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
            (Devm.pop_instructionFrame d)) (next := fun value d => do
              .assert (sevm.benvStat.rules.sstore.stipendSentry → gCallStipend < d.gasLeft) ⟨.halt (.outOfGas .none), d⟩
              let ct := sevm.currentTarget
              let original := d.getOrigStorVal sevm ct key
              let d := Devm.balReadStorage sevm.benvStat.rules ct key d
              let current := d.getStorVal ct key
              let ⟨d3, gas2⟩ ← .ok <|
                match sevm.benvStat.rules.access with
                | .flat _ => (d, 0)
                | .eip2929 => if (ct, key) ∉ d.accessedStorageKeys then
                    (addAccessedStorageKey d ct key, gasColdSload) else (d, 0)
              let gas3 ← .ok <|
                sstoreRegimeGasCost sevm.benvStat.rules.sstore
                  sevm.benvStat.rules.access gas2 value original current
              let d4 ← .ok <| d3.withRefundCounter
                (match sevm.benvStat.rules.sstore.netMetering, sevm.benvStat.rules.access with
                | false, _ => sstoreLegacyRefundCounter sevm.benvStat.rules.gas value original current d3.refundCounter
                | true, .flat g => sstoreFlatRefundCounter sevm.benvStat.rules.gas g.sload value original current d3.refundCounter
                | true, .eip2929 => sstoreNewRefundCounter sevm.benvStat.rules.gas value original current d3.refundCounter)
              let d5 ← chargeGas gas3 d4
              assertDynamic sevm d5
              .ok ((Devm.balReadAccount sevm.benvStat.rules ct d5).setStorVal
                ct key value)) ?_
        intro value d
        unfold Except.assert
        dsimp only
        split
        · simp only [Except.bind_ok]
          let d2 : Devm :=
            Devm.balReadStorage sevm.benvStat.rules sevm.currentTarget key d
          let d3gas : Devm × Nat :=
            match sevm.benvStat.rules.access with
            | .flat _ => (d2, 0)
            | .eip2929 => if (sevm.currentTarget, key) ∉ d2.accessedStorageKeys then
                (addAccessedStorageKey d2 sevm.currentTarget key, gasColdSload)
              else (d2, 0)
          let gas3 := sstoreRegimeGasCost sevm.benvStat.rules.sstore
            sevm.benvStat.rules.access d3gas.2 value
            (d.getOrigStorVal sevm sevm.currentTarget key)
            (d2.getStorVal sevm.currentTarget key)
          let d4 : Devm := d3gas.1.withRefundCounter (
            match sevm.benvStat.rules.sstore.netMetering, sevm.benvStat.rules.access with
            | false, _ => sstoreLegacyRefundCounter sevm.benvStat.rules.gas value
                (d.getOrigStorVal sevm sevm.currentTarget key)
                (d2.getStorVal sevm.currentTarget key) d3gas.1.refundCounter
            | true, .flat g => sstoreFlatRefundCounter sevm.benvStat.rules.gas g.sload value
                (d.getOrigStorVal sevm sevm.currentTarget key)
                (d2.getStorVal sevm.currentTarget key) d3gas.1.refundCounter
            | true, .eip2929 => sstoreNewRefundCounter sevm.benvStat.rules.gas value
                (d.getOrigStorVal sevm sevm.currentTarget key)
                (d2.getStorVal sevm.currentTarget key) d3gas.1.refundCounter)
          change Execution.Rel Devm.StateWriteFrame d
            (chargeGas gas3 d4 >>= fun d5 =>
              assertDynamic sevm d5 >>= fun _ =>
                .ok ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
                  d5).setStorVal sevm.currentTarget key value))
          have hd4 : Devm.StateWriteFrame d d4 := by
            have h2 : Devm.StateWriteFrame d d2 :=
              Devm.instructionFrame_refines_stateWriteFrame
                (Devm.balReadStorage_instructionFrame sevm.benvStat.rules
                  sevm.currentTarget key d)
            have h3 : Devm.StateWriteFrame d2 d3gas.1 := by
              unfold d3gas
              cases haccess : sevm.benvStat.rules.access with
              | flat gas => exact Devm.stateWriteFrame_refl d2
              | eip2929 =>
                dsimp only
                split <;> exact Devm.stateWriteFrame_of_world_eq rfl rfl rfl rfl
            exact Devm.stateWriteFrame_trans (Devm.stateWriteFrame_trans h2 h3)
              (Devm.stateWriteFrame_of_world_eq rfl rfl rfl rfl)
          apply Execution.Rel.bind Devm.stateWriteFrame_trans
            (Execution.Rel.trans_left Devm.stateWriteFrame_trans hd4
              (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
                (chargeGas_instructionFrame gas3 d4)))
          intro d5
          unfold assertDynamic Except.assert
          split
          · apply Execution.Rel.trans_left Devm.stateWriteFrame_trans
              (Devm.instructionFrame_refines_stateWriteFrame
                (Devm.balReadAccount_instructionFrame sevm.benvStat.rules
                  sevm.currentTarget d5))
            exact Devm.setStorVal_stateWriteFrame _ _ _ _
          · exact Devm.stateWriteFrame_refl d5
        · exact Devm.stateWriteFrame_refl d

  | some state =>
      dsimp only
      unfold assertDynamic Except.assert
      split
      · simp only [Except.bind_ok]
        refine Outcome.Rel.bindExecution Devm.stateWriteFrame_trans
          (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
            (Devm.pop_instructionFrame pre)) (next := fun key d => do
              let ⟨value, d⟩ ← d.pop
              let ct := sevm.currentTarget
              let cold := (ct, key) ∉ d.accessedStorageKeys
              let accessGas := if cold then gasColdSload else gasWarmAccess
              .assert (max accessGas (gCallStipend + 1) ≤ d.gasLeft)
                ⟨.halt (.outOfGas .none), d⟩
              let d := if cold then addAccessedStorageKey d ct key else d
              let original := d.getOrigStorVal sevm ct key
              let d := Devm.balReadStorage sevm.benvStat.rules ct key d
              let current := d.getStorVal ct key
              let d := d.withRefundCounter (sstoreAmsterdamRefundCounter
                sevm.benvStat.rules.gas state value original current
                d.refundCounter)
              let d := Devm.creditStateGasRefund (sstoreAmsterdamStateRefund
                state value original current) d
              let d ← chargeGas (sstoreAmsterdamGasCost state value original
                current cold) d
              let d ← chargeStateGas (sstoreAmsterdamStateGas state value
                original current) d
              .ok ((Devm.balReadAccount sevm.benvStat.rules ct d).setStorVal
                ct key value)) ?_
        intro key d
        refine Outcome.Rel.bindExecution Devm.stateWriteFrame_trans
          (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
            (Devm.pop_instructionFrame d)) (next := fun value d => do
              let ct := sevm.currentTarget
              let cold := (ct, key) ∉ d.accessedStorageKeys
              let accessGas := if cold then gasColdSload else gasWarmAccess
              .assert (max accessGas (gCallStipend + 1) ≤ d.gasLeft)
                ⟨.halt (.outOfGas .none), d⟩
              let d := if cold then addAccessedStorageKey d ct key else d
              let original := d.getOrigStorVal sevm ct key
              let d := Devm.balReadStorage sevm.benvStat.rules ct key d
              let current := d.getStorVal ct key
              let d := d.withRefundCounter (sstoreAmsterdamRefundCounter
                sevm.benvStat.rules.gas state value original current
                d.refundCounter)
              let d := Devm.creditStateGasRefund (sstoreAmsterdamStateRefund
                state value original current) d
              let d ← chargeGas (sstoreAmsterdamGasCost state value original
                current cold) d
              let d ← chargeStateGas (sstoreAmsterdamStateGas state value
                original current) d
              .ok ((Devm.balReadAccount sevm.benvStat.rules ct d).setStorVal
                ct key value)) ?_
        intro value d
        unfold Except.assert
        dsimp only
        by_cases hacc : max (if (sevm.currentTarget, key) ∉ d.accessedStorageKeys
            then gasColdSload else gasWarmAccess) (gCallStipend + 1) ≤ d.gasLeft
        · simp only [ite_eq_left hacc, Except.bind_ok]
          let cold :=
            (sevm.currentTarget, key) ∉ d.accessedStorageKeys
          let d2 : Devm := if cold then
            addAccessedStorageKey d sevm.currentTarget key else d
          let d3 : Devm := Devm.balReadStorage sevm.benvStat.rules
            sevm.currentTarget key d2
          let d4 : Devm := d3.withRefundCounter (sstoreAmsterdamRefundCounter
            sevm.benvStat.rules.gas state value
            (d2.getOrigStorVal sevm sevm.currentTarget key)
            (d3.getStorVal sevm.currentTarget key) d3.refundCounter)
          let d5 : Devm := Devm.creditStateGasRefund (sstoreAmsterdamStateRefund
            state value (d2.getOrigStorVal sevm sevm.currentTarget key)
            (d3.getStorVal sevm.currentTarget key)) d4
          change Execution.Rel Devm.StateWriteFrame d
            (chargeGas (sstoreAmsterdamGasCost state value
              (d2.getOrigStorVal sevm sevm.currentTarget key)
              (d3.getStorVal sevm.currentTarget key) cold) d5 >>= fun d6 =>
              chargeStateGas (sstoreAmsterdamStateGas state value
                (d2.getOrigStorVal sevm sevm.currentTarget key)
                (d3.getStorVal sevm.currentTarget key)) d6 >>= fun d7 =>
                .ok ((Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
                  d7).setStorVal sevm.currentTarget key value))
          have hd5 : Devm.StateWriteFrame d d5 := by
            have h3 : Devm.StateWriteFrame d d3 := by
              unfold d3 d2 cold
              split
              · exact Devm.stateWriteFrame_trans
                  (Devm.stateWriteFrame_of_world_eq (d := d)
                    (d' := addAccessedStorageKey d sevm.currentTarget key)
                    rfl rfl rfl rfl)
                  (Devm.instructionFrame_refines_stateWriteFrame
                    (Devm.balReadStorage_instructionFrame sevm.benvStat.rules
                      sevm.currentTarget key
                      (addAccessedStorageKey d sevm.currentTarget key)))
              · exact Devm.instructionFrame_refines_stateWriteFrame
                  (Devm.balReadStorage_instructionFrame sevm.benvStat.rules
                    sevm.currentTarget key d)
            have h4 : Devm.StateWriteFrame d3 d4 :=
              Devm.stateWriteFrame_of_world_eq rfl rfl rfl rfl
            have h5 : Devm.StateWriteFrame d4 d5 :=
              Devm.instructionFrame_refines_stateWriteFrame
                (Devm.machFrame_refines_instructionFrame
                  (Devm.machFrame_setMach d4 _))
            exact Devm.stateWriteFrame_trans h3
              (Devm.stateWriteFrame_trans h4 h5)
          apply Execution.Rel.bind Devm.stateWriteFrame_trans
            (Execution.Rel.trans_left Devm.stateWriteFrame_trans hd5
              (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
                (chargeGas_instructionFrame _ d5)))
          intro d6
          apply Execution.Rel.bind Devm.stateWriteFrame_trans
            (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
              (chargeStateGas_instructionFrame _ d6))
          intro d7
          apply Execution.Rel.trans_left Devm.stateWriteFrame_trans
            (Devm.instructionFrame_refines_stateWriteFrame
              (Devm.balReadAccount_instructionFrame sevm.benvStat.rules
                sevm.currentTarget d7))
          exact Devm.setStorVal_stateWriteFrame _ _ _ _
        · simp only [ite_eq_right hacc]
          exact Devm.stateWriteFrame_refl d
      · exact Devm.stateWriteFrame_refl pre

theorem Rinst.run_instructionFrame
    (pc : Nat) (sevm : Sevm) (pre : Devm) (r : Rinst)
    (h_not_sstore : r ≠ .sstore) (h_not_tstore : r ≠ .tstore) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.run ⟨pc, sevm, pre⟩ r) := by
  exact Rinst.runCore_instructionFrame pc sevm pre r
    h_not_sstore h_not_tstore

lemma Rinst.sstore_run_stateWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.StateWriteFrame pre
      (Rinst.run ⟨pc, sevm, pre⟩ .sstore) := by
  exact Rinst.sstore_runCore_stateWriteFrame pc pre sevm

lemma Rinst.tstore_run_transientWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.TransientWriteFrame pre
      (Rinst.run ⟨pc, sevm, pre⟩ .tstore) := by
  exact Rinst.tstore_runCore_transientWriteFrame pc pre sevm

/-- Jump instructions keep the instruction frame (Jaune's `Jinst.runCore_worldFrame`). -/
theorem Jinst.runCore_instructionFrame
    (pc : Nat) (sevm : Sevm) (pre : Devm) (j : Jinst) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame pre
      (Jinst.runCore pc pre sevm j) := by
  have h := Jinst.runCore_worldFrame pc sevm pre j
  cases hx : Jinst.runCore pc pre sevm j <;> rw [hx] at h <;>
    exact Devm.WorldFrame.instructionFrame h

theorem Jinst.run_instructionFrame (evm : Evm) (j : Jinst) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame evm.dyna
      (Jinst.run evm j) := by
  exact Jinst.runCore_instructionFrame evm.pc evm.sta evm.dyna j

/-- The halting instructions other than `SELFDESTRUCT` keep the instruction
frame (Jaune's `Linst.run_worldFrame`). -/
theorem Linst.run_instructionFrame
    (sevm : Sevm) (pre : Devm) (l : Linst) (h_not_selfdestruct : l ≠ .selfdestruct) :
    Execution.Rel Devm.InstructionFrame pre (Linst.run sevm pre l) :=
  Execution.Rel.of_worldFrame (Linst.run_worldFrame sevm pre l h_not_selfdestruct)

def Execution.getCode : Execution → Adr → ByteArray
  | Except.error ⟨_, devm⟩, adr => devm.getCode adr
  | Except.ok devm, adr => devm.getCode adr

/-- The created-account set carried by either raw execution outcome. -/
def Execution.createdAccounts : Execution → AdrSet
  | .ok d => d.createdAccounts
  | .error (_, d) => d.createdAccounts

lemma Rinst.run_code_created {pc sevm devm r exn}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = exn) (a : Adr) :
    Execution.getCode exn a = devm.getCode a ∧
      Execution.createdAccounts exn = devm.createdAccounts := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm
    rw [run] at hf
    cases exn <;> exact ⟨(hf.getCode_eq a).symm, hf.createdAccounts.symm⟩
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm
    rw [run] at hf
    cases exn <;> refine ⟨?_, hf.createdAccounts.symm⟩ <;>
      simpa only [Execution.getCode, Devm.getCode, Devm.getAcct, id_eq] using
        congrFun (congrArg (fun st => fun address => (st.get address).code) hf.state).symm a
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht
    rw [run] at hf
    cases exn <;> exact ⟨(hf.getCode a).symm, hf.createdAccounts.symm⟩

lemma Rinst.preserves_getCode
    {pc sevm devm r devm'}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = .ok devm') (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  exact (Rinst.run_code_created run a).1

lemma chargeStateGas_getCode_gen {amount devm exn} (h : chargeStateGas amount devm = exn) (a : Adr) : Execution.getCode exn a = devm.getCode a := by
  cases exn with
  | error err => exact (chargeStateGas_worldEq_of_error h).getCode a |>.symm
  | ok devm' => exact (chargeStateGas_worldEq_of_ok h).getCode a |>.symm

lemma chargeGas_getCode_gen {cost devm exn} (h : chargeGas cost devm = exn) (a : Adr) : Execution.getCode exn a = devm.getCode a := by
  cases exn with
  | error err => exact (chargeGas_worldEq_of_error h).getCode a |>.symm
  | ok devm' => exact (chargeGas_worldEq_of_ok h).getCode a |>.symm

lemma processCreateMessage.chargeCodeGas_getCode_gen {rules : ForkRules}
    {evm : Devm} {exn : Execution}
    (h : processCreateMessage.chargeCodeGas rules evm = exn) (a : Adr) :
    Execution.getCode exn a = evm.getCode a := by
  simp only [processCreateMessage.chargeCodeGas] at h
  split at h
  · split at h
    · split at h
      · subst h; rfl
      · dsimp only [ExceptT.stM_eq, bind, Except.bind] at h
        split at h
        · rename_i eq_err; subst h
          have h_charge := chargeGas_getCode_gen eq_err a
          exact h_charge
        · rename_i eq_ok; split at h
          · subst h
            have h_charge := chargeGas_getCode_eq eq_ok a
            exact h_charge
          · subst h
            have h_charge := chargeGas_getCode_eq eq_ok a
            exact h_charge
    · dsimp only [ExceptT.stM_eq, bind, Except.bind] at h
      split at h
      · rename_i eq_err; subst h
        have h_charge := chargeGas_getCode_gen eq_err a
        exact h_charge
      · rename_i eq_ok; split at h
        · subst h
          have h_charge := chargeGas_getCode_eq eq_ok a
          exact h_charge
        · subst h
          have h_charge := chargeGas_getCode_eq eq_ok a
          exact h_charge
  · split at h
    · subst h; rfl
    · split at h
      · subst h; rfl
      · cases hcg : chargeGas
            (gasKeccak256Word * ceilDiv evm.output.length 32) evm with
        | error err =>
            simp only [hcg, Except.bind_error] at h
            subst h
            exact chargeGas_getCode_gen hcg a
        | ok devm' =>
            simp only [hcg, Except.bind_ok] at h
            exact (chargeStateGas_getCode_gen h a).trans
              (chargeGas_getCode_eq hcg a)

/-- Code-deposit charging preserves the coarse instruction frame on either
outcome, including forks that accept the EF prefix and state-gas charging. -/
lemma processCreateMessage.chargeCodeGas_instructionFrame (rules : ForkRules)
    (pre : Devm) : Execution.Rel Devm.InstructionFrame pre
      (processCreateMessage.chargeCodeGas rules pre) := by
  generalize h : processCreateMessage.chargeCodeGas rules pre = out
  simp only [processCreateMessage.chargeCodeGas] at h
  split at h
  · split at h
    · split at h
      · subst h; exact Devm.instructionFrame_refl pre
      · dsimp only [ExceptT.stM_eq, bind, Except.bind] at h
        split at h
        · rename_i hc; subst h
          have hf := chargeGas_instructionFrame (pre.output.length * gasCodeDeposit) pre
          rw [hc] at hf
          exact hf
        · rename_i hc; split at h
          · subst h
            have hf := chargeGas_instructionFrame (pre.output.length * gasCodeDeposit) pre
            rw [hc] at hf
            exact hf
          · subst h
            have hf := chargeGas_instructionFrame (pre.output.length * gasCodeDeposit) pre
            rw [hc] at hf
            exact hf
    · dsimp only [ExceptT.stM_eq, bind, Except.bind] at h
      split at h
      · rename_i hc; subst h
        have hf := chargeGas_instructionFrame (pre.output.length * gasCodeDeposit) pre
        rw [hc] at hf
        exact hf
      · rename_i hc; split at h
        · subst h
          have hf := chargeGas_instructionFrame (pre.output.length * gasCodeDeposit) pre
          rw [hc] at hf
          exact hf
        · subst h
          have hf := chargeGas_instructionFrame (pre.output.length * gasCodeDeposit) pre
          rw [hc] at hf
          exact hf
  · split at h
    · subst h; exact Devm.instructionFrame_refl pre
    · split at h
      · subst h; exact Devm.instructionFrame_refl pre
      · cases hcg : chargeGas
            (gasKeccak256Word * ceilDiv pre.output.length 32) pre with
        | error err =>
            simp only [hcg, Except.bind_error] at h
            subst h
            have hf := chargeGas_instructionFrame (gasKeccak256Word * ceilDiv pre.output.length 32) pre
            rw [hcg] at hf
            exact hf
        | ok mid =>
            simp only [hcg, Except.bind_ok] at h
            have hg := chargeGas_instructionFrame (gasKeccak256Word * ceilDiv pre.output.length 32) pre
            rw [hcg] at hg
            have hs : Execution.Rel Devm.InstructionFrame mid out := by
              rw [← h]
              exact chargeStateGas_instructionFrame _ _
            cases out <;> exact Devm.instructionFrame_trans hg hs

lemma Devm.push_getCode_gen {v devm} {exn : Execution} (h : Devm.push v devm = exn) (a : Adr) : Execution.getCode exn a = devm.getCode a := by
  subst h
  cases hp : Devm.push v devm with
  | error err =>
    exact (liftMachExecution_worldEq_of_error (core := Mach.push v) hp).getCode a |>.symm
  | ok d =>
    exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) hp).getCode a |>.symm


lemma Devm.push_createdAccounts_eq {value : B256} {pre : Devm} {out : Execution}
    (h : pre.push value = out) : Execution.createdAccounts out = pre.createdAccounts := by
  have frame := Devm.push_instructionFrame value pre
  rw [h] at frame
  cases out <;> exact frame.createdAccounts.symm

lemma Devm.popToAdr_createdAccounts_eq {d d' : Devm} {a : Adr}
    (h : d.popToAdr = .ok (a, d')) : d'.createdAccounts = d.createdAccounts := by
  have frame := Devm.popToAdr_instructionFrame d
  rw [h] at frame
  exact frame.createdAccounts.symm

lemma Devm.popToAdr_createdAccounts_err {d : Devm} {e : EvmError × Devm}
    (h : d.popToAdr = .error e) : e.2.createdAccounts = d.createdAccounts := by
  have frame := Devm.popToAdr_instructionFrame d
  rw [h] at frame
  exact frame.createdAccounts.symm

lemma chargeGas_createdAccounts_eq {cost : Nat} {d : Devm} {out : Execution}
    (h : chargeGas cost d = out) : Execution.createdAccounts out = d.createdAccounts := by
  have frame := chargeGas_instructionFrame cost d
  rw [h] at frame
  cases out <;> exact frame.createdAccounts.symm

lemma chargeStateGas_createdAccounts_eq {amount : Nat} {d : Devm} {out : Execution}
    (h : chargeStateGas amount d = out) :
    Execution.createdAccounts out = d.createdAccounts := by
  have frame := chargeStateGas_instructionFrame amount d
  rw [h] at frame
  cases out <;> exact frame.createdAccounts.symm

lemma Devm.subBal_createdAccounts_eq {d d' : Devm} {a : Adr} {v : B256}
    (h : d.subBal a v = some d') : d'.createdAccounts = d.createdAccounts := by
  dsimp only [Devm.subBal, Option.bind_eq_bind] at h
  cases state : d.state.subBal a v with
  | none => rw [state] at h; contradiction
  | some st =>
    rw [state] at h
    dsimp only [Option.bind_some] at h
    cases h
    rfl

def Xlot.InvGetCode : Xlot → Prop
  | .none => True
  | .some ⟨evm, exn⟩ =>
    ∀ adr,
      (evm.dyna.getCode adr).toList ≠ [] →
      evm.dyna.getCode adr = Execution.getCode exn adr

lemma applyPrecompResult_code_created (evm : Evm) (res : PrecompResult) (ex : Execution)
    (h_ex : applyPrecompResult evm res = ex) (a : Adr) :
    Execution.getCode ex a = evm.dyna.getCode a ∧
      Execution.createdAccounts ex = evm.dyna.createdAccounts := by
  revert h_ex
  cases res <;> (intro h_ex; subst h_ex; exact ⟨rfl, rfl⟩)

lemma applyPrecompResult_getCode (evm : Evm) (res : PrecompResult) (ex : Execution)
    (h_ex : applyPrecompResult evm res = ex) (a : Adr) :
    Execution.getCode ex a = evm.dyna.getCode a := by
  exact (applyPrecompResult_code_created evm res ex h_ex a).1

lemma executePrecomp_preserves_getCode (evm : Evm) (adr : Adr) (ex : Execution)
    (h_ex : executePrecomp evm adr = ex) (a : Adr) :
    Execution.getCode ex a = evm.dyna.getCode a := by
  apply applyPrecompResult_getCode evm (precompileRun evm adr) ex h_ex a

def MsgResult.getCode (exn : Except (EvmError × State × AdrSet × Tra) Devm) (a : Adr) : ByteArray :=
  match exn with
  | .ok d => d.getCode a
  | .error ⟨_, state, _, _⟩ => state.getCode a

def MsgResult.createdAccounts : Except (EvmError × State × AdrSet × Tra) Devm → AdrSet
  | .ok d => d.createdAccounts
  | .error (_, _, created, _) => created

/-- Shared proof mode: code-only compatibility, or code plus created exclusion. -/
def Xlot.InvAccountPreserve (track : Bool) : Xlot → Prop
  | .none => True
  | .some (evm, out) => ∀ a, (evm.dyna.getCode a).toList ≠ [] →
      Execution.getCode out a = evm.dyna.getCode a ∧
      (track = true → a ∉ evm.dyna.createdAccounts → a ∉ Execution.createdAccounts out)

lemma Xlot.invAccountPreserve_false {xl : Xlot} (h : Xlot.InvGetCode xl) :
    Xlot.InvAccountPreserve false xl := by
  cases xl with
  | none => trivial
  | some pair =>
    intro a code
    exact ⟨(h a code).symm, by intro impossible; cases impossible⟩

def MsgResult.AccountPreserve (track : Bool) (base : Benv)
    (out : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  ∀ a, (base.state.getCode a).toList ≠ [] →
    MsgResult.getCode out a = base.state.getCode a ∧
      (track = true → a ∉ base.createdAccounts → a ∉ MsgResult.createdAccounts out)

def MsgResult.AccountPreserveExcept (track : Bool) (base : Benv) (target : Adr)
    (out : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  ∀ a, a ≠ target → (base.state.getCode a).toList ≠ [] →
    MsgResult.getCode out a = base.state.getCode a ∧
      (track = true → a ∉ base.createdAccounts → a ∉ MsgResult.createdAccounts out)

def Execution.AccountPreserve (track : Bool) (base : Devm) (out : Execution) : Prop :=
  ∀ a, (base.getCode a).toList ≠ [] →
    Execution.getCode out a = base.getCode a ∧
      (track = true → a ∉ base.createdAccounts → a ∉ Execution.createdAccounts out)

lemma chargeGas_getCode_err {cost devm err} (h : chargeGas cost devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (chargeGas_worldEq_of_error h).getCode a |>.symm

lemma chargeStateGas_getCode_err {amount devm err} (h : chargeStateGas amount devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (chargeStateGas_worldEq_of_error h).getCode a |>.symm

lemma Devm.push_getCode_err {v devm err} (h : Devm.push v devm = Except.error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.push v) h).getCode a |>.symm

lemma Devm.popToAdr_getCode_err {devm err} (h : Devm.popToAdr devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_error (core := Mach.popToAdr) h).getCode a |>.symm

lemma Rinst.preserves_getCode_err
    {pc sevm devm r err}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = Except.error err) (a : Adr) :
    err.2.getCode a = devm.getCode a := by
  exact (Rinst.run_code_created run a).1

lemma Rinst.preserves_getCode_gen
    {pc sevm devm r exn}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = exn) (a : Adr)
    (_ne : (devm.getCode a).toList ≠ []) :
    Execution.getCode exn a = devm.getCode a := by
  exact (Rinst.run_code_created run a).1

def JumpResult.getCode (ex : Except (EvmError × Devm) (Nat × Devm)) (a : Adr) : ByteArray :=
  match ex with
  | .ok ⟨_, devm⟩ => devm.getCode a
  | .error ⟨_, devm⟩ => devm.getCode a

lemma Jinst.preserves_getCode_gen
    {pc sevm devm j ex}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j ex) :
    ∀ a : Adr, JumpResult.getCode ex a = devm.getCode a := by
  intro a
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  cases ex <;> exact (hf.getCode a).symm

/-- Crediting a beneficiary preserves every code byte, including historical
credits that preserve account presence instead of erasing empty accounts. -/
lemma Devm.creditBeneficiary_getCode (rules : ForkRules) (donee : Adr)
    (value : B256) (d : Devm) (a : Adr) :
    (d.creditBeneficiary rules donee value).getCode a = d.getCode a := by
  unfold Devm.creditBeneficiary
  split
  · exact State.addBal_getCode d.state donee a value
  · change ((d.state.setPresent donee
      ((d.state.get donee).withBal (d.state.bal donee + value))).get a).code =
        (d.state.get a).code
    by_cases h : donee = a
    · subst a
      rw [State.get_setPresent_self]
      rfl
    · rw [State.get_setPresent_ne _ h]

/-- Refund bookkeeping changes no persistent state. -/
lemma creditSelfdestructRefund_state (rules : ForkRules) (scheduled : Prop)
    [Decidable scheduled] (d : Devm) :
    (creditSelfdestructRefund rules scheduled d).state = d.state := by
  unfold creditSelfdestructRefund
  split <;> rfl

/-- Removing only touched empty accounts preserves every balance. -/
lemma sweepTouchedAccounts_bal (rules : ForkRules) (addresses : List Adr) (state : State) :
    (sweepTouchedAccounts rules addresses state).bal = state.bal := by
  have eraseEmpty (w : State) (a : Adr) (h : accountExistsAndIsEmpty w a) :
      (destroyAccount w a).bal = w.bal := by
    funext b
    change (State.get (w.erase a) b).bal = (w.get b).bal
    rw [State.get_eq_getD, State.getElem?_erase]
    by_cases hab : a = b
    · subst b
      simp only [↓reduceIte, Option.getD_none]
      exact h.2.2.2.symm
    · rw [if_neg hab, State.get_eq_getD]
  unfold sweepTouchedAccounts
  split
  · induction addresses generalizing state with
    | nil => rfl
    | cons a as ih =>
      rw [List.foldl_cons, ih]
      split
      · exact eraseEmpty _ _ (by assumption)
      · rfl
  · rfl

lemma Devm.creditBeneficiary_delSets (rules : ForkRules) (donee : Adr)
    (value : B256) (d : Devm) :
    Devm.delSets (d.creditBeneficiary rules donee value) = Devm.delSets d := by
  unfold Devm.creditBeneficiary
  split <;> rfl

lemma creditSelfdestructRefund_getCode (rules : ForkRules) (scheduled : Prop)
    [Decidable scheduled] (d : Devm) (a : Adr) :
    (creditSelfdestructRefund rules scheduled d).getCode a = d.getCode a := by
  unfold creditSelfdestructRefund
  split <;> rfl

lemma creditSelfdestructRefund_delSets (rules : ForkRules) (scheduled : Prop)
    [Decidable scheduled] (d : Devm) :
    Devm.delSets (creditSelfdestructRefund rules scheduled d) = Devm.delSets d := by
  unfold creditSelfdestructRefund
  split <;> rfl

lemma memRead_getBal_eq {x n : Nat} {devm devm' : Devm} {value : Bytes} (h : devm.memRead x n = ⟨value, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  simp only [Devm.memRead] at h
  rcases h_read : devm.memory.read x n with ⟨val, mem⟩
  rw [h_read] at h
  injection h with _ h_devm
  rw [← h_devm]
  rfl

/-- Successful-run observation invariant retained as the public projection of
the canonical regular-instruction effect theorems. -/
def Rinst.Inv {ξ : Type} (f : Devm → ξ) (r : Rinst) : Prop :=
  ∀ {pc sevm pre post}, Rinst.run ⟨pc, sevm, pre⟩ r = (.ok post) → f pre = f post

lemma Rinst.preserves_bal {r} : Rinst.Inv Devm.getBal r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc pre sevm; rw [hrun] at hf; exact funext hf.getBal_eq
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm; rw [hrun] at hf
    exact congrArg (fun s => s.bal) hf.state
  · have hf := Rinst.run_instructionFrame pc sevm pre r hs ht; rw [hrun] at hf; exact funext hf.getBal

/-- A regular instruction other than the two world-writing stores preserves
the complete persistent world state.  Specific `Hinv` instances below expose
the cases needed by WETH10's shared nonpayable entry wrapper. -/
lemma Rinst.preserves_state {r}
    (h_not_sstore : r ≠ Rinst.sstore)
    (h_not_tstore : r ≠ Rinst.tstore) :
    Rinst.Inv Devm.state r := by
  intro pc sevm pre post hrun
  have hf := Rinst.run_instructionFrame pc sevm pre r
    h_not_sstore h_not_tstore
  rw [hrun] at hf
  exact hf.state

lemma memRead_getStor_eq {x n : Nat} {devm devm' : Devm} {value : Bytes}
    (h : devm.memRead x n = ⟨value, devm'⟩) :
    Devm.getStor devm' = Devm.getStor devm := by
  simp only [Devm.memRead] at h
  rcases h_read : devm.memory.read x n with ⟨val, mem⟩
  rw [h_read] at h
  injection h with _ h_devm
  rw [← h_devm]
  rfl

lemma Rinst.preserves_stor {r} (h_not_sstore : r ≠ Rinst.sstore) : Rinst.Inv Devm.getStor r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm; rw [hrun] at hf
    exact congrArg (fun s => fun a => (s.get a).stor) hf.state
  · have hf := Rinst.run_instructionFrame pc sevm pre r h_not_sstore ht; rw [hrun] at hf
    exact funext (Devm.InstructionFrame.getStor hf)

end Blanc
