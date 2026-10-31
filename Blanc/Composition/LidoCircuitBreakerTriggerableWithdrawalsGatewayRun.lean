import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewayCrossing
import Jaune.DevmProjections

/-!
# One generic executed pause-world run for the CircuitBreaker × gateway composition

The stub-duration control (`LidoCircuitBreakerTriggerableWithdrawalsGatewayControlRun`)
and the infinite-sentinel control
(`LidoCircuitBreakerTriggerableWithdrawalsGatewaySentinelControlRun`) replay the
same production public pause over the real gateway crossing.  They differ only in
the control storage (the stored duration word), the gateway's child charge for
that duration (`gatewayPauseChildCost`, 25,598 or 25,567), and therefore in one
gas literal.  This module states the run once, over a `GWorld` whose spec supplies
exactly those three data plus the premise bundle of the concrete world; each control
module instantiates it and keeps its own public statement.
-/

namespace Blanc.Composition

open Jaune
open Blanc
open Blanc.LidoCircuitBreaker
open Blanc.LidoTriggerableWithdrawalsGateway
open Blanc.Composition.LidoCircuitBreakerTwg

namespace LidoCircuitBreakerTwgRun

/-! ## The generic closed world -/

/-- The row-19 pause world with the compiled gateway installed at the pause
target: its breaker storage, entry gas, stored duration word and the gateway's
child charge for it. -/
structure GWorld where
  stor : Stor
  gas : Nat
  dur : B256
  c : Nat

def GWorld.state (w : GWorld) : State :=
  State.set
    (State.set (.empty : State) configWorldOwner
      { Acct.nil with stor := w.stor, code := configWorldCode })
    pauseWorldCallee
      { Acct.nil with
        stor := controlGatewayStor
        code := gatewayCode controlDeployParams }

def GWorld.msg (w : GWorld) : Msg :=
  { (pauseWorldMsg w.stor w.gas) with
    benv :=
      { (pauseWorldMsg w.stor w.gas).benv with
        state := w.state
        stat :=
          { (pauseWorldMsg w.stor w.gas).benv.stat with
            origState := w.state } } }

def GWorld.sevm (w : GWorld) : Sevm := initSevm w.msg

def GWorld.pre (w : GWorld) : Devm := initDevm w.msg

/-- What a concrete world owes the generic run. -/
class GWorldSpec (w : GWorld) : Prop where
  assignment : w.stor.get (assignmentSlot pauseWorldCallee.toB256) = pauseWorldPauser
  expiry : w.stor.get (expirySlot pauseWorldPauser) = pauseWorldExpiry
  duration : w.stor.get pauseDurationSlot = w.dur
  index : w.stor.get (indexSlot pauseWorldCallee.toB256) = 1
  length : w.stor.get arrayLengthSlot = 1
  entry : w.stor.get (arrayEntrySlot 1) = pauseWorldCallee.toB256
  count : w.stor.get (countSlot pauseWorldPauser) = 1
  child : gatewayPauseChildCost w.dur = w.c
  gas : w.gas = pauseDispatchGas + (w.c + 77755)
  premises : PublicPauseEntryPremises w.sevm w.pre configWorldOwner
    pauseWorldCallee.toB256 w.dur 1 1 pauseWorldCallee.toB256 []
    (gatewayCode controlDeployParams)
  notPrecompile : w.sevm.benvStat.rules.isPrecomp
    pauseWorldCallee.toB256.toAdr = false
  timeLtExpiry : w.sevm.benvStat.time < pauseWorldExpiry
  durNe : w.dur ≠ 0
  projNe : pauseForProjection w.sevm.benvStat.time w.dur ≠ 0
  timeLt : w.sevm.benvStat.time < pauseForProjection w.sevm.benvStat.time w.dur

variable {w : GWorld}

theorem GWorld.state_get_breaker :
    w.state.get configWorldOwner =
      { Acct.nil with stor := w.stor, code := configWorldCode } := by
  rw [GWorld.state, State.get_set_ne _ pauseWorld_callee_ne_owner,
    State.get_set_self]

theorem GWorld.state_get_target :
    w.state.get pauseWorldCallee =
      { Acct.nil with
        stor := controlGatewayStor
        code := gatewayCode controlDeployParams } := by
  rw [GWorld.state, State.get_set_self]

theorem GWorld.currentTarget : w.sevm.currentTarget = configWorldOwner := rfl

theorem GWorld.callerWord : w.sevm.caller.toB256 = pauseWorldPauser :=
  pauseWorld_pauserAdr_toB256

theorem GWorld.getStorVal {key : B256} :
    w.pre.getStorVal configWorldOwner key = w.stor.get key := by
  change (w.state.get configWorldOwner).stor.get key = _
  rw [GWorld.state_get_breaker]

theorem GWorld.targetCodeAt :
    CodeAt w.pre pauseWorldCallee (gatewayCode controlDeployParams) := by
  show (w.state.get pauseWorldCallee).code = _
  rw [GWorld.state_get_target]

theorem GWorld.target_ne_owner :
    pauseWorldCallee.toB256.toAdr ≠ w.sevm.currentTarget := by
  rw [toAdr_toB256, GWorld.currentTarget]
  exact pauseWorld_callee_ne_owner



variable (w)

private theorem temporalSloadBase_accessedAddresses (sevm : Sevm) (base : Devm)
    (key : B256) : (temporalSloadBase sevm base key).accessedAddresses =
      base.accessedAddresses :=
  (temporalSloadBase_carriers sevm base key).2.2.1

/-! ## Slot-pair inequalities lifted to accessed-key pairs -/

private theorem keyPairNe {a₁ a₂ : Adr} {k₁ k₂ : B256} (h : k₂ ≠ k₁) :
    (a₁, k₁) ≠ (a₂, k₂) := fun hp => h (congrArg Prod.snd hp).symm

/-! ## The accessed-key set, stage by stage

The row-19 walk enters with both accessed sets empty, so each
`temporalSloadBase` layer resolves to its cold arm and the accessed-key set
grows by exactly the read key.  These shapes are what the cold cost equations
below read off; every non-membership is settled by slot separation, never by
deciding a `HashSet`. -/



private theorem gatewayRunKeys_expiryBase :
    (pauseExpiryBase w.sevm w.pre
      pauseWorldCallee.toB256).accessedStorageKeys =
    Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256) := by
  unfold pauseExpiryBase temporalSloadBase
  rw [ite_eq_right (show (w.sevm.currentTarget,
      assignmentSlot pauseWorldCallee.toB256) ∉
    (pauseLockPost w.sevm w.pre).accessedStorageKeys from
    Std.HashSet.not_mem_emptyWithCapacity)]
  rfl

private theorem gatewayRunKeys_durationBase :
    (pauseDurationBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys =
    (Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser) := by
  have hnot : (w.sevm.currentTarget, expirySlot pauseWorldPauser) ∉
      (pauseExpiryBase w.sevm w.pre
        pauseWorldCallee.toB256).accessedStorageKeys := by
    rw [(gatewayRunKeys_expiryBase w)]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
      Prod.mk.injEq, not_and]
    intro _
    exact pauseWorld_assignCallee_ne_expiry
  unfold pauseDurationBase temporalSloadBase
  rw [ite_eq_right hnot]
  show ((pauseExpiryBase w.sevm w.pre
    pauseWorldCallee.toB256).accessedStorageKeys).insert
    (w.sevm.currentTarget, expirySlot pauseWorldPauser) = _
  rw [(gatewayRunKeys_expiryBase w)]
  rfl

private theorem gatewayRunKeys_kernelBase :
    (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys =
    ((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot) := by
  have hnot : (w.sevm.currentTarget, pauseDurationSlot) ∉
      (pauseDurationBase w.sevm w.pre
        pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys := by
    rw [(gatewayRunKeys_durationBase w)]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_expiry.symm
    · exact pauseWorld_duration_ne_assignCallee.symm
  unfold pauseKernelBase temporalSloadBase
  rw [ite_eq_right hnot]
  show ((pauseDurationBase w.sevm w.pre
    pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys).insert
    (w.sevm.currentTarget, pauseDurationSlot) = _
  rw [(gatewayRunKeys_durationBase w)]
  rfl

private theorem gatewayRunWarm_assign_kernelBase :
    (w.sevm.currentTarget, assignmentSlot pauseWorldCallee.toB256) ∈
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser).accessedStorageKeys := by
  rw [(gatewayRunKeys_kernelBase w)]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr Std.HashSet.mem_insert_self)))

private theorem gatewayRunKeys_assignPost :
    (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys = (((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)) := by
  rw [assignmentPost, temporalSstorePost_accessedStorageKeys]
  unfold assignmentBase temporalSloadBase
  rw [ite_eq_left (gatewayRunWarm_assign_kernelBase w)]
  exact (gatewayRunKeys_kernelBase w)

private theorem gatewayRunKeys_countBase :
    (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser)).accessedStorageKeys = ((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)) := by
  have hnot : (w.sevm.currentTarget, countSlot pauseWorldPauser) ∉
      (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys := by
    rw [(gatewayRunKeys_assignPost w)]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_count
    · exact pauseWorld_count_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_count
  rw [temporalSloadBase_cold_keys _ _ _ hnot, (gatewayRunKeys_assignPost w)]
  rfl

private theorem gatewayRunKeys_removeBase1 :
    (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys = (((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)).insert
      (configWorldOwner, indexSlot pauseWorldCallee.toB256)) := by
  have hnot : (w.sevm.currentTarget, indexSlot pauseWorldCallee.toB256) ∉
      (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).accessedStorageKeys := by
    rw [temporalSstorePost_accessedStorageKeys, (gatewayRunKeys_countBase w)]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_indexCallee_ne_count.symm
    · exact pauseWorld_duration_ne_indexCallee
    · exact pauseWorld_indexCallee_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_indexCallee
  rw [temporalSloadBase_cold_keys _ _ _ hnot, temporalSstorePost_accessedStorageKeys,
    (gatewayRunKeys_countBase w)]
  rfl

private theorem gatewayRunKeys_removeBase2 :
    (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys = ((((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)).insert
      (configWorldOwner, indexSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, arrayLengthSlot)) := by
  have hnot : (w.sevm.currentTarget, arrayLengthSlot) ∉
      (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys := by
    rw [(gatewayRunKeys_removeBase1 w)]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_length_ne_indexCallee.symm
    · exact pauseWorld_length_ne_count.symm
    · exact pauseWorld_duration_ne_length
    · exact pauseWorld_length_ne_expiry.symm
    · exact pauseWorld_length_ne_assignCallee.symm
  rw [temporalSloadBase_cold_keys _ _ _ hnot, (gatewayRunKeys_removeBase1 w)]
  rfl

private theorem gatewayRunKeys_removeBase3 :
    (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).accessedStorageKeys = (((((((Std.HashSet.emptyWithCapacity.insert
      (configWorldOwner, assignmentSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, expirySlot pauseWorldPauser)).insert
      (configWorldOwner, pauseDurationSlot)).insert
      (configWorldOwner, countSlot pauseWorldPauser)).insert
      (configWorldOwner, indexSlot pauseWorldCallee.toB256)).insert
      (configWorldOwner, arrayLengthSlot)).insert
      (configWorldOwner, arrayEntrySlot 1)) := by
  have hnot : (w.sevm.currentTarget, arrayEntrySlot 1) ∉
      (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys := by
    rw [(gatewayRunKeys_removeBase2 w)]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_,
      fun _ => ?_⟩
    · exact pauseWorld_length_ne_entryOne
    · exact pauseWorld_entryOne_ne_indexCallee.symm
    · exact pauseWorld_entryOne_ne_count.symm
    · exact pauseWorld_duration_ne_entryOne
    · exact pauseWorld_entryOne_ne_expiry.symm
    · exact pauseWorld_entryOne_ne_assignCallee.symm
  rw [temporalSloadBase_cold_keys _ _ _ hnot, (gatewayRunKeys_removeBase2 w)]
  rfl

/-! ## One-layer projection helpers -/

/-! ## One-layer projection helpers -/

private theorem temporalSstorePost_accessedAddresses (sevm : Sevm)
    (base : Devm) (key value : B256) :
    (temporalSstorePost sevm base key value).accessedAddresses =
      base.accessedAddresses := rfl

private theorem setMach_getStorVal (devm : Devm) (m : Mach) (a : Adr)
    (key : B256) : (devm.setMach m).getStorVal a key = devm.getStorVal a key :=
  rfl

/-! ## The cold and warm charges, resolved at the row-19 world -/

private theorem gatewayRunCost_assignment :
    temporalSloadCost w.sevm (pauseLockPost w.sevm w.pre)
      (assignmentSlot pauseWorldCallee.toB256) = 2100 := by
  unfold temporalSloadCost
  rw [ite_eq_right (show (w.sevm.currentTarget, assignmentSlot pauseWorldCallee.toB256) ∉
    (pauseLockPost w.sevm w.pre).accessedStorageKeys from
    Std.HashSet.not_mem_emptyWithCapacity)]
  rfl

private theorem gatewayRunCost_expiry :
    temporalSloadCost w.sevm
      (pauseExpiryBase w.sevm w.pre pauseWorldCallee.toB256)
      (expirySlot pauseWorldPauser) = 2100 := by
  unfold temporalSloadCost
  rw [ite_eq_right (show (w.sevm.currentTarget, expirySlot pauseWorldPauser) ∉
      (pauseExpiryBase w.sevm w.pre pauseWorldCallee.toB256).accessedStorageKeys from by
    rw [(gatewayRunKeys_expiryBase w)]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
      Prod.mk.injEq, not_and]
    intro _
    exact pauseWorld_assignCallee_ne_expiry)]
  rfl

private theorem gatewayRunCost_duration :
    temporalSloadCost w.sevm
      (pauseDurationBase w.sevm w.pre pauseWorldCallee.toB256 pauseWorldPauser)
      pauseDurationSlot = 2100 := by
  unfold temporalSloadCost
  rw [ite_eq_right (show (w.sevm.currentTarget, pauseDurationSlot) ∉
      (pauseDurationBase w.sevm w.pre pauseWorldCallee.toB256
        pauseWorldPauser).accessedStorageKeys from by
    rw [(gatewayRunKeys_durationBase w)]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_expiry.symm
    · exact pauseWorld_duration_ne_assignCallee.symm)]
  rfl

private theorem gatewayRunCost_assignWarm :
    temporalSloadCost w.sevm (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser)
      (assignmentSlot pauseWorldCallee.toB256) = 100 := by
  unfold temporalSloadCost
  rw [ite_eq_left (gatewayRunWarm_assign_kernelBase w)]
  rfl

private theorem gatewayRunCost_countCold :
    temporalSloadCost w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser) = 2100 := by
  unfold temporalSloadCost
  rw [ite_eq_right (show (w.sevm.currentTarget, countSlot pauseWorldPauser) ∉
      (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedStorageKeys from by
    rw [(gatewayRunKeys_assignPost w)]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_duration_ne_count
    · exact pauseWorld_count_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_count)]
  rfl

private theorem gatewayRunCost_idxCold :
    temporalSloadCost w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256) = 2100 := by
  unfold temporalSloadCost
  rw [ite_eq_right (show (w.sevm.currentTarget, indexSlot pauseWorldCallee.toB256) ∉
      (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).accessedStorageKeys from by
    rw [temporalSstorePost_accessedStorageKeys, (gatewayRunKeys_countBase w)]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_indexCallee_ne_count.symm
    · exact pauseWorld_duration_ne_indexCallee
    · exact pauseWorld_indexCallee_ne_expiry.symm
    · exact pauseWorld_assignCallee_ne_indexCallee)]
  rfl

private theorem gatewayRunCost_lenCold :
    temporalSloadCost w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot = 2100 := by
  unfold temporalSloadCost
  rw [ite_eq_right (show (w.sevm.currentTarget, arrayLengthSlot) ∉
      (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256)).accessedStorageKeys from by
    rw [(gatewayRunKeys_removeBase1 w)]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · exact pauseWorld_length_ne_indexCallee.symm
    · exact pauseWorld_length_ne_count.symm
    · exact pauseWorld_duration_ne_length
    · exact pauseWorld_length_ne_expiry.symm
    · exact pauseWorld_length_ne_assignCallee.symm)]
  rfl

private theorem gatewayRunCost_arrCold :
    temporalSloadCost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1) = 2100 := by
  unfold temporalSloadCost
  rw [ite_eq_right (show (w.sevm.currentTarget, arrayEntrySlot 1) ∉
      (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot).accessedStorageKeys from by
    rw [(gatewayRunKeys_removeBase2 w)]
    simp only [Std.HashSet.mem_insert,
      Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or, beq_iff_eq,
      Prod.mk.injEq, not_and]
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_,
      fun _ => ?_⟩
    · exact pauseWorld_length_ne_entryOne
    · exact pauseWorld_entryOne_ne_indexCallee.symm
    · exact pauseWorld_entryOne_ne_count.symm
    · exact pauseWorld_duration_ne_entryOne
    · exact pauseWorld_entryOne_ne_expiry.symm
    · exact pauseWorld_entryOne_ne_assignCallee.symm)]
  rfl

private theorem gatewayRunKernelPrefixGas :
    foundSetPauserKernelPrefixGas w.sevm
      (pauseKernelBase w.sevm w.pre
        pauseWorldCallee.toB256 pauseWorldPauser)
      pauseWorldCallee.toB256 0 pauseWorldPauser 2900 2900 = 8122 := by
  unfold foundSetPauserKernelPrefixGas
  rw [(gatewayRunCost_assignWarm w), (gatewayRunCost_countCold w)]

private theorem gatewayRunWarm_count_rb3 :
    (w.sevm.currentTarget, countSlot pauseWorldPauser) ∈
      (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).accessedStorageKeys := by
  rw [(gatewayRunKeys_removeBase3 w)]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr Std.HashSet.mem_insert_self)))))

private theorem gatewayRunWarm_expiry_rb3 :
    (w.sevm.currentTarget, expirySlot pauseWorldPauser) ∈
      (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).accessedStorageKeys := by
  rw [(gatewayRunKeys_removeBase3 w)]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
      (Or.inr (Std.HashSet.mem_insert.mpr
        (Or.inr Std.HashSet.mem_insert_self)))))))))

/-! ## Storage read through the tower, stage by stage

Each lemma peels exactly one named layer by rewrite, per the substrate's
one-layer transport discipline. -/

private theorem gatewayRunStor_lockPost (key : B256) :
    (pauseLockPost w.sevm w.pre).getStorVal configWorldOwner key =
      w.stor.get key := by
  show w.pre.getStorVal configWorldOwner key = _
  exact (GWorld.getStorVal (w := w))

private theorem gatewayRunStor_kernelBase (key : B256) :
    (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser).getStorVal configWorldOwner key = w.stor.get key := by
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact (gatewayRunStor_lockPost w) key

private theorem gatewayRunStor_assignPost_other {key : B256}
    (h : assignmentSlot pauseWorldCallee.toB256 ≠ key) :
    (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).getStorVal configWorldOwner key = w.stor.get key := by
  unfold assignmentPost
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe h)]
  unfold assignmentBase
  rw [temporalSloadBase_getStorVal]
  exact (gatewayRunStor_kernelBase w) key


private theorem gatewayRunStor_countPost_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key) :
    (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner key = w.stor.get key := by
  rw [temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hc),
    temporalSloadBase_getStorVal]
  exact (gatewayRunStor_assignPost_other w) ha

private theorem gatewayRunStor_countPost_count :
    (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 :=
  temporalSstorePost_self _ _ _ _

private theorem gatewayRunStor_removeBase3_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key) :
    (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).getStorVal configWorldOwner key = w.stor.get key := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact (gatewayRunStor_countPost_other w) ha hc

private theorem gatewayRunStor_removeBase3_count :
    (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 := by
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  exact (gatewayRunStor_countPost_count w)

/-! The five removal-walk writes, peeled from the outside of `B6`:
`indexClearPost` writes the index clear over the length restore, and
`entryClearPost` writes the tail clear over the moved-index and hole
writes. -/

private theorem gatewayRunStor_B6_other {key : B256}
    (ha : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hc : countSlot pauseWorldPauser ≠ key)
    (hr : arrayEntrySlot 1 ≠ key)
    (hi : indexSlot pauseWorldCallee.toB256 ≠ key)
    (hl : arrayLengthSlot ≠ key) :
    (indexClearPost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner key = w.stor.get key := by
  rw [show (indexClearPost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost w.sevm
      (lengthWritePost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hi),
    show lengthWritePost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hl),
    show (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost w.sevm
      (indexWritePost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hr),
    show indexWritePost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost w.sevm
      (entryWritePost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hi),
    show entryWritePost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost w.sevm
      (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_other _ _ _ _ _ _ (keyPairNe hr)]
  exact (gatewayRunStor_removeBase3_other w) ha hc

private theorem gatewayRunStor_B6_count :
    (indexClearPost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).getStorVal configWorldOwner (countSlot pauseWorldPauser) = 0 := by
  rw [show (indexClearPost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost w.sevm
      (lengthWritePost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_indexCallee_ne_count),
    show lengthWritePost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_length_ne_count),
    show (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost w.sevm
      (indexWritePost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_count),
    show indexWritePost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost w.sevm
      (entryWritePost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_indexCallee_ne_count),
    show entryWritePost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost w.sevm
      (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_other _ _ _ _ _ _
      (keyPairNe pauseWorld_entryOne_ne_count)]
  exact (gatewayRunStor_removeBase3_count w)

/-! ## The staged memory and its image, through the walk's writes

`pauseMemory`'s five scratch words are staged by the body; the kernel saves
the old pauser at `previousPauserWord`, and the removal walk writes its three
scratch words above it.  Every write stays inside the `768`-byte image, so no
extension is ever charged. -/


private theorem temporalSloadBase_getCode (sevm : Sevm) (base : Devm)
    (key : B256) (a : Adr) :
    (temporalSloadBase sevm base key).getCode a = base.getCode a :=
  (temporalSloadBase_carriers sevm base key).2.2.2 a


private theorem gatewayRunAddrs_B7 :
    ((indexClearPost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨w.sevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).accessedAddresses = Std.HashSet.emptyWithCapacity := by
  rw [Devm.addLog_accessedAddresses,
    show (indexClearPost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0) = temporalSstorePost w.sevm
      (lengthWritePost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0) (indexSlot pauseWorldCallee.toB256) 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show lengthWritePost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) 0 = temporalSstorePost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1)
      arrayLengthSlot 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) = temporalSstorePost w.sevm
      (indexWritePost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (arrayEntrySlot 1) 0 from rfl,
    temporalSstorePost_accessedAddresses,
    show indexWritePost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost w.sevm
      (entryWritePost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) (indexSlot pauseWorldCallee.toB256) 1 from rfl,
    temporalSstorePost_accessedAddresses,
    show entryWritePost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1 = temporalSstorePost w.sevm
      (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) (arrayEntrySlot 1) pauseWorldCallee.toB256 from rfl,
    temporalSstorePost_accessedAddresses,
    temporalSloadBase_accessedAddresses, temporalSloadBase_accessedAddresses,
    temporalSloadBase_accessedAddresses, temporalSstorePost_accessedAddresses,
    temporalSloadBase_accessedAddresses]
  show (assignmentPost w.sevm
    (pauseKernelBase w.sevm w.pre pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0).accessedAddresses = _
  unfold assignmentPost
  rw [temporalSstorePost_accessedAddresses]
  unfold assignmentBase
  rw [temporalSloadBase_accessedAddresses]
  unfold pauseKernelBase pauseDurationBase pauseExpiryBase
  rw [temporalSloadBase_accessedAddresses,
    temporalSloadBase_accessedAddresses, temporalSloadBase_accessedAddresses]
  rfl

private theorem gatewayRunCode_B7 :
    ((indexClearPost w.sevm (entryClearPost w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSloadBase w.sevm (temporalSstorePost w.sevm (temporalSloadBase w.sevm (assignmentPost w.sevm
      (pauseKernelBase w.sevm w.pre
      pauseWorldCallee.toB256 pauseWorldPauser) pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
      (countSlot pauseWorldPauser) 0)
      (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
      (arrayEntrySlot 1)) pauseWorldCallee.toB256 1) pauseWorldCallee.toB256 0).addLog
      ⟨w.sevm.currentTarget,
      [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩).getCode pauseWorldCallee.toB256.toAdr = (gatewayCode controlDeployParams) := by
  have addLogCode : ∀ (d : Devm) (l : Log) (a : Adr),
      (d.addLog l).getCode a = d.getCode a := fun _ _ _ => rfl
  have transCode : ∀ (d : Devm) (a : Adr) (k v : B256) (x : Adr),
      (d.setTransVal a k v).getCode x = d.getCode x := fun _ _ _ _ _ => rfl
  simp only [indexClearPost, entryClearPost, lengthWritePost, indexWritePost,
    entryWritePost, assignmentPost, assignmentBase, pauseKernelBase,
    pauseDurationBase, pauseExpiryBase, pauseLockPost, addLogCode, transCode,
    temporalSstorePost_getCode, temporalSloadBase_getCode]
  show w.pre.state.getCode pauseWorldCallee.toB256.toAdr = (gatewayCode controlDeployParams)
  rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from by decide]
  exact (GWorld.targetCodeAt (w := w))



variable [GWorldSpec w]

private def gatewayRunKernelBase (w : GWorld) : Devm :=
  pauseKernelBase w.sevm w.pre
    pauseWorldCallee.toB256 pauseWorldPauser

private def gatewayRunCountPost (w : GWorld) : Devm :=
  temporalSstorePost w.sevm
    (temporalSloadBase w.sevm
      (assignmentPost w.sevm (gatewayRunKernelBase w)
        pauseWorldCallee.toB256 0)
      (countSlot pauseWorldPauser))
    (countSlot pauseWorldPauser) 0

private def gatewayRunRemoveBase3 (w : GWorld) : Devm :=
  temporalSloadBase w.sevm
    (temporalSloadBase w.sevm
      (temporalSloadBase w.sevm (gatewayRunCountPost w)
        (indexSlot pauseWorldCallee.toB256))
      arrayLengthSlot)
    (arrayEntrySlot 1)

private def gatewayRunAfterSetBase (w : GWorld) : Devm :=
  (indexClearPost w.sevm
    (entryClearPost w.sevm (gatewayRunRemoveBase3 w)
      pauseWorldCallee.toB256 1)
    pauseWorldCallee.toB256 0).addLog
      ⟨w.sevm.currentTarget,
        [pauserSetEvent, pauseWorldCallee.toB256, pauseWorldPauser, 0], []⟩

section MemImage

variable (dur : B256)

private def gatewayRunMemoryLast : Mem :=
  ((((pauseMemory pauseWorldCallee.toB256 dur).write
    (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
    (removedIndexWord * 32).toNat (1 : B256).toBytes).write
    (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
    (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes

private def gatewayRunImageLast : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt (pauseImage pauseWorldCallee.toB256
            dur)
          (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
        (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
    (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes

theorem gatewayRunMem_wf1 : Mem.Wf ((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 dur with ⟨hwf, -⟩
  exact hwf.write _ _

/-- The stage-one facts of the kernel-saved memory, read off
`pauseMemory_spec` in one destructuring: the written image, the unmoved `768`
size, and the two staged words the kernel's write must not disturb.  The four
named facts below are its projections. -/
private theorem gatewayRunMem_stage1 :
    Mem.Reads ((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) ∧
    ((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).size = 768 ∧
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD
        (targetWord * 32).toNat 32 0) = pauseWorldCallee.toB256 ∧
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD
        (newPauserWord * 32).toNat 32 0) = 0 := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 dur with
    ⟨hwf, hreads, hsize, -, -, htarget, hnew, -⟩
  refine ⟨Mem.Reads.write hwf hreads _ _, ?_, ?_, ?_⟩
  · rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, hsize]
      decide)]
    exact hsize
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact htarget
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
    exact hnew

theorem gatewayRunMem_reads1 : Mem.Reads ((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes) :=
  (gatewayRunMem_stage1 dur).1

theorem gatewayRunMem_size1 : ((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).size = 768 :=
  (gatewayRunMem_stage1 dur).2.1

theorem gatewayRunMem_target1 :
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 :=
  (gatewayRunMem_stage1 dur).2.2.1

theorem gatewayRunMem_new1 :
    Bytes.toB256 ((Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).sliceD (newPauserWord * 32).toNat 32 0) = 0 :=
  (gatewayRunMem_stage1 dur).2.2.2

theorem gatewayRunMem_wfLast : Mem.Wf (((((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) :=
  (((gatewayRunMem_wf1 dur).write _ _).write _ _).write _ _

theorem gatewayRunMem_readsLast : Mem.Reads (((((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) :=
  Mem.Reads.write (((gatewayRunMem_wf1 dur).write _ _).write _ _)
    (Mem.Reads.write ((gatewayRunMem_wf1 dur).write _ _)
      (Mem.Reads.write (gatewayRunMem_wf1 dur) (gatewayRunMem_reads1 dur) _ _) _ _) _ _

private theorem gatewayRunMem_sizeIdx : (((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, gatewayRunMem_size1]
    decide)]
  exact (gatewayRunMem_size1 dur)

private theorem gatewayRunMem_sizeLen : ((((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, gatewayRunMem_sizeIdx]
    decide)]
  exact (gatewayRunMem_sizeIdx dur)

theorem gatewayRunMem_sizeLast : (((((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, gatewayRunMem_sizeLen]
    decide)]
  exact (gatewayRunMem_sizeLen dur)

theorem gatewayRunMem_targetLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact (gatewayRunMem_target1 dur)

theorem gatewayRunMem_newLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (newPauserWord * 32).toNat 32 0) = 0 := by
  rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide)]
  exact (gatewayRunMem_new1 dur)

/-- The three scratch words of the four-write image no later write disturbs,
in one bundle: the saved pauser survives at its own offset below every later
write, and the continuation and duration words sit above them all.  The three
named facts below are its projections. -/
private theorem gatewayRunMem_lastWords :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (previousPauserWord * 32).toNat 32 0) =
      pauseWorldPauser ∧
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (continuationWord * 32).toNat 32 0) = 1 ∧
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (durationWord * 32).toNat 32 0) =
      dur := by
  rcases pauseMemory_spec pauseWorldCallee.toB256 dur with
    ⟨-, -, -, -, -, -, -, -, hcont, hdur⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      show 32 = pauseWorldPauser.toBytes.length by rw [B256.length_toBytes],
      Bytes.sliceD_writeAt, B256.toB256_toBytes]
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by decide),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]; decide)]
    exact hcont
  · rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]; decide),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]; decide),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]; decide),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by
        rw [B256.length_toBytes]; decide)]
    exact hdur

theorem gatewayRunMem_prevLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (previousPauserWord * 32).toNat 32 0) =
      pauseWorldPauser :=
  (gatewayRunMem_lastWords dur).1

theorem gatewayRunMem_contLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (continuationWord * 32).toNat 32 0) = 1 :=
  (gatewayRunMem_lastWords dur).2.1

theorem gatewayRunMem_durLast :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).sliceD (durationWord * 32).toNat 32 0) =
      dur :=
  (gatewayRunMem_lastWords dur).2.2
/-! ## Staged-memory sizes past the crossings -/

private theorem gatewayRunMem_sizeStaged1 : ((((((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).write 256 pauseForSelector.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, gatewayRunMem_sizeLast]
    decide)]
  exact (gatewayRunMem_sizeLast dur)

private theorem gatewayRunMem_sizeStaged2 : (((((((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).write 256 pauseForSelector.toBytes).write 288 dur.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, gatewayRunMem_sizeStaged1]
    decide)]
  exact (gatewayRunMem_sizeStaged1 dur)

private theorem gatewayRunMem_sizeStaged3 : ((((((((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes).write 256 pauseForSelector.toBytes).write 288 dur.toBytes).write 256 isPausedSelector.toBytes).size = 768 := by
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, gatewayRunMem_sizeStaged2]
    decide)]
  exact (gatewayRunMem_sizeStaged2 dur)


theorem gatewayRunMem_size8 :
    (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) dur).size = 768 := by
  unfold pauseDecodedMemory pauseStagedMemory
  rw [Mem.size_write_of_le (by
    rw [B256.length_toBytes, gatewayRunMem_sizeStaged3]
    decide)]
  exact (gatewayRunMem_sizeStaged3 dur)
theorem gatewayRunMem_wf8 :
    Mem.Wf (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) dur) := by
  unfold pauseDecodedMemory pauseStagedMemory
  exact ((((gatewayRunMem_wfLast dur).write _ _).write _ _).write _ _).write _ _

theorem gatewayRunMem_reads8 :
    Mem.Reads (pauseDecodedMemory (((((pauseMemory pauseWorldCallee.toB256 dur).write
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes).write
      (removedIndexWord * 32).toNat (1 : B256).toBytes).write
      (arrayLengthWord * 32).toNat (1 : B256).toBytes).write
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes) dur) (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes)
      256 pauseForSelector.toBytes) 288 dur.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes) := by
  unfold pauseDecodedMemory pauseStagedMemory
  exact Mem.Reads.write ((((gatewayRunMem_wfLast dur).write _ _).write _ _).write _ _)
    (Mem.Reads.write (((gatewayRunMem_wfLast dur).write _ _).write _ _)
      (Mem.Reads.write ((gatewayRunMem_wfLast dur).write _ _)
        (Mem.Reads.write (gatewayRunMem_wfLast dur) (gatewayRunMem_readsLast dur) _ _) _ _) _ _) _ _

theorem gatewayRunMem_target8 :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes)
      256 pauseForSelector.toBytes) 288 dur.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes).sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 := by
  rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
  exact (gatewayRunMem_targetLast dur)

theorem gatewayRunMem_dur8 :
    Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
      (previousPauserWord * 32).toNat pauseWorldPauser.toBytes)
      (removedIndexWord * 32).toNat (1 : B256).toBytes)
      (arrayLengthWord * 32).toNat (1 : B256).toBytes)
      (lastTargetWord * 32).toNat pauseWorldCallee.toB256.toBytes)
      256 pauseForSelector.toBytes) 288 dur.toBytes) 256
      isPausedSelector.toBytes) 0 (1 : B256).toBytes).sliceD (durationWord * 32).toNat 32 0) =
      dur := by
  rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
  exact (gatewayRunMem_durLast dur)



end MemImage

/-! ## The composed run -/

omit [GWorldSpec w] in
private theorem gatewayPauseWorld_targetPausedOrigZero :
    getOrigStorVal w.sevm pauseWorldCallee
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0 := by
  change (w.state.get pauseWorldCallee).stor.get
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0
  rw [(GWorld.state_get_target (w := w))]
  decide +kernel

omit [GWorldSpec w] in
private theorem gatewayRunAfterSetBase_code :
    (gatewayRunAfterSetBase w).getCode pauseWorldCallee.toB256.toAdr =
      (gatewayCode controlDeployParams) := by
  have hcode := (gatewayRunCode_B7 w)
  simpa only [gatewayRunAfterSetBase, gatewayRunRemoveBase3, gatewayRunCountPost,
    gatewayRunKernelBase] using hcode

omit [GWorldSpec w] in
/-- The CircuitBreaker owner keeps its installed runtime at the after-set
entry, so it is `State.Protected` there (TWG-3 crossing premise, decision
blanc-composition-twg2-protected-20261012, cause SA). -/
private theorem gatewayRunAfterSetBase_ownerProtected :
    State.Protected (gatewayRunAfterSetBase w).state
      w.sevm.currentTarget := by
  apply State.Protected.of_code_ne_nil
  have addLogCode : ∀ (d : Devm) (l : Log) (a : Adr),
      (d.addLog l).getCode a = d.getCode a := fun _ _ _ => rfl
  have transCode : ∀ (d : Devm) (a : Adr) (k v : B256) (x : Adr),
      (d.setTransVal a k v).getCode x = d.getCode x := fun _ _ _ _ _ => rfl
  have hcarry : (gatewayRunAfterSetBase w).getCode configWorldOwner =
      w.pre.getCode configWorldOwner := by
    simp only [gatewayRunAfterSetBase,
      gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase,
      indexClearPost, entryClearPost, lengthWritePost, indexWritePost,
      entryWritePost, assignmentPost, assignmentBase, pauseKernelBase,
      pauseDurationBase, pauseExpiryBase, pauseLockPost,
      addLogCode, transCode, temporalSstorePost_getCode, temporalSloadBase_getCode]
  change ((gatewayRunAfterSetBase w).getCode
    w.sevm.currentTarget).toList ≠ []
  rw [(GWorld.currentTarget (w := w)), hcarry]
  change (w.state.get configWorldOwner).code.toList ≠ []
  rw [(GWorld.state_get_breaker (w := w))]
  intro hnil
  have hempty : lidoCircuitBreakerCode officialParams = [] := by
    simpa only [configWorldCode, ByteArray.toList_eq_toList_data,
      List.toList_toArray] using hnil
  exact Prog.compile_ne_nil (by rw [lidoCircuitBreakerCode_compile, hempty])

omit [GWorldSpec w] in
private theorem gatewayRunAfterSetBase_targetKeyCold (key : B256) :
    (pauseWorldCallee.toB256.toAdr, key) ∉
      (gatewayRunAfterSetBase w).accessedStorageKeys := by
  have hcallee : pauseWorldCallee.toB256.toAdr = pauseWorldCallee := by decide
  rw [gatewayRunAfterSetBase, Devm.addLog_accessedStorageKeys,
    indexClearPost_accessedStorageKeys, entryClearPost_accessedStorageKeys]
  unfold gatewayRunRemoveBase3 gatewayRunCountPost gatewayRunKernelBase
  rw [(gatewayRunKeys_removeBase3 w)]
  simp only [Std.HashSet.mem_insert,
    Std.HashSet.not_mem_emptyWithCapacity, or_false, not_or,
    beq_iff_eq, Prod.mk.injEq, not_and]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_, fun h => ?_⟩
  all_goals
    intro _
    apply pauseWorld_callee_ne_owner
    rw [← hcallee]
    exact h.symm


omit [GWorldSpec w] in
private theorem gatewayRunAfterSetBase_targetStor (key : B256) :
    (gatewayRunAfterSetBase w).getStorVal pauseWorldCallee.toB256.toAdr key =
      controlGatewayStor.get key := by
  have haddr : pauseWorldCallee.toB256.toAdr ≠
      w.sevm.currentTarget := (GWorld.target_ne_owner (w := w))
  unfold gatewayRunAfterSetBase
  rw [Devm.addLog_getStorVal]
  unfold indexClearPost lengthWritePost entryClearPost indexWritePost
    entryWritePost
  rw [temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr]
  unfold gatewayRunRemoveBase3
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal]
  unfold gatewayRunCountPost
  rw [temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr,
    temporalSloadBase_getStorVal]
  unfold assignmentPost
  rw [temporalSstorePost_getStorVal_otherAddress _ _ _ _ _ _ haddr]
  unfold assignmentBase gatewayRunKernelBase pauseKernelBase pauseDurationBase
    pauseExpiryBase
  rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal,
    temporalSloadBase_getStorVal, temporalSloadBase_getStorVal]
  rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from by decide]
  change (w.state.get pauseWorldCallee).stor.get key = _
  rw [(GWorld.state_get_target (w := w))]

omit [GWorldSpec w] in
private theorem gatewayRunAfterSetBase_targetPausedZero :
    (gatewayRunAfterSetBase w).getStorVal pauseWorldCallee.toB256.toAdr
      LidoTriggerableWithdrawalsGateway.resumeSinceSlot = 0 := by
  calc
    _ = controlGatewayStor.get
        LidoTriggerableWithdrawalsGateway.resumeSinceSlot :=
      (gatewayRunAfterSetBase_targetStor w) _
    _ = 0 := by decide +kernel

omit [GWorldSpec w] in
private theorem gatewayRunAfterSetBase_membership :
    (gatewayRunAfterSetBase w).getStorVal pauseWorldCallee.toB256.toAdr
      (roleMembershipSlot pauseRole
        w.sevm.currentTarget.toB256) ≠ 0 := by
  rw [(gatewayRunAfterSetBase_targetStor w), (GWorld.currentTarget (w := w))]
  decide +kernel

omit [GWorldSpec w] in
private theorem gatewayRunAfterSetBase_count :
    (gatewayRunAfterSetBase w).getStorVal configWorldOwner
      (countSlot pauseWorldPauser) = 0 := by
  have hcount := (gatewayRunStor_B6_count w)
  rw [gatewayRunAfterSetBase, Devm.addLog_getStorVal]
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using
    hcount

private theorem gatewayRunAfterSetBase_expiry :
    (gatewayRunAfterSetBase w).getStorVal configWorldOwner
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
  rw [gatewayRunAfterSetBase, Devm.addLog_getStorVal]
  have h := ((gatewayRunStor_B6_other w) pauseWorld_assignCallee_ne_expiry
    pauseWorld_count_ne_expiry pauseWorld_entryOne_ne_expiry
    pauseWorld_indexCallee_ne_expiry pauseWorld_length_ne_expiry).trans
      (GWorldSpec.expiry (w := w))
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using h

omit [GWorldSpec w] in
private theorem gatewayRunAfterSetBase_accessedAddresses :
    (gatewayRunAfterSetBase w).accessedAddresses = Std.HashSet.emptyWithCapacity := by
  simpa only [gatewayRunAfterSetBase, gatewayRunRemoveBase3, gatewayRunCountPost,
    gatewayRunKernelBase] using (gatewayRunAddrs_B7 w)


omit [GWorldSpec w] in
private theorem gatewayRunAfterSetBase_warmCount :
    (w.sevm.currentTarget, countSlot pauseWorldPauser) ∈
      (gatewayRunAfterSetBase w).accessedStorageKeys := by
  rw [gatewayRunAfterSetBase, Devm.addLog_accessedStorageKeys,
    indexClearPost_accessedStorageKeys, entryClearPost_accessedStorageKeys]
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using
    (gatewayRunWarm_count_rb3 w)

omit [GWorldSpec w] in
private theorem gatewayRunAfterSetBase_warmExpiry :
    (w.sevm.currentTarget, expirySlot pauseWorldPauser) ∈
      (gatewayRunAfterSetBase w).accessedStorageKeys := by
  rw [gatewayRunAfterSetBase, Devm.addLog_accessedStorageKeys,
    indexClearPost_accessedStorageKeys, entryClearPost_accessedStorageKeys]
  simpa only [gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using
    (gatewayRunWarm_expiry_rb3 w)

omit [GWorldSpec w] in
private theorem gatewayRunAfterSetBase_membershipCold :
    (pauseWorldCallee.toB256.toAdr,
      roleMembershipSlot pauseRole
        w.sevm.currentTarget.toB256) ∉
      (gatewayRunAfterSetBase w).accessedStorageKeys :=
  (gatewayRunAfterSetBase_targetKeyCold w) _

omit [GWorldSpec w] in
private theorem gatewayRunAfterSetBase_resumeCold :
    (pauseWorldCallee.toB256.toAdr, resumeSinceSlot) ∉
      (pauseRoleWarm
        { w.sevm with
          currentTarget := pauseWorldCallee.toB256.toAdr
          caller := w.sevm.currentTarget }
        (gatewayRunAfterSetBase w)).accessedStorageKeys := by
  simp only [pauseRoleWarm, addAccessedStorageKey_accessedStorageKeys,
    Std.HashSet.mem_insert, beq_iff_eq, not_or]
  exact ⟨by rw [(GWorld.currentTarget (w := w))]; decide +kernel, (gatewayRunAfterSetBase_targetKeyCold w) _⟩

private theorem memOfAsk {mid : Devm} {A B : Std.HashSet (Adr × B256)} {k : Adr × B256}
    (hask : ∀ k : Adr × B256, k ∈ mid.accessedStorageKeys ↔ k ∈ Std.HashSet.union A B)
    (h : k ∈ A) : k ∈ mid.accessedStorageKeys :=
  (hask _).mpr (Std.HashSet.mem_union_iff.mpr (Or.inl h))

private theorem gatewayPauseWorld_afterSetGatewaySeam :
    ∃ mid : Devm,
      mid.createdAccounts = (gatewayRunAfterSetBase w).createdAccounts ∧
      mid.stack = [] ∧
      mid.memory = pauseDecodedMemory (gatewayRunMemoryLast w.dur) w.dur ∧
      mid.gasLeft = 42321 ∧
      (∀ key : B256,
        mid.getStorVal configWorldOwner key =
          (gatewayRunAfterSetBase w).getStorVal configWorldOwner key) ∧
      (w.sevm.currentTarget, countSlot pauseWorldPauser) ∈
        mid.accessedStorageKeys ∧
      (w.sevm.currentTarget, expirySlot pauseWorldPauser) ∈
        mid.accessedStorageKeys ∧
      ∀ final : Devm,
        Func.RunCompiled
            ((runtime officialParams).main :: (runtime officialParams).aux)
            w.sevm mid pauseSuccess final →
          Func.RunCompiled
            ((runtime officialParams).main :: (runtime officialParams).aux)
            w.sevm
            ((gatewayRunAfterSetBase w).setMach
              ⟨[], (gatewayRunMemoryLast w.dur), (w.c + 45556), (gatewayRunAfterSetBase w).stateGas⟩)
            pauseAfterSet final := by
  obtain ⟨mid, hcreated, hmidState, hstk, hmem, hgas, _herr, _hout, _hret,
      _hlogs, _hrefund, _hatd, _htrans, hask, _haddrs, _hpaused, _hchain,
      hclose⟩ :=
    pauseAfterSet_gateway_toSuccess_runCompiled_created (hfork := by first | (change CoveredFork .prague; exact CoveredFork.prague) | decide)
      ((runtime officialParams).main :: (runtime officialParams).aux)
      w.sevm (gatewayRunAfterSetBase w) pauseWorldCallee.toB256
      w.dur (gatewayRunMemoryLast w.dur) (gatewayRunImageLast w.dur) 2600 42362
      (by simpa only [gatewayRunMemoryLast,
          gatewayRunMemoryLast] using (gatewayRunMem_wfLast w.dur))
      (by simpa only [gatewayRunMemoryLast, gatewayRunImageLast,
        gatewayRunMemoryLast,
        gatewayRunImageLast] using
        (gatewayRunMem_readsLast w.dur))
      (by simpa only [gatewayRunImageLast,
        gatewayRunImageLast] using (gatewayRunMem_targetLast w.dur))
      (by simpa only [gatewayRunImageLast,
        gatewayRunImageLast] using (gatewayRunMem_durLast w.dur))
      (by simpa only [gatewayRunMemoryLast,
        gatewayRunMemoryLast] using (gatewayRunMem_sizeLast w.dur))
      (by
        simp only [temporalAccountAccessCost, Lift.temporalAccountAccessCost]
        rw [ite_eq_right (show ¬ pauseWorldCallee.toB256.toAdr ∈
            (gatewayRunAfterSetBase w).accessedAddresses from by
          rw [(gatewayRunAfterSetBase_accessedAddresses w)]
          exact Std.HashSet.not_mem_emptyWithCapacity)]
        rfl)
      (gatewayRunAfterSetBase_code w)
      (gatewayRunAfterSetBase_membership w)
      (gatewayRunAfterSetBase_membershipCold w)
      (gatewayRunAfterSetBase_targetPausedZero w)
      (by simpa only [toAdr_toB256] using
        (gatewayPauseWorld_targetPausedOrigZero w))
      (gatewayRunAfterSetBase_resumeCold w)
      rfl
      (GWorldSpec.durNe (w := w))
      (GWorldSpec.projNe (w := w))
      (GWorldSpec.timeLt (w := w))
      (by show (1024 : Nat) ≠ 0; decide)
      (by simpa only [toAdr_toB256] using
        (GWorldSpec.notPrecompile (w := w)))
      (by norm_num only)
      (by
        unfold gatewayPauseChildCost
        split <;> norm_num only)
      (gatewayRunAfterSetBase_ownerProtected w)
  have htargetOwner : pauseWorldCallee.toB256.toAdr ≠
      configWorldOwner := by
    simpa only [(GWorld.currentTarget (w := w))] using
      GWorld.target_ne_owner (w := w)
  have hownerStor : (mid.state.get configWorldOwner).stor =
      ((gatewayRunAfterSetBase w).state.get configWorldOwner).stor := by
    rw [hmidState]
    exact congrArg Acct.stor (State.setStorVal_get_ne _ htargetOwner _ _)
  have hstor : ∀ key : B256,
      mid.getStorVal configWorldOwner key =
        (gatewayRunAfterSetBase w).getStorVal configWorldOwner key := by
    intro key
    exact congrArg (fun stor => stor.get key) hownerStor
  refine ⟨mid, hcreated, hstk, hmem, hgas, hstor,
    memOfAsk hask (gatewayRunAfterSetBase_warmCount w),
    memOfAsk hask (gatewayRunAfterSetBase_warmExpiry w), ?_⟩
  intro final hrun
  have h := hclose final hrun
  simp only [GWorldSpec.child] at h
  rw [show (42362 + w.c + 594 + 2600 : Nat) = w.c + 45556 from by omega] at h
  exact h

private theorem gatewayPauseWorld_originalExpiry :
    getOrigStorVal w.sevm configWorldOwner
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
  change (w.state.get configWorldOwner).stor.get
    (expirySlot pauseWorldPauser) = pauseWorldExpiry
  rw [(GWorld.state_get_breaker (w := w))]
  exact (GWorldSpec.expiry (w := w))

private def gatewayRunDecodedMemory (dur : B256) : Mem :=
  pauseDecodedMemory (gatewayRunMemoryLast dur) dur

private def gatewayRunImage8 (dur : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt (gatewayRunImageLast dur) 256 pauseForSelector.toBytes)
        288 dur.toBytes)
      256 isPausedSelector.toBytes)
    0 (1 : B256).toBytes

private def gatewayRunAfterSetNoLog (w : GWorld) : Devm :=
  indexClearPost w.sevm
    (entryClearPost w.sevm (gatewayRunRemoveBase3 w)
      pauseWorldCallee.toB256 1)
    pauseWorldCallee.toB256 0

private def gatewayRunMemory1 (dur : B256) : Mem :=
  (pauseMemory pauseWorldCallee.toB256 dur).write
    (previousPauserWord * 32).toNat pauseWorldPauser.toBytes

private def gatewayRunImage1 (dur : B256) : Bytes :=
  Bytes.writeAt (pauseImage pauseWorldCallee.toB256 dur)
    (previousPauserWord * 32).toNat pauseWorldPauser.toBytes

omit [GWorldSpec w] in
private theorem gatewayPauseWorld_getOrigStorVal (key : B256) :
    getOrigStorVal w.sevm configWorldOwner key =
      w.stor.get key := by
  change (w.state.get configWorldOwner).stor.get key = _
  rw [(GWorld.state_get_breaker (w := w))]

/-! The created-account set through the walk carriers (cause OS): every carrier
leaves it alone, so the owner's actual original read stays the entry snapshot
word.  Private twins of `LidoCircuitBreakerPauseWorldRun`'s carrier lemmas. -/

private theorem gatewayPauseWorldRun_sload_created (sevm : Sevm) (b : Devm) (k : B256) :
    (temporalSloadBase sevm b k).createdAccounts = b.createdAccounts := by
  unfold temporalSloadBase
  split <;> rfl

private theorem gatewayPauseWorldRun_sstore_created (sevm : Sevm) (b : Devm) (k v : B256) :
    (temporalSstorePost sevm b k v).createdAccounts = b.createdAccounts := rfl

omit [GWorldSpec w] in
/-- At any state whose created-account set is still the entry one, the
machine's actual original read at the CircuitBreaker owner is its entry
snapshot word. -/
private theorem gatewayPauseWorld_actualOrigStor {d : Devm} {key : B256}
    (hd : d.createdAccounts = w.pre.createdAccounts := by
      (try simp only [gatewayRunAfterSetBase, gatewayRunRemoveBase3,
        gatewayRunCountPost, gatewayRunKernelBase,
        indexClearPost, entryClearPost, lengthWritePost, indexWritePost,
        entryWritePost, swapPopClearPost, assignmentPost, assignmentBase,
        foundKernelPost, pauseKernelBase, pauseDurationBase, pauseExpiryBase,
        pauseLockPost, gatewayPauseWorldRun_sload_created, gatewayPauseWorldRun_sstore_created,
        addAccessedStorageKey_createdAccounts, Devm.addLog_createdAccounts,
        Devm.setTransVal_createdAccounts, Devm.setMach_createdAccounts]) <;> rfl) :
    d.getOrigStorVal w.sevm w.sevm.currentTarget key =
      getOrigStorVal w.sevm configWorldOwner key := by
  have hnc : w.sevm.currentTarget ∉ d.createdAccounts := by
    rw [hd]
    exact Std.HashSet.not_mem_emptyWithCapacity
  rw [Devm.getOrigStorVal]
  simp only [hnc, ↓reduceIte]
  rw [(GWorld.currentTarget (w := w))]

omit [GWorldSpec w] in
private theorem gatewayRunAfterSetBase_createdAccounts :
    (gatewayRunAfterSetBase w).createdAccounts = w.pre.createdAccounts := by
  simp only [gatewayRunAfterSetBase, gatewayRunRemoveBase3,
    gatewayRunCountPost, gatewayRunKernelBase,
    indexClearPost, entryClearPost, lengthWritePost, indexWritePost,
    entryWritePost, assignmentPost, assignmentBase,
    pauseKernelBase, pauseDurationBase, pauseExpiryBase,
    pauseLockPost, gatewayPauseWorldRun_sload_created, gatewayPauseWorldRun_sstore_created,
    Devm.addLog_createdAccounts,
    Devm.setTransVal_createdAccounts]

private theorem gatewayPauseWorld_successSuffix :
    ∃ successPre final : Devm,
      Func.RunCompiled
          ((runtime officialParams).main :: (runtime officialParams).aux)
          w.sevm successPre pauseSuccess final ∧
      Func.RunCompiled
          ((runtime officialParams).main :: (runtime officialParams).aux)
          w.sevm
          ((gatewayRunAfterSetBase w).setMach
            ⟨[], (gatewayRunMemoryLast w.dur), (w.c + 45556), (gatewayRunAfterSetBase w).stateGas⟩)
          pauseAfterSet final ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          w.sevm successPre pauseSuccess (.ok final) ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          w.sevm
          ((gatewayRunAfterSetBase w).setMach
            ⟨[], (gatewayRunMemoryLast w.dur), (w.c + 45556), (gatewayRunAfterSetBase w).stateGas⟩)
          pauseAfterSet (.ok final) ∧
      PauseSuccessNoninterference w.sevm
        ((gatewayRunAfterSetBase w).setMach
          ⟨[], (gatewayRunMemoryLast w.dur), (w.c + 45556), (gatewayRunAfterSetBase w).stateGas⟩) successPre := by
  obtain ⟨mid, hcreated, hstk, hmem, hgas, hstor, hwarmCount, hwarmExpiry,
      hclose⟩ :=
    (gatewayPauseWorld_afterSetGatewaySeam w)
  have hmidCount : mid.getStorVal w.sevm.currentTarget
      (countSlot pauseWorldPauser) = 0 := by
    rw [(GWorld.currentTarget (w := w)), hstor]
    exact (gatewayRunAfterSetBase_count w)
  have hmidExpiry : mid.getStorVal w.sevm.currentTarget
      (expirySlot pauseWorldPauser) = pauseWorldExpiry := by
    rw [(GWorld.currentTarget (w := w)), hstor]
    exact (gatewayRunAfterSetBase_expiry w)
  have hW8 := pauseSuccess_zeroCount_ok_runCompiled (hfork := by first | (change CoveredFork .prague; exact CoveredFork.prague) | decide)
    ((runtime officialParams).main :: (runtime officialParams).aux)
    w.sevm mid (gatewayRunDecodedMemory w.dur) (gatewayRunImage8 w.dur)
    pauseWorldCallee.toB256 w.dur pauseWorldPauser
    pauseWorldExpiry pauseWorldExpiry 100 2900 35999
    (by simpa only [gatewayRunDecodedMemory, gatewayRunMemoryLast,
      gatewayRunMemoryLast] using
      (gatewayRunMem_wf8 w.dur))
    (by simpa only [gatewayRunDecodedMemory, gatewayRunMemoryLast, gatewayRunImage8,
      gatewayRunImageLast, gatewayRunMemoryLast,
      gatewayRunImageLast] using (gatewayRunMem_reads8 w.dur))
    (by simpa only [gatewayRunImage8, gatewayRunImageLast,
      gatewayRunImageLast] using
      (gatewayRunMem_target8 w.dur))
    (by simpa only [gatewayRunImage8, gatewayRunImageLast,
      gatewayRunImageLast] using (gatewayRunMem_dur8 w.dur))
    (by
      have hs : (gatewayRunDecodedMemory w.dur).size = 768 := by
        simpa only [gatewayRunDecodedMemory, gatewayRunMemoryLast] using
          (gatewayRunMem_size8 w.dur)
      rw [hs])
    (by
      have hs : (gatewayRunDecodedMemory w.dur).size = 768 := by
        simpa only [gatewayRunDecodedMemory, gatewayRunMemoryLast] using
          (gatewayRunMem_size8 w.dur)
      rw [hs])
    (GWorld.callerWord (w := w)) hmidCount
    (by
      unfold temporalSloadCost
      rw [ite_eq_left hwarmCount]
      rfl)
    hmidExpiry
    ((gatewayPauseWorld_actualOrigStor w
      (hd := hcreated.trans (gatewayRunAfterSetBase_createdAccounts w))).trans
      (gatewayPauseWorld_originalExpiry w))
    hwarmExpiry
    (stubRunSvc_reset (by decide) (by decide))
    (by norm_num only [gCallStipend])
    rfl
  have hmidEta : mid.setMach
      ⟨[], (gatewayRunDecodedMemory w.dur), 35999 + 3322 + 100 + 2900, mid.stateGas⟩ = mid := by
    rw [show (35999 + 3322 + 100 + 2900 : Nat) = 42321 from by norm_num only,
      gatewayRunDecodedMemory, ← hgas, ← hmem, ← hstk]
    rfl
  rw [hmidEta] at hW8
  have hafter := hclose _ hW8
  have hboundary := Func.RunCompiledTo.of_runCompiled hW8
  have hafterTo := Func.RunCompiledTo.of_runCompiled hafter
  refine ⟨mid, _, hW8, hafter, hboundary, hafterTo, ?_⟩
  unfold PauseSuccessNoninterference
  rw [(GWorld.currentTarget (w := w)), (GWorld.callerWord (w := w))]
  constructor
  · rw [hstor, setMach_getStorVal]
  · rw [hstor, setMach_getStorVal]

private theorem gatewayPauseWorld_productionRun :
    ∃ successPre final : Devm,
      Prog.RunCompiledTo w.sevm w.pre
          (runtime officialParams) (.ok final) ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          w.sevm successPre pauseSuccess (.ok final) ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          w.sevm
          ((gatewayRunAfterSetBase w).setMach
            ⟨[], (gatewayRunMemoryLast w.dur), (w.c + 45556), (gatewayRunAfterSetBase w).stateGas⟩)
          pauseAfterSet (.ok final) ∧
      PauseSuccessNoninterference w.sevm
        ((gatewayRunAfterSetBase w).setMach
          ⟨[], (gatewayRunMemoryLast w.dur), (w.c + 45556), (gatewayRunAfterSetBase w).stateGas⟩) successPre := by
  obtain ⟨successPre, final, hsuccess, hafter, hsuccessTo, hafterTo, hni⟩ :=
    (gatewayPauseWorld_successSuffix w)
  have hfin := finishSetPauser_pauseAfterSet_runCompiled (h_push0 := (show CoveredFork w.sevm.benvStat.fork by first | (change CoveredFork .prague; exact CoveredFork.prague) | decide).rules_push0) officialParams
    w.sevm (gatewayRunAfterSetNoLog w) (gatewayRunMemoryLast w.dur) (gatewayRunImageLast w.dur)
    pauseWorldCallee.toB256 pauseWorldPauser 0 [] (w.c + 45556) _ (by decide)
    (by simpa only [gatewayRunMemoryLast, gatewayRunImageLast,
      gatewayRunMemoryLast,
      gatewayRunImageLast] using
      (gatewayRunMem_readsLast w.dur))
    (by simpa only [gatewayRunImageLast,
      gatewayRunImageLast] using (gatewayRunMem_targetLast w.dur))
    (by simpa only [gatewayRunImageLast,
      gatewayRunImageLast] using (gatewayRunMem_prevLast w.dur))
    (by simpa only [gatewayRunImageLast,
      gatewayRunImageLast] using (gatewayRunMem_newLast w.dur))
    (by simpa only [gatewayRunImageLast,
      gatewayRunImageLast] using (gatewayRunMem_contLast w.dur))
    (by
      have hs : (gatewayRunMemoryLast w.dur).size = 768 := by
        simpa only [gatewayRunMemoryLast] using (gatewayRunMem_sizeLast w.dur)
      rw [hs]
      decide)
    (by
      have hs : (gatewayRunMemoryLast w.dur).size = 768 := by
        simpa only [gatewayRunMemoryLast] using (gatewayRunMem_sizeLast w.dur)
      rw [hs])
    rfl
    (by
      simpa only [gatewayRunAfterSetNoLog, gatewayRunAfterSetBase,
        gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase] using hafter)
  rw [show (w.c + 45556 + 1934 : Nat) = w.c + 47490 from by omega] at hfin
  have hrem := removeTarget_toFinish_coldEntry_runCompiled (hfork := by first | (change CoveredFork .prague; exact CoveredFork.prague) | decide) officialParams
    w.sevm (gatewayRunCountPost w) (gatewayRunMemory1 w.dur) (gatewayRunImage1 w.dur)
    pauseWorldCallee.toB256 0 1 [] (by decide)
    pauseWorldCallee.toB256 1 1
    2100 2100 2100 100 100 2900 2900 2900 (w.c + 47490) 0
    (by simpa only [gatewayRunMemory1] using (gatewayRunMem_wf1 w.dur))
    (by simpa only [gatewayRunMemory1, gatewayRunImage1] using (gatewayRunMem_reads1 w.dur))
    (by simpa only [gatewayRunImage1] using (gatewayRunMem_target1 w.dur))
    pauseWorld_calleeValid
    (by decide) (by decide) 768 0 0 0
    (by simpa only [gatewayRunMemory1] using (gatewayRunMem_size1 w.dur))
    (by rw [gatewayRunMemory1, gatewayRunMem_size1])
    (by decide) (by decide) (by decide) (by decide)
    (((gatewayRunStor_countPost_other w)
      pauseWorld_entryOne_ne_assignCallee.symm
      pauseWorld_entryOne_ne_count.symm).trans (GWorldSpec.entry (w := w)))
    (((gatewayRunStor_countPost_other w) pauseWorld_assignCallee_ne_indexCallee
      pauseWorld_indexCallee_ne_count.symm).trans (GWorldSpec.index (w := w)))
    (((gatewayRunStor_countPost_other w) pauseWorld_length_ne_assignCallee.symm
      pauseWorld_length_ne_count.symm).trans (GWorldSpec.length (w := w)))
    ((((gatewayPauseWorld_actualOrigStor w)).trans ((gatewayPauseWorld_getOrigStorVal w) _)).trans (GWorldSpec.entry (w := w)))
    ((((gatewayPauseWorld_actualOrigStor w)).trans ((gatewayPauseWorld_getOrigStorVal w) _)).trans (GWorldSpec.index (w := w)))
    ((((gatewayPauseWorld_actualOrigStor w)).trans ((gatewayPauseWorld_getOrigStorVal w) _)).trans (GWorldSpec.length (w := w)))
    (gatewayRunCost_idxCold w) (gatewayRunCost_lenCold w) (gatewayRunCost_arrCold w)
    stubRunSvc_noop stubRunSvc_noop
    (stubRunSvc_reset (by decide) (by decide))
    (stubRunSvc_reset (by decide) (by decide))
    (stubRunSvc_reset (by decide) (by decide))
    (by decide) (by norm_num only [gCallStipend]; omega) rfl _
    (by dsimp only; rw [Nat.zero_add]; exact hfin)
  rw [show (0 + (w.c + 47490) + 139 + 0 + 0 + 0 + 2100 + 2100 + 2100 + 100 +
    100 + 2900 + 2900 + 2900 : Nat) = w.c + 62829 from by omega] at hrem
  have hglue := afterOldPauser_removeTarget_runCompiled officialParams
    w.sevm (gatewayRunCountPost w) (gatewayRunMemory1 w.dur) (gatewayRunImage1 w.dur) []
    (w.c + 62829) _ (by decide)
    (by simpa only [gatewayRunMemory1, gatewayRunImage1] using (gatewayRunMem_reads1 w.dur))
    (by simpa only [gatewayRunImage1] using (gatewayRunMem_new1 w.dur))
    (by rw [gatewayRunMemory1, gatewayRunMem_size1]; decide)
    (by rw [gatewayRunMemory1, gatewayRunMem_size1])
    hrem
  rw [show (w.c + 62829 + 35 : Nat) = w.c + 62864 from by omega] at hglue
  have hker := setPauserKernel_found_runCompiled (hfork := by first | (change CoveredFork .prague; exact CoveredFork.prague) | decide) officialParams
    w.sevm (gatewayRunKernelBase w)
    (pauseMemory pauseWorldCallee.toB256 w.dur)
    (pauseImage pauseWorldCallee.toB256 w.dur) _
    pauseWorldCallee.toB256 0 pauseWorldPauser 1 pauseWorldPauser 1
    2900 2900 (w.c + 62864) 0
    (pauseMemory_spec pauseWorldCallee.toB256 w.dur).1
    (pauseMemory_spec pauseWorldCallee.toB256 w.dur).2.1
    (pauseMemory_spec pauseWorldCallee.toB256
      w.dur).2.2.2.2.2.1
    (pauseMemory_spec pauseWorldCallee.toB256
      w.dur).2.2.2.2.2.2.1
    pauseWorld_calleeValid pauseWorld_pauserValid
    (pauseMemory_spec pauseWorldCallee.toB256
      w.dur).2.2.2.1
    (pauseMemory_spec pauseWorldCallee.toB256
      w.dur).2.2.2.2.1
    (((gatewayRunStor_kernelBase w) _).trans (GWorldSpec.assignment (w := w)))
    ((((gatewayPauseWorld_actualOrigStor w)).trans ((gatewayPauseWorld_getOrigStorVal w) _)).trans (GWorldSpec.assignment (w := w)))
    (stubRunSvc_reset (by decide) (by decide))
    (((gatewayRunStor_assignPost_other w) pauseWorld_assignCallee_ne_count).trans
      (GWorldSpec.count (w := w)))
    ((((gatewayPauseWorld_actualOrigStor w)).trans ((gatewayPauseWorld_getOrigStorVal w) _)).trans (GWorldSpec.count (w := w)))
    (stubRunSvc_reset (by decide) (by decide))
    (by norm_num only [gCallStipend]; omega) rfl
    (by
      dsimp only [gatewayRunKernelBase, gatewayRunCountPost, gatewayRunMemory1,
        gatewayRunImage1]
      rw [show (1 - 1 : B256) = 0 from by decide]
      rw [Nat.zero_add]
      exact hglue)
  rw [show foundSetPauserKernelPrefixGas w.sevm
      (gatewayRunKernelBase w) pauseWorldCallee.toB256 0 pauseWorldPauser
      2900 2900 = 8122 from by
        simpa only [gatewayRunKernelBase] using (gatewayRunKernelPrefixGas w),
    show (0 + (w.c + 62864) + 8122 : Nat) = w.c + 70986 from by omega] at hker
  have hcalldata := pauseCalldata_facts
    (GWorldSpec.premises (w := w)).calldata
  have hbody := pause_body_runCompiled (hfork := by first | (change CoveredFork .prague; exact CoveredFork.prague) | decide) officialParams w.sevm
    w.pre pauseWorldCallee.toB256 pauseWorldPauser
    pauseWorldExpiry w.dur 2100 2100 2100 (w.c + 70986) _
    hcalldata.1
    (by decide) rfl
    hcalldata.2
    (GWorld.callerWord (w := w))
    (((gatewayRunStor_lockPost w) _).trans (GWorldSpec.assignment (w := w)))
    (gatewayRunCost_assignment w)
    (by
      unfold pauseExpiryBase
      rw [temporalSloadBase_getStorVal]
      exact ((gatewayRunStor_lockPost w) _).trans (GWorldSpec.expiry (w := w)))
    (gatewayRunCost_expiry w)
    (GWorldSpec.timeLtExpiry (w := w))
    (by
      unfold pauseDurationBase pauseExpiryBase
      rw [temporalSloadBase_getStorVal, temporalSloadBase_getStorVal]
      exact ((gatewayRunStor_lockPost w) _).trans (GWorldSpec.duration (w := w)))
    (gatewayRunCost_duration w) rfl hker
  rw [show (w.c + 70986 + (469 + 2100 + 2100 + 2100) : Nat) = w.c + 77755 from by
    omega] at hbody
  have hbodyTo := Func.RunCompiledTo.of_runCompiled hbody
  obtain ⟨hprog, _hcompile⟩ := pause_dispatch_runCompiledTo
    (h_push0 := (show CoveredFork w.sevm.benvStat.fork by first | (change CoveredFork .prague; exact CoveredFork.prague) | decide).rules_push0)
    (h_shifts := (show CoveredFork w.sevm.benvStat.fork by first | (change CoveredFork .prague; exact CoveredFork.prague) | decide).rules_shifts) officialParams
    w.sevm w.pre 0 (w.c + 77755) _
    hcalldata.1
    (GWorldSpec.premises (w := w)).valueZero
    (GWorldSpec.premises (w := w)).selectorEq
    (by
      rw [(GWorldSpec.premises (w := w)).currentTarget]
      exact (GWorldSpec.premises (w := w)).codeAddress)
    (GWorldSpec.premises (w := w)).productionBytes hbodyTo
  have hentry : w.pre.setMach
      ⟨[], Mem.empty, w.c + 77755 + pauseDispatchGas + 0, w.pre.stateGas⟩ =
      w.pre := by
    rw [show (w.c + 77755 + pauseDispatchGas + 0 : Nat) = w.gas from by
      rw [GWorldSpec.gas (w := w)]; omega]
    rfl
  rw [hentry] at hprog
  exact ⟨successPre, final, hprog, hsuccessTo, hafterTo, hni⟩

private def gatewayPauseWorldAfterSetEntry (w : GWorld) : Devm :=
  (gatewayRunAfterSetBase w).setMach ⟨[], (gatewayRunMemoryLast w.dur), (w.c + 45556), (gatewayRunAfterSetBase w).stateGas⟩

omit [GWorldSpec w] in
private theorem gatewayPauseWorldAfterSetEntry_memory :
    (gatewayPauseWorldAfterSetEntry w).memory = (gatewayRunMemoryLast w.dur) := by
  rw [gatewayPauseWorldAfterSetEntry, Devm.memory_setMach]

omit [GWorldSpec w] in
private theorem gatewayRunMemoryLast_wf : Mem.Wf (gatewayRunMemoryLast w.dur) := by
  unfold gatewayRunMemoryLast
  exact (gatewayRunMem_wfLast w.dur)

omit [GWorldSpec w] in
private theorem gatewayRunMemoryLast_reads :
    Mem.Reads (gatewayRunMemoryLast w.dur) (gatewayRunImageLast w.dur) := by
  unfold gatewayRunMemoryLast gatewayRunImageLast
  exact (gatewayRunMem_readsLast w.dur)

omit [GWorldSpec w] in
private theorem gatewayRunImageLast_target :
    Bytes.toB256
      ((gatewayRunImageLast w.dur).sliceD (targetWord * 32).toNat 32 0) =
      pauseWorldCallee.toB256 := by
  unfold gatewayRunImageLast
  exact (gatewayRunMem_targetLast w.dur)

omit [GWorldSpec w] in
private theorem gatewayRunImageLast_duration :
    Bytes.toB256
      ((gatewayRunImageLast w.dur).sliceD (durationWord * 32).toNat 32 0) =
      w.dur := by
  unfold gatewayRunImageLast
  exact (gatewayRunMem_durLast w.dur)

omit [GWorldSpec w] in
private theorem gatewayRunMemoryLast_targetWindow {devm : Devm}
    (hmemory : devm.memory = (gatewayRunMemoryLast w.dur)) :
    MemWordAt devm (targetWord * 32).toNat pauseWorldCallee.toB256 := by
  unfold MemWordAt
  rw [hmemory]
  refine ⟨(gatewayRunMemoryLast_wf w), (gatewayRunImageLast w.dur),
    (gatewayRunMemoryLast_reads w), ?_⟩
  have hlen :
      ((gatewayRunImageLast w.dur).sliceD (targetWord * 32).toNat 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  have htarget := (gatewayRunImageLast_target w)
  rw [← htarget, Bytes.toBytes_toB256_of_length hlen]

omit [GWorldSpec w] in
private theorem gatewayRunMemoryLast_durationWindow {devm : Devm}
    (hmemory : devm.memory = (gatewayRunMemoryLast w.dur)) :
    MemWordAt devm (durationWord * 32).toNat w.dur := by
  unfold MemWordAt
  rw [hmemory]
  refine ⟨(gatewayRunMemoryLast_wf w), (gatewayRunImageLast w.dur),
    (gatewayRunMemoryLast_reads w), ?_⟩
  have hlen :
      ((gatewayRunImageLast w.dur).sliceD (durationWord * 32).toNat 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  have hd := Bytes.toBytes_toB256_of_length hlen
  rw [(gatewayRunImageLast_duration w)] at hd
  exact hd.symm

omit [GWorldSpec w] in
private theorem gatewayPauseWorldAfterSetEntry_ownerCode :
    ((gatewayPauseWorldAfterSetEntry w).getCode
      w.sevm.currentTarget).toList ≠ [] := by
  have addLogCode : ∀ (d : Devm) (l : Log) (a : Adr),
      (d.addLog l).getCode a = d.getCode a := fun _ _ _ => rfl
  have transCode : ∀ (d : Devm) (a : Adr) (k v : B256) (x : Adr),
      (d.setTransVal a k v).getCode x = d.getCode x := fun _ _ _ _ _ => rfl
  have hcarry : (gatewayPauseWorldAfterSetEntry w).getCode configWorldOwner =
      w.pre.getCode configWorldOwner := by
    simp only [gatewayPauseWorldAfterSetEntry, gatewayRunAfterSetBase,
      gatewayRunRemoveBase3, gatewayRunCountPost, gatewayRunKernelBase,
      indexClearPost, entryClearPost, lengthWritePost, indexWritePost,
      entryWritePost, assignmentPost, assignmentBase, pauseKernelBase,
      pauseDurationBase, pauseExpiryBase, pauseLockPost, Devm.getCode_setMach,
      addLogCode, transCode, temporalSstorePost_getCode, temporalSloadBase_getCode]
  rw [(GWorld.currentTarget (w := w)), hcarry]
  change (w.state.get configWorldOwner).code.toList ≠ []
  rw [(GWorld.state_get_breaker (w := w))]
  intro hnil
  have hempty : lidoCircuitBreakerCode officialParams = [] := by
    simpa only [configWorldCode, ByteArray.toList_eq_toList_data,
      List.toList_toArray] using hnil
  exact Prog.compile_ne_nil (by rw [lidoCircuitBreakerCode_compile, hempty])

private theorem gatewayPauseWorld_afterSetAt {final : Devm}
    (hafter : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      w.sevm (gatewayPauseWorldAfterSetEntry w) pauseAfterSet
      (.ok final)) :
    PublicPauseAfterSetAt
      ((runtime officialParams).main :: (runtime officialParams).aux)
      w.sevm w.pre pauseWorldCallee.toB256
      w.dur (gatewayCode controlDeployParams) (.ok final)
      (gatewayPauseWorldAfterSetEntry w) := by
  refine ⟨?_, ?_, ?_, ?_, hafter⟩
  · exact (gatewayRunMemoryLast_targetWindow w)
      (gatewayPauseWorldAfterSetEntry_memory w)
  · exact (gatewayRunMemoryLast_durationWindow w)
      (gatewayPauseWorldAfterSetEntry_memory w)
  · unfold CodeAt gatewayPauseWorldAfterSetEntry
    rw [Devm.getCode_setMach]
    exact (gatewayRunAfterSetBase_code w)
  · rw [(GWorld.currentTarget (w := w)), (GWorld.callerWord (w := w))]
    unfold gatewayPauseWorldAfterSetEntry
    rw [setMach_getStorVal, (gatewayRunAfterSetBase_count w),
      (GWorld.getStorVal (w := w)), (GWorldSpec.count (w := w))]
    decide

/-- The entry-3 closure at a reached entry: hand it a successful production run of
the world, its reached `pauseAfterSet` entry, and the owner's installed code
there. -/
private theorem closedPremises
    {ex : Execution} {final : Devm}
    (publicRun : Prog.RunCompiledTo w.sevm w.pre (runtime officialParams) ex)
    (success : ex = .ok final)
    (entry : Devm)
    (reachedAt : PublicPauseAfterSetAt
      ((runtime officialParams).main :: (runtime officialParams).aux)
      w.sevm w.pre pauseWorldCallee.toB256 w.dur
      (gatewayCode controlDeployParams) ex entry)
    (ownerInstalled : (entry.getCode w.sevm.currentTarget).toList ≠ []) :
    PublicPausePinnedTargetConclusion w.sevm w.pre pauseWorldCallee.toB256 w.dur
      (gatewayCode controlDeployParams)
      (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
      LidoTriggerableWithdrawalsGateway.pausedUntil ex final :=
  publicPause_gatewayPinnedTarget
    (hfork := by first | (change CoveredFork .prague; exact CoveredFork.prague) | decide)
    (GWorldSpec.premises (w := w)) (GWorld.target_ne_owner (w := w))
    (GWorldSpec.notPrecompile (w := w)) publicRun success entry reachedAt ownerInstalled

/-- A concrete production public pause with the installed pinned-target gateway.
The theorem exposes the production run, exact `pauseAfterSet` entry, actual
`pauseSuccess` subrun, explicit callback noninterference, combined hook,
committed outcome family, and the final pinned-target conclusion. -/
theorem closedPublicPause :
    ∃ entry successPre final : Devm,
      Prog.RunCompiledTo w.sevm w.pre
          (runtime officialParams) (.ok final) ∧
      PublicPauseAfterSetAt
          ((runtime officialParams).main :: (runtime officialParams).aux)
          w.sevm w.pre pauseWorldCallee.toB256
          w.dur (gatewayCode controlDeployParams) (.ok final) entry ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          w.sevm successPre pauseSuccess (.ok final) ∧
      PauseSuccessNoninterference w.sevm entry successPre ∧
      LidoPinnedBoundaryExecutions
          ((runtime officialParams).main :: (runtime officialParams).aux)
          w.sevm entry pauseWorldCallee
          (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams) w.dur (.ok final) ∧
      PublicPauseCommittedOutcomes w.sevm w.pre
          pauseWorldCallee.toB256 w.dur
          (gatewayCode controlDeployParams) (.ok final) ∧
      PublicPausePinnedTargetConclusion w.sevm
          w.pre pauseWorldCallee.toB256 w.dur
          (gatewayCode controlDeployParams) (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
          LidoTriggerableWithdrawalsGateway.pausedUntil (.ok final) final := by
  obtain ⟨successPre, final, hprog, hsuccess, hafter, hni⟩ :=
    (gatewayPauseWorld_productionRun w)
  have hafter' : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      w.sevm (gatewayPauseWorldAfterSetEntry w) pauseAfterSet
      (.ok final) := by
    simpa only [gatewayPauseWorldAfterSetEntry] using hafter
  have reached := (gatewayPauseWorld_afterSetAt w) hafter'
  have hook := gatewayBoundaryExecutions_of_afterSet_ok (hfork := by first | (change CoveredFork .prague; exact CoveredFork.prague) | decide)
    (fs := (runtime officialParams).main :: (runtime officialParams).aux)
    (sevm := w.sevm) (entry := (gatewayPauseWorldAfterSetEntry w))
    (final := final) (target := pauseWorldCallee)
    (duration := w.dur)
    (by rfl) (by rfl) pauseWorld_callee_ne_owner
    (GWorldSpec.notPrecompile (w := w))
    (by
      unfold gatewayPauseWorldAfterSetEntry
      rw [Devm.getCode_setMach, ← show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from
        toAdr_toB256 pauseWorldCallee]
      exact (gatewayRunAfterSetBase_code w))
    (gatewayPauseWorldAfterSetEntry_ownerCode w)
    reached.1 reached.2.1 (GWorldSpec.premises (w := w)).dynamic hafter'
  have conclusion := (closedPremises w) hprog rfl
    (gatewayPauseWorldAfterSetEntry w) reached
    (gatewayPauseWorldAfterSetEntry_ownerCode w)
  refine ⟨(gatewayPauseWorldAfterSetEntry w), successPre, final, hprog, reached,
    hsuccess, ?_, hook, conclusion.1, conclusion⟩
  simpa only [gatewayPauseWorldAfterSetEntry] using hni

end LidoCircuitBreakerTwgRun

end Blanc.Composition
