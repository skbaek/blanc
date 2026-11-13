import Blanc.JointGloasReplayStep
import Blanc.Lift.BuilderRequest.Deposit.Latch
import Blanc.Lift.BuilderRequest.Exit.Delivery
import Blanc.Lift.SystemWordWriter

/-!
# Finite, proof-backed pieces of builder-request applicability (`P5`)

This module supplies computational `Decidable` checks (never `Classical.propDecidable` or unsafe
extensional map `BEq`) for the finite checkpoint, configuration, and per-state registry-bound
obligations of `ValidJointG` and `BuilderCheckpointObservation`, together with symbolic/Amsterdam
system-latch execution witnesses for both builder contracts (`depositLatchExec`,
`positiveDepositLatch`, `exitLatchExec`, `positiveExitLatch`). It does not construct a full
`ValidJointG` or assume a successful execution trace.
-/
namespace Blanc.Composition.BuilderRequestApplicability.Checks

open Jaune JauneConsensus Blanc.Lift Blanc.Lift.RequestSystem

/-- Structural equality with the entire deployed exit storage, including absence
of every other key. This deliberately does not use extensional map BEq. -/
def exitStorageDecidable (s : Stor) : Decidable (s = BuilderRequest.Exit.deployedStorage) := by
  rcases s with ⟨⟨tree, wf⟩⟩
  cases tree with
  | leaf => exact isFalse (by intro h; cases h)
  | inner n k v l r =>
    cases l with
    | inner => exact isFalse (by intro h; cases h)
    | leaf =>
      cases r with
      | inner => exact isFalse (by intro h; cases h)
      | leaf =>
        exact decidable_of_iff (n = 1 ∧ k = 0 ∧ v = B256.max) (by
          constructor
          · rintro ⟨rfl, rfl, rfl⟩; rfl
          · intro h; cases h; exact ⟨rfl, rfl, rfl⟩)

/-- Structural equality with whole empty storage (`Stor.empty`), matching the underlying
`Std.TreeMap` leaf representation without `Classical.propDecidable` or extensional map `BEq`. -/
def emptyStorageDecidable (s : Stor) : Decidable (s = Stor.empty) := by
  rcases s with ⟨⟨tree, wf⟩⟩
  cases tree with
  | leaf => exact isTrue rfl
  | inner => exact isFalse (by intro h; cases h)

/-- Finite checkpoint fields supported by the initial prototype. -/
def Checkpoint (bls : Bool) (depositCode exitCode : ByteArray)
    (depositStorage exitStorage : Stor) : Prop :=
  bls = true ∧ depositCode = BuilderRequest.Deposit.code ∧
    exitCode = BuilderRequest.Exit.code ∧ depositStorage = Stor.empty ∧
    exitStorage = BuilderRequest.Exit.deployedStorage

instance (bls : Bool) (depositCode exitCode : ByteArray) (depositStorage exitStorage : Stor) :
    Decidable (Checkpoint bls depositCode exitCode depositStorage exitStorage) := by
  letI := exitStorageDecidable exitStorage
  unfold Checkpoint
  infer_instance

/-- Complete five-account/storage checkpoint obligation consumed by `ValidJointG`
(`noSystemCode`, `depositInstalled`, `depositFresh`, `exitInstalled`, `exitFresh`) and
`BuilderCheckpointObservation`: empty code at `systemAddress`, canonical runtime codes at both
builder addresses, whole `Stor.empty` at the deposit address, and whole `Exit.deployedStorage`
at the exit address. -/
def FullCheckpoint (sysCode depositCode exitCode : ByteArray)
    (depositStorage exitStorage : Stor) : Prop :=
  sysCode = ByteArray.empty ∧
    depositCode = BuilderRequest.Deposit.code ∧
    depositStorage = Stor.empty ∧
    exitCode = BuilderRequest.Exit.code ∧
    exitStorage = BuilderRequest.Exit.deployedStorage

instance instDecidableFullCheckpoint (sysCode depositCode exitCode : ByteArray)
    (depositStorage exitStorage : Stor) :
    Decidable (FullCheckpoint sysCode depositCode exitCode depositStorage exitStorage) := by
  letI := emptyStorageDecidable depositStorage
  letI := exitStorageDecidable exitStorage
  unfold FullCheckpoint
  infer_instance

/-- `FullCheckpoint` evaluated directly on a `BlockChain` checkpoint's account/storage state. -/
def FullCheckpointAt (checkpoint : BlockChain) : Prop :=
  FullCheckpoint
    (checkpoint.state.getCode systemAddress)
    (checkpoint.state.getCode BuilderRequest.Deposit.Creation.address)
    (checkpoint.state.getCode BuilderRequest.Exit.Creation.address)
    (checkpoint.state.getStor BuilderRequest.Deposit.Creation.address)
    (checkpoint.state.getStor BuilderRequest.Exit.Creation.address)

instance instDecidableFullCheckpointAt (checkpoint : BlockChain) :
    Decidable (FullCheckpointAt checkpoint) := by
  unfold FullCheckpointAt
  infer_instance

/-- The five preset/consensus configuration inequalities of `ValidJointG`:
`quorumPositive`, `inclusionDelay`, `exitDelayPos`, `exitDelayBelow`, and `slotsPerEpoch`. -/
def ConfigBounds (P : Preset) (ccfg : Config) : Prop :=
  2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT ∧
  1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY ∧
  0 < ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY ∧
  ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY < 2 ^ 63 ∧
  2 ≤ P.SLOTS_PER_EPOCH

instance instDecidableConfigBounds (P : Preset) (ccfg : Config) :
    Decidable (ConfigBounds P ccfg) := by
  unfold ConfigBounds
  infer_instance

theorem configBounds_iff {P : Preset} {ccfg : Config} :
    ConfigBounds P ccfg ↔
      2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT ∧
      1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY ∧
      0 < ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY ∧
      ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY < 2 ^ 63 ∧
      2 ≤ P.SLOTS_PER_EPOCH := Iff.rfl

/-- Validator registry size of a joint state (matching `GJointState.validatorCount`). -/
def stateValidatorCount {P : Preset} : GJointState P → Nat
  | .pre s => s.beacon.validators.toArray.size
  | .gloas b _ _ => b.validators.toArray.size

/-- Builder registry size of a joint state (matching `GJointState.builderCount`). -/
def stateBuilderCount {P : Preset} : GJointState P → Nat
  | .pre _ => 0
  | .gloas b _ _ => b.builders.toArray.size

/-- Finite per-state N7 registry bounds over a list of `GJointState P` states:
`validatorsBound` (`≤ 2^40`) and `buildersBound` (`≤ 2^40`). -/
def RegistryBounds {P : Preset} (states : List (GJointState P)) : Prop :=
  (∀ st ∈ states, stateValidatorCount st ≤ 2 ^ 40) ∧
  (∀ st ∈ states, stateBuilderCount st ≤ 2 ^ 40)

instance instDecidableRegistryBounds {P : Preset} (states : List (GJointState P)) :
    Decidable (RegistryBounds states) :=
  decidable_of_iff
    (states.all (fun st => decide (stateValidatorCount st ≤ 2 ^ 40)) = true ∧
      states.all (fun st => decide (stateBuilderCount st ≤ 2 ^ 40)) = true)
    (by
      unfold RegistryBounds
      simp only [List.all_eq_true, decide_eq_true_eq])

theorem registryBounds_iff {P : Preset} {states : List (GJointState P)} :
    RegistryBounds states ↔
      (∀ st ∈ states, stateValidatorCount st ≤ 2 ^ 40) ∧
      (∀ st ∈ states, stateBuilderCount st ≤ 2 ^ 40) := Iff.rfl

/-- Combined computationally decidable applicability bundle covering all 12 finite
checkpoint/config/registry-list obligations of `ValidJointG`. -/
def FiniteApplicability {P : Preset} (ccfg : Config) (checkpoint : BlockChain)
    (states : List (GJointState P)) : Prop :=
  FullCheckpointAt checkpoint ∧ ConfigBounds P ccfg ∧ RegistryBounds states

instance instDecidableFiniteApplicability {P : Preset} (ccfg : Config) (checkpoint : BlockChain)
    (states : List (GJointState P)) :
    Decidable (FiniteApplicability ccfg checkpoint states) := by
  unfold FiniteApplicability
  infer_instance

/-- The original registered deposit certificate constructs the original `Exec`
for its positive nonempty-calldata latch path. No child trace is an input. -/
theorem depositLatchExec {s : Sevm} {b : Devm} {G : Nat}
    (code : s.code = BuilderRequest.Deposit.code)
    (fork : s.benvStat.fork = .amsterdam) (dynamic : s.isStatic = false)
    (caller : s.caller = systemAddress) (data : s.data.length.toB256 ≠ 0)
    (ready : Ready s b [2, 3, 0, 1]) (gas : gCallStipend < G) :
    Nonempty (Exec 0 s
      (St b [] .empty (G + BuilderRequest.latchCost BuilderRequest.Deposit.sysPath s b))
      (.ok (BuilderRequest.latchPost BuilderRequest.Deposit.sysPath s b G))) := by
  have run := BuilderRequest.latch_frame_run BuilderRequest.Deposit.sysPath
    BuilderRequest.Deposit.sysWords rfl rfl fork dynamic caller data ready gas
  exact lift_exact_noExec BuilderRequest.Deposit.sysPath.check
    BuilderRequest.Deposit.sysPath.jumps code BuilderRequest.Deposit.sysPath.noExec
    ⟨_, BuilderRequest.Deposit.sysPath.root, run⟩

/-- A positive registered deposit system-message run, from any Amsterdam environment.
The original certificate, gas bound and readiness laws discharge every run premise. -/
theorem positiveDepositLatch (benv : Benv) (fork : benv.stat.fork = .amsterdam) :
    let msg := systemCallMsg benv BuilderRequest.Deposit.Creation.address
      BuilderRequest.Deposit.code [1]
    let s := initSevm msg
    let b := systemCallBase msg
    Nonempty (Exec 0 s b (.ok (BuilderRequest.latchPost BuilderRequest.Deposit.sysPath s b
      (systemTransactionGas - BuilderRequest.latchCost BuilderRequest.Deposit.sysPath s b)))) := by
  dsimp only
  let s := initSevm (systemCallMsg benv BuilderRequest.Deposit.Creation.address
    BuilderRequest.Deposit.code [1])
  let b := systemCallBase (systemCallMsg benv BuilderRequest.Deposit.Creation.address
    BuilderRequest.Deposit.code [1])
  have bound := BuilderRequest.latchCost_le BuilderRequest.Deposit.sysCall.memory s b
  have room := BuilderRequest.Deposit.sysCall.room
  have cap := BuilderRequest.Deposit.sysCall.bound_le
  have run := depositLatchExec (s := s) (b := b)
    (G := systemTransactionGas - BuilderRequest.latchCost BuilderRequest.Deposit.sysPath s b)
    rfl fork rfl rfl (by change (1 : B256) ≠ 0; decide) (SysPath.ready_base (k := BuilderRequest.Deposit.sysPath) (benv := benv)
      (target := BuilderRequest.Deposit.Creation.address) (data := [1]) fork) (by omega)
  rw [show systemTransactionGas - BuilderRequest.latchCost BuilderRequest.Deposit.sysPath s b +
    BuilderRequest.latchCost BuilderRequest.Deposit.sysPath s b = systemTransactionGas by omega,
    systemCallBase_St] at run
  exact run

/-- The original registered exit certificate constructs the original `Exec`
for its positive nonempty-calldata latch path. No child trace is an input. -/
theorem exitLatchExec {s : Sevm} {b : Devm} {G : Nat}
    (code : s.code = BuilderRequest.Exit.code)
    (fork : s.benvStat.fork = .amsterdam) (dynamic : s.isStatic = false)
    (caller : s.caller = systemAddress) (data : s.data.length.toB256 ≠ 0)
    (ready : Ready s b [2, 3, 0, 1]) (gas : gCallStipend < G) :
    Nonempty (Exec 0 s
      (St b [] .empty (G + BuilderRequest.latchCost BuilderRequest.Exit.sysPath s b))
      (.ok (BuilderRequest.latchPost BuilderRequest.Exit.sysPath s b G))) := by
  have run := BuilderRequest.latch_frame_run BuilderRequest.Exit.sysPath
    BuilderRequest.Exit.sysWords rfl rfl fork dynamic caller data ready gas
  exact lift_exact_noExec BuilderRequest.Exit.sysPath.check
    BuilderRequest.Exit.sysPath.jumps code BuilderRequest.Exit.sysPath.noExec
    ⟨_, BuilderRequest.Exit.sysPath.root, run⟩

/-- A positive registered exit system-message run, from any Amsterdam environment.
The original certificate, gas bound and readiness laws discharge every run premise. -/
theorem positiveExitLatch (benv : Benv) (fork : benv.stat.fork = .amsterdam) :
    let msg := systemCallMsg benv BuilderRequest.Exit.Creation.address
      BuilderRequest.Exit.code [1]
    let s := initSevm msg
    let b := systemCallBase msg
    Nonempty (Exec 0 s b (.ok (BuilderRequest.latchPost BuilderRequest.Exit.sysPath s b
      (systemTransactionGas - BuilderRequest.latchCost BuilderRequest.Exit.sysPath s b)))) := by
  dsimp only
  let s := initSevm (systemCallMsg benv BuilderRequest.Exit.Creation.address
    BuilderRequest.Exit.code [1])
  let b := systemCallBase (systemCallMsg benv BuilderRequest.Exit.Creation.address
    BuilderRequest.Exit.code [1])
  have bound := BuilderRequest.latchCost_le BuilderRequest.Exit.sysCall.memory s b
  have room := BuilderRequest.Exit.sysCall.room
  have cap := BuilderRequest.Exit.sysCall.bound_le
  have run := exitLatchExec (s := s) (b := b)
    (G := systemTransactionGas - BuilderRequest.latchCost BuilderRequest.Exit.sysPath s b)
    rfl fork rfl rfl (by change (1 : B256) ≠ 0; decide)
    (SysPath.ready_base (k := BuilderRequest.Exit.sysPath) (benv := benv)
      (target := BuilderRequest.Exit.Creation.address) (data := [1]) fork) (by omega)
  rw [show systemTransactionGas - BuilderRequest.latchCost BuilderRequest.Exit.sysPath s b +
    BuilderRequest.latchCost BuilderRequest.Exit.sysPath s b = systemTransactionGas by omega,
    systemCallBase_St] at run
  exact run

/-- The supported finite fields accept the actual canonical deployment, with BLS enabled. -/
theorem canonicalCheckpoint : Checkpoint true BuilderRequest.Deposit.code BuilderRequest.Exit.code
    Stor.empty BuilderRequest.Exit.deployedStorage := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `FullCheckpoint` accepts the canonical five-account/storage deployment. -/
theorem canonicalFullCheckpoint : FullCheckpoint ByteArray.empty BuilderRequest.Deposit.code
    BuilderRequest.Exit.code Stor.empty BuilderRequest.Exit.deployedStorage :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Compatibility bridge between `Checkpoint` and `FullCheckpoint` when `sysCode` is empty. -/
theorem checkpoint_iff_bls_and_fullCheckpoint {bls : Bool}
    {sysCode depositCode exitCode : ByteArray} {depositStorage exitStorage : Stor}
    (hsys : sysCode = ByteArray.empty) :
    Checkpoint bls depositCode exitCode depositStorage exitStorage ↔
      bls = true ∧ FullCheckpoint sysCode depositCode exitCode depositStorage exitStorage := by
  unfold Checkpoint FullCheckpoint
  constructor
  · rintro ⟨hbls, hd, he, hds, hes⟩
    exact ⟨hbls, hsys, hd, hds, he, hes⟩
  · rintro ⟨hbls, -, hd, hds, he, hes⟩
    exact ⟨hbls, hd, he, hds, hes⟩

end Blanc.Composition.BuilderRequestApplicability.Checks
