import Blanc.JointGloasReplayStep
import Blanc.Lift.BuilderRequest.Deposit.Latch
import Blanc.Lift.BuilderRequest.Exit.Delivery
import Blanc.Lift.SystemWordWriter

/-! Finite, proof-backed pieces of builder-request applicability. This module does
not construct `ValidJointG` or assume a successful execution trace. -/
namespace Blanc.Composition.BuilderRequestApplicability.Checks

open Jaune Blanc.Lift Blanc.Lift.RequestSystem

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

/-- Finite checkpoint fields supported by this first prototype. -/
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

/-- A positive registered system-message run, from any Amsterdam environment.
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

/-- The supported finite fields accept the actual canonical deployment, with BLS enabled. -/
theorem canonicalCheckpoint : Checkpoint true BuilderRequest.Deposit.code BuilderRequest.Exit.code
    Stor.empty BuilderRequest.Exit.deployedStorage := ⟨rfl, rfl, rfl, rfl, rfl⟩

end Blanc.Composition.BuilderRequestApplicability.Checks
