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

end Blanc.Composition.BuilderRequestApplicability.Checks
