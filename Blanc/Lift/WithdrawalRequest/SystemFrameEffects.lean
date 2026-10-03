import Blanc.Lift.WithdrawalRequest.SystemProtocol
import Blanc.Lift.ExactWalkSolc

/-!
# What the 7002 system frame leaves untouched

The canonical system path (`systemFramePost`) is a sequence of `SLOAD`s, `SSTORE`s to the
predeploy, machine updates and a `RETURN`.  It therefore keeps every account's code, appends
no log and schedules no account for deletion, whatever frame it runs in: the system call
itself, or a frame whose caller is SYSTEM_ADDRESS inside a user transaction
(`SystemDrain.drain_exec`).
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-! ## Code -/

/-- `St` preserves every account's code: it only replaces the machine. -/
theorem St_getCode (b : Devm) (S : List B256) (M : Mem) (G : Nat) (address : Adr) :
    (Blanc.Lift.St b S M G).getCode address = b.getCode address := by
  simp only [Blanc.Lift.St, Devm.getCode_state, Devm.setMach_state]

/-- `returnPost` preserves every account's code: it only replaces machine,
memory window and output. -/
theorem returnPost_getCode (d : Devm) (i sz : B256) (S : List B256) (address : Adr) :
    (Blanc.Lift.returnPost d i sz S).getCode address = d.getCode address := by
  have hstate : (Blanc.Lift.returnPost d i sz S).state = d.state := by
    simp only [Blanc.Lift.returnPost, Devm.withOutput_state, Devm.memRead_state,
      Devm.setMach_state]
  simp only [Devm.getCode_state, hstate]

/-- One queue-loop body preserves every account's code: three `SLOAD`s. -/
theorem systemBodyBase_getCode (sevm : Sevm) (base : Devm) (head index : B256)
    (address : Adr) :
    (systemBodyBase sevm base head index).getCode address = base.getCode address := by
  simp only [systemBodyBase, systemBodyBase2, systemBodyBase1, Blanc.afterSload_getCode]

/-- The queue loop preserves every account's code, mirroring `systemLoopFold_storage`. -/
theorem systemLoopFold_getCode (sevm : Sevm) (head : B256) (index remaining : Nat)
    (base : Devm) (memory : Mem) (address : Adr) :
    (systemLoopFold sevm head index remaining base memory).base.getCode address =
      base.getCode address := by
  induction remaining generalizing index base memory with
  | zero => rfl
  | succ remaining ih =>
    simp only [systemLoopFold]
    rw [ih, systemBodyBase_getCode]

/-- Queue setup preserves every account's code: two `SLOAD`s. -/
theorem systemSetupBase_getCode (sevm : Sevm) (base : Devm) (address : Adr) :
    (systemSetupBase sevm base).getCode address = base.getCode address := by
  simp only [systemSetupBase, Blanc.afterSload_getCode]

/-- The whole queue segment preserves every account's code, mirroring
`systemQueuePost_storage`. -/
theorem systemQueuePost_getCode (sevm : Sevm) (base : Devm) (memory : Mem) (address : Adr) :
    (systemQueuePost sevm base memory).base.getCode address = base.getCode address := by
  rw [systemQueuePost, systemLoopFold_getCode, systemSetupBase_getCode]

/-- The whole 7002 system frame preserves every account's code: every layer is
an `SLOAD`, an `SSTORE`, `RETURN` or a machine update. Mirrors
`systemFramePost_other_storage`, with no side condition since stores never touch
code. -/
theorem systemFramePost_getCode (sevm : Sevm) (base : Devm) (memory : Mem)
    (gas : Nat) (address : Adr) :
    (systemFramePost sevm base memory gas).getCode address = base.getCode address := by
  rw [systemFramePost, systemBookkeepingPost, returnPost_getCode, St_getCode]
  simp only [systemBookkeepingBase, systemExcessStore, systemCountRead, systemExcessRead,
    Blanc.afterSstore_getCode, Blanc.afterSload_getCode]
  unfold systemFramePointers systemPointerBase
  split
  · simp only [Blanc.afterSstore_getCode, systemQueuePost_getCode]
  · simp only [Blanc.afterSstore_getCode, systemQueuePost_getCode]

/-! ## Logs and deletions -/

theorem systemQueuePost_logs_deletions (sevm : Sevm) (base : Devm) (memory : Mem) :
    (systemQueuePost sevm base memory).base.logs = base.logs ∧
    (systemQueuePost sevm base memory).base.accountsToDelete = base.accountsToDelete := by
  have loop : ∀ (head : B256) (index remaining : Nat) (b : Devm) (m : Mem),
      (systemLoopFold sevm head index remaining b m).base.logs = b.logs ∧
      (systemLoopFold sevm head index remaining b m).base.accountsToDelete =
        b.accountsToDelete := by
    intro head index remaining
    induction remaining generalizing index with
    | zero => intro b m; exact ⟨rfl, rfl⟩
    | succ remaining ih =>
      intro b m
      simp only [systemLoopFold]
      rw [(ih _ _ _).1, (ih _ _ _).2]
      simp only [systemBodyBase, systemBodyBase2, systemBodyBase1, Blanc.afterSload_logs,
        Blanc.Lift.afterSload_accountsToDelete, and_self]
  rw [systemQueuePost, (loop _ _ _ _ _).1, (loop _ _ _ _ _).2]
  simp only [systemSetupBase, Blanc.afterSload_logs, Blanc.Lift.afterSload_accountsToDelete,
    and_self]

/-- The whole 7002 system frame appends no log and schedules no deletion. -/
theorem systemFramePost_logs_deletions (sevm : Sevm) (base : Devm) (memory : Mem)
    (gas : Nat) :
    (systemFramePost sevm base memory gas).logs = base.logs ∧
    (systemFramePost sevm base memory gas).accountsToDelete = base.accountsToDelete := by
  have hq := systemQueuePost_logs_deletions sevm base memory
  have hret : ∀ (d : Devm) (i sz : B256) (S : List B256),
      (Blanc.Lift.returnPost d i sz S).logs = d.logs ∧
      (Blanc.Lift.returnPost d i sz S).accountsToDelete = d.accountsToDelete :=
    fun _ _ _ _ => ⟨rfl, rfl⟩
  have hSt : ∀ (d : Devm) (S : List B256) (M : Mem) (G : Nat),
      (Blanc.Lift.St d S M G).logs = d.logs ∧
      (Blanc.Lift.St d S M G).accountsToDelete = d.accountsToDelete :=
    fun _ _ _ _ => ⟨rfl, rfl⟩
  rw [systemFramePost, systemBookkeepingPost, (hret _ _ _ _).1, (hret _ _ _ _).2,
    (hSt _ _ _ _).1, (hSt _ _ _ _).2]
  simp only [systemBookkeepingBase, systemExcessStore, systemCountRead, systemExcessRead,
    Blanc.afterSstore_logs, Blanc.afterSload_logs, Blanc.afterSstore_accountsToDelete,
    Blanc.Lift.afterSload_accountsToDelete]
  unfold systemFramePointers systemPointerBase
  split
  · simp only [Blanc.afterSstore_logs, Blanc.afterSstore_accountsToDelete, hq.1, hq.2,
      and_self]
  · simp only [Blanc.afterSstore_logs, Blanc.afterSstore_accountsToDelete, hq.1, hq.2,
      and_self]

end Blanc.Lift.WithdrawalRequest
