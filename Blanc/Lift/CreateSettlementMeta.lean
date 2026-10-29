import Blanc.Lift.Deploy
import Blanc.Lift.HistAccessWalkFacts
import Blanc.Lift.HistAccessMeta

/-! Metadata projections used by historical creation settlement.
All equations are over symbolic machines; no concrete memory image is evaluated. -/

namespace Blanc.Lift

open Jaune

theorem St_meta (b : Devm) (S : List B256) (M : Mem) (G : Nat) :
    (St b S M G).meta = b.meta := rfl

theorem shaResume_accountsToDelete (p c : Devm) (oi : Nat) :
    (((incorporateChildOnSuccess p c c.output).setMach
      ⟨1 :: p.stack, p.memory, p.gasLeft + c.gasLeft, p.stateGas⟩).memWrite
      oi (c.output.take 32)).accountsToDelete = p.accountsToDelete.union c.accountsToDelete := rfl

theorem recordTouch_accountsToDelete (rules : ForkRules) (cond : Bool) (a : Adr) (d : Devm) :
    (d.recordTouch rules cond a).accountsToDelete = d.accountsToDelete := by
  unfold Devm.recordTouch
  split <;> rfl

/-- SHA successor facts retaining the deletion set needed by historical CREATE settlement. -/
structure ShaCallPostDelete (b b' : Devm) (rd : Bytes) extends ShaCallPost b b' rd where
  deletions : b'.accountsToDelete = b.accountsToDelete

/-- A constructor with zero refund and logs, the inherited deletion set, and a newly created target. -/
structure CreateRunMeta (target : Adr) (deletions : AdrSet) (b : Devm) : Prop where
  refund : b.refundCounter = 0
  logs : b.logs = []
  deletions : b.accountsToDelete = deletions
  created : target ∈ b.createdAccounts

theorem CreateRunMeta.of_meta_eq {target : Adr} {deletions : AdrSet} {a b : Devm}
    (h : CreateRunMeta target deletions a) (heq : b.meta = a.meta) :
    CreateRunMeta target deletions b := by
  have hr : b.refundCounter = a.refundCounter := congrArg Meta.refundCounter heq
  have hl : b.logs = a.logs := congrArg Meta.logs heq
  have hd : b.accountsToDelete = a.accountsToDelete := congrArg Meta.accountsToDelete heq
  have hc : b.createdAccounts = a.createdAccounts := congrArg Meta.createdAccounts heq
  exact ⟨hr.trans h.refund, hl.trans h.logs, hd.trans h.deletions, by rw [hc]; exact h.created⟩

theorem CreateRunMeta.st {target : Adr} {deletions : AdrSet} {b : Devm}
    (h : CreateRunMeta target deletions b) (S : List B256) (M : Mem) (G : Nat) :
    CreateRunMeta target deletions (St b S M G) := h.of_meta_eq (St_meta b S M G)

theorem CreateRunMeta.returnPost {target : Adr} {deletions : AdrSet} {d : Devm}
    (h : CreateRunMeta target deletions d) (i sz : B256) (S : List B256) :
    CreateRunMeta target deletions (returnPost d i sz S) :=
  ⟨h.refund, h.logs, h.deletions, h.created⟩

theorem sstoreRefundH_zero_zero (rules : ForkRules) (value : B256) (rc : Int) :
    sstoreRefundH rules value 0 0 rc = rc := by
  unfold sstoreRefundH
  split
  · simp only [sstoreLegacyRefundCounter, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
  · rename_i g
    by_cases hv : value = 0 <;>
      simp only [sstoreFlatRefundCounter, hv, ne_eq, not_true_eq_false, false_and,
        ↓reduceIte, eq_comm, not_false_eq_true]
  · by_cases hv : value = 0 <;>
      simp only [sstoreNewRefundCounter, hv, ne_eq, not_true_eq_false, false_and,
        ↓reduceIte, eq_comm, not_false_eq_true]

theorem CreateRunMeta.afterSstoreH {sevm : Sevm} {b : Devm} {key value : B256}
    {deletions : AdrSet} (h : CreateRunMeta sevm.currentTarget deletions b)
    (hzero : b.getStorVal sevm.currentTarget key = 0) :
    CreateRunMeta sevm.currentTarget deletions (afterSstoreH sevm b key value) := by
  have horig : b.getOrigStorVal sevm sevm.currentTarget key = 0 := by
    unfold Devm.getOrigStorVal
    rw [ite_eq_left h.created]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [afterSstoreH_refundCounter, horig, hzero, sstoreRefundH_zero_zero]
    exact h.refund
  · rw [afterSstoreH_logs]
    exact h.logs
  · rw [afterSstoreH_accountsToDelete]
    exact h.deletions
  · rw [afterSstoreH_createdAccounts]
    exact h.created

end Blanc.Lift

