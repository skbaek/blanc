import Blanc.Lift.HistAccessWalk
import Blanc.Lift.ExactWalkSolc

/-!
# Frame bookkeeping across the historical storage steps

`afterSloadH` and `afterSstoreH` (`Blanc/Lift/HistAccessWalk.lean`) are the successors of
`SLOAD`/`SSTORE` under the frame's actual access schedule and refund regime. A settled creation
or call reads two more of their fields: the accounts scheduled for deletion, which neither step
touches, and the refund counter, which `SLOAD` leaves alone and which the legacy (pre-EIP-1283)
`SSTORE` schedule changes only when a nonzero slot is cleared.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

theorem afterSloadH_accountsToDelete (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).accountsToDelete = base.accountsToDelete := by
  unfold afterSloadH
  split
  · exact afterSload_accountsToDelete
  · rfl

theorem afterSloadH_refundCounter (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).refundCounter = base.refundCounter := by
  unfold afterSloadH
  split
  · exact afterSload_refundCounter
  · rfl

theorem afterSstoreH_accountsToDelete (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstoreH sevm base key value).accountsToDelete = base.accountsToDelete := by
  unfold afterSstoreH storageAccessH
  split
  · rfl
  · split <;> rfl

/-- Under the legacy `SSTORE` refund schedule (no net metering), writing a nonzero word leaves
the refund counter unchanged. -/
theorem afterSstoreH_refundCounter_legacy {sevm : Sevm} (base : Devm) (key : B256) {value : B256}
    (legacy : sevm.benvStat.rules.sstore.netMetering = false) (nonzero : value ≠ 0) :
    (afterSstoreH sevm base key value).refundCounter = base.refundCounter := by
  have refund : sstoreRefundH sevm.benvStat.rules value
      (base.getOrigStorVal sevm sevm.currentTarget key)
      (base.getStorVal sevm.currentTarget key) base.refundCounter = base.refundCounter := by
    unfold sstoreRefundH
    rw [legacy]
    unfold sstoreLegacyRefundCounter
    rw [ite_eq_right (fun h => nonzero h.2)]
  exact refund

end Blanc.Lift
