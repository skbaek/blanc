import Blanc.Lift.HistAccessWalk

/-!
# The `SSTORE` refund counter does not fall on a clean or non-zero slot

Under every `SSTORE` regime a store lowers the refund counter only when it re-sets a slot that
was non-zero at the transaction's start and is zero now (EIP-2200/EIP-3529: reversing an earlier
clear's refund). So a store whose slot started at zero, or is non-zero now, never lowers it:

* `sstoreRefundH_ge` — for the refund function itself, under any rules;
* `afterSstoreH_refundCounter_ge` — for the successor world of `afterSstoreH`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- A store never lowers the refund counter when the slot's original value is zero or its current
value is non-zero, under any `SSTORE` regime whose flat `SLOAD` price (if any) is at most the
update price. -/
theorem sstoreRefundH_ge (rules : ForkRules) (new orig cur : B256) (rc : Int)
    (hflat : ∀ g, rules.access = .flat g → g.sload ≤ 5000)
    (h : orig = 0 ∨ cur ≠ 0) : rc ≤ sstoreRefundH rules new orig cur rc := by
  unfold sstoreRefundH
  split
  · unfold sstoreLegacyRefundCounter
    split_ifs <;> omega
  · rename_i g _ hacc
    have hg := hflat g hacc
    unfold sstoreFlatRefundCounter gasStorageSet gasStorageUpdate
    dsimp only
    split_ifs <;> first | omega | (exfalso; tauto)
  · unfold sstoreNewRefundCounter gasStorageSet gasStorageUpdate gasColdSload gasWarmAccess
    dsimp only
    split_ifs <;> first | omega | (exfalso; tauto)

/-- `afterSstoreH` keeps the refund counter from falling under the same condition. -/
theorem afterSstoreH_refundCounter_ge (sevm : Sevm) (base : Devm) (key value : B256)
    (hflat : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 5000)
    (h : base.getOrigStorVal sevm sevm.currentTarget key = 0 ∨
      base.getStorVal sevm.currentTarget key ≠ 0) :
    base.refundCounter ≤ (afterSstoreH sevm base key value).refundCounter := by
  rw [afterSstoreH_refundCounter]
  exact sstoreRefundH_ge _ _ _ _ _ hflat h

end Blanc.Lift
