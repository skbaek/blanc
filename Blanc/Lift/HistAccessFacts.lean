import Blanc.Lift.HistAccessWalk

/-!
# World facts of the historical `SLOAD`/`SSTORE` successors

`afterSloadH_state`: an `SLOAD` under either access schedule leaves the world state unchanged.
`afterSstoreH_getCode`: an `SSTORE` under either access schedule and refund regime changes no
account's code; `afterSstoreH_state` writes exactly its one cell. Nothing here mentions a contract.
-/

namespace Blanc.Lift
open Jaune

/-- An `SLOAD` under the actual access schedule leaves the world state unchanged. -/
theorem afterSloadH_state (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSloadH sevm base key).state = base.state := by
  unfold afterSloadH afterSload
  split
  · split <;> rfl
  · rfl

/-- An `SSTORE` under the actual access schedule and refund regime writes one cell of the world
state and changes nothing else in it. -/
theorem afterSstoreH_state (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstoreH sevm base key value).state =
      base.state.setStorVal sevm.currentTarget key value := by
  unfold afterSstoreH storageAccessH
  split
  · rfl
  · split <;> rfl

/-- The refund-counter update and one storage-cell write touch no account's code. -/
private theorem withRefund_setStorVal_getCode (devm : Devm) (rc : Int) (target : Adr)
    (key value : B256) (address : Adr) :
    ((devm.withRefundCounter rc).setStorVal target key value).getCode address =
      devm.getCode address := by
  show (((devm.withRefundCounter rc).state.setStorVal target key value).get
    address).code = ((devm.state.get address)).code
  by_cases h : target = address
  · subst h
    rw [State.setStorVal_get_self]
    rfl
  · rw [State.setStorVal_get_ne _ h]
    rfl

/-- An `SSTORE` under the actual access schedule and refund regime changes no account's code. -/
theorem afterSstoreH_getCode (sevm : Sevm) (base : Devm) (key value : B256) (address : Adr) :
    (afterSstoreH sevm base key value).getCode address = base.getCode address := by
  unfold afterSstoreH storageAccessH
  split
  · exact withRefund_setStorVal_getCode base _ _ _ _ _
  · split
    · exact withRefund_setStorVal_getCode base _ _ _ _ _
    · exact (withRefund_setStorVal_getCode _ _ _ _ _ _).trans rfl

end Blanc.Lift
