import Blanc.Composition.RequestPhaseAmsterdam

/-!
# The request phase's access-list builder, under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

`request_phase` leaves the fold's final builder existential. This sibling states its value: the builder as given, with the
four calls incorporated at the same index, in rule order. `SysCall.bal` says what the deposit and exit steps do to their own
accounts' slots.
-/

namespace Blanc.Composition.RequestPhaseAmsterdam

open Jaune
open Blanc.Lift
open Blanc.Lift.RequestSystem
open Blanc.ExecutionTrace (optionalRequestEntry append_optionalRequestEntry)

/-- **The value of the builder a request phase leaves.** Four checked calls, each at the state the last left: the fold's
builder is the incorporation of each, at index `idx`, in rule order, each reading its contract's account. -/
theorem request_phase_bal {benv : Benv} {σ1 σ2 σ3 σ4 : State} {out1 out2 out3 out4 : MsgCallOutput}
    (hfork : benv.stat.fork = .amsterdam) (idx : Nat) (acc : List Bytes) (bal : BalBuilder)
    (c1 : processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] = .ok (σ1, out1))
    (c2 : processCheckedSystemTransaction (benv.withState σ1) consolidationRequestPredeployAddress [] =
      .ok (σ2, out2))
    (c3 : processCheckedSystemTransaction (benv.withState σ2) BuilderRequest.Deposit.Creation.address [] =
      .ok (σ3, out3))
    (c4 : processCheckedSystemTransaction (benv.withState σ3) BuilderRequest.Exit.Creation.address [] =
      .ok (σ4, out4)) :
    let bal1 := bal.incorporate idx benv.state σ1 (withdrawalRequestPredeployAddress :: out1.accountReads.toList)
      out1.storageReads.toList out1.storageWrites.toList
    let bal2 := bal1.incorporate idx σ1 σ2 (consolidationRequestPredeployAddress :: out2.accountReads.toList)
      out2.storageReads.toList out2.storageWrites.toList
    let bal3 := bal2.incorporate idx σ2 σ3 (BuilderRequest.Deposit.Creation.address :: out3.accountReads.toList)
      out3.storageReads.toList out3.storageWrites.toList
    let bal4 := bal3.incorporate idx σ3 σ4 (BuilderRequest.Exit.Creation.address :: out4.accountReads.toList)
      out4.storageReads.toList out4.storageWrites.toList
    runRequestContracts idx amsterdamRules.requests benv acc bal =
      .ok (σ4, acc ++ optionalRequestEntry 1 out1.returnData ++
        optionalRequestEntry 2 out2.returnData ++ optionalRequestEntry 3 out3.returnData ++
        optionalRequestEntry 4 out4.returnData, bal4) := by
  intro bal1 bal2 bal3 bal4
  have hb0 : ∃ r, benv.stat.rules.bal = some r := by
    rw [amsterdam_rules (s := benv.stat) hfork]
    exact ⟨_, rfl⟩
  have w : ∀ a b, (benv.withState a).withState b = benv.withState b := fun _ _ => rfl
  obtain ⟨r0, hr0⟩ := hb0
  have hr : ∀ σ : State, (benv.withState σ).stat.rules.bal = some r0 := fun _ => hr0
  rw [requests_eq, RequestSystem.runRequestContracts_step c1, RequestSystem.runRequestContracts_step c2, w,
    RequestSystem.runRequestContracts_step c3, w, RequestSystem.runRequestContracts_step c4, w, runRequestContracts]
  simp only [hr0, hr, append_optionalRequestEntry]
  rfl

end Blanc.Composition.RequestPhaseAmsterdam
