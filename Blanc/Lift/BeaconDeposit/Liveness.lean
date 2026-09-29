import Blanc.Lift.BeaconDeposit.CommittedHistory
import Blanc.Lift.BeaconDeposit.DepositExec

/-!
# Liveness at every reachable state (beacon deposit)

`configuredHistory_solInv` (`CommittedHistory.lean`) says the future storage of a
configured history satisfies `SolInv` for the initial history extended by the
history's committed nodes. `deposit_exec_solInv` (`DepositExec.lean`) says a
model-accepted deposit executes with exact gas and extends the abstraction by
the model's node. This module composes them: at any frame whose pre-state is
the future state of a configured history, a model-accepted deposit executes
with exact gas and appends exactly the new node.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- **Liveness at every reachable state.** After any configured history, a deposit
the model accepts at the future storage executes with exactly
`G + depositGas sevm base` gas, ends in the model's accumulator, and extends
the abstraction by exactly the new node. -/
theorem configuredHistory_deposit_live {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca beaconEntry)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory)
    (sevm : Sevm) (base : Devm) (G : Nat)
    (s' : BeaconDeposit.Acc) (ev : BeaconDeposit.DepositEvent)
    (target : sevm.currentTarget = ca)
    (state : base.state = future.state)
    (hcode : sevm.code = code)
    (hdataLength : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (hdec : DepositDecodable sevm)
    (hOk : BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor base sevm.currentTarget))
      (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm) sevm.value.toNat =
        .ok (s', ev))
    (hsha : ShaReady sevm base) (hdepth : sevm.depth ≠ 0) (hstatic : sevm.isStatic = false)
    (hsentryLive : gCallStipend < G + 52 + bodyLiveCost sevm base)
    (hsentryCount : gCallStipend < G + 4 + bodyInsertGas sevm base +
      countStoreCost sevm (bodyCount sevm base))
    (hbound : G + 1 + bodyGas sevm base < 2 ^ 256) :
    ∃ post, Nonempty (Exec 0 sevm (St base [] Mem.empty (G + depositGas sevm base)) (.ok post)) ∧
      post.gasLeft = G ∧
      solAcc (Devm.getStor post sevm.currentTarget) = s' ∧
      SolInv (Devm.getStor post sevm.currentTarget)
        (initialHistory ++ committedNodes ca trace ++ [BeaconDeposit.depositDataNode Bytes.sha256
          (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2)
          (BeaconDeposit.le64 (sevm.value.toNat / BeaconDeposit.oneGwei))]) ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor base a) ∧
      post.logs = base.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev] := by
  have hfuture : SolInv (future.state.getStor ca) (initialHistory ++ committedNodes ca trace) :=
    configuredHistory_solInv trace admitted installed invariant
  have hbase : SolInv (Devm.getStor base sevm.currentTarget)
      (initialHistory ++ committedNodes ca trace) := by
    rw [target]
    have e : Devm.getStor base ca = future.state.getStor ca :=
      congrArg (fun world : State => world.getStor ca) state
    rw [e]
    exact hfuture
  obtain ⟨post, hex, hg, hacc, hinv, hother, hlogs⟩ :=
    deposit_exec_solInv sevm base G _ s' ev hcode hdataLength hcd hsel hdec hbase hOk
      hsha hdepth hstatic hsentryLive hsentryCount hbound
  refine ⟨post, hex, hg, hacc, ?_, hother, hlogs⟩
  simpa only [List.append_assoc] using hinv

end Blanc.Lift.BeaconDeposit
