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
`G + depositGasOf … sevm base` gas (the body's `SSTORE`s priced from the entry machine's
original reads `base.getOrigStorVal`, as Jaune charges them; Option A, decision
blanc-repin-os-optionA-delegation-20261012), ends in the model's accumulator, and extends
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
    (hsentryLive : gCallStipend < G + 52 +
      bodyLiveCostOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base))) sevm base)
    (hsentryCount : gCallStipend < G + 4 +
      bodyInsertGasOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base))) sevm base +
      countStoreCostOf (base.getOrigStorVal sevm sevm.currentTarget solCountSlot)
        (bodyCount sevm base))
    (hbound : G + 1 + bodyGasOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base)))
      (base.getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm base < 2 ^ 256) :
    ∃ post, Nonempty (Exec 0 sevm (St base [] Mem.empty
        (G + depositGasOf (base.getOrigStorVal sevm sevm.currentTarget
          (solBranchSlot (bodyDepth sevm base)))
          (base.getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm base)) (.ok post)) ∧
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

/-! ## The pre-re-pin header, refuted (evidence)

As for `deposit_exec_solInv` (`not_oldDepositExecSolInv_of_gap`, `depositGas_created_gap` in
`DepositExec.lean`): wherever the static snapshot budget `depositGas` differs from the machine
budget, the old residual `G` is impossible.  Evidence only. -/

/-- The pre-re-pin header of `configuredHistory_deposit_live`, verbatim (binders turned into a
proposition). -/
def OldConfiguredHistoryDepositLive : Prop :=
  ∀ {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (_admitted : trace.FrameAdmitted ca beaconEntry)
    (_installed : checkpoint.state.getCode ca = code)
    (_invariant : SolInv (checkpoint.state.getStor ca) initialHistory)
    (sevm : Sevm) (base : Devm) (G : Nat)
    (s' : BeaconDeposit.Acc) (ev : BeaconDeposit.DepositEvent)
    (_target : sevm.currentTarget = ca)
    (_state : base.state = future.state)
    (_hcode : sevm.code = code)
    (_hdataLength : 4 ≤ sevm.data.length) (_hcd : sevm.data.length < 2 ^ 256)
    (_hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (_hdec : DepositDecodable sevm)
    (_hOk : BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor base sevm.currentTarget))
      (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm) sevm.value.toNat =
        .ok (s', ev))
    (_hsha : ShaReady sevm base) (_hdepth : sevm.depth ≠ 0) (_hstatic : sevm.isStatic = false)
    (_hsentryLive : gCallStipend < G + 52 + bodyLiveCost sevm base)
    (_hsentryCount : gCallStipend < G + 4 + bodyInsertGas sevm base +
      countStoreCost sevm (bodyCount sevm base))
    (_hbound : G + 1 + bodyGas sevm base < 2 ^ 256),
    ∃ post, Nonempty (Exec 0 sevm (St base [] Mem.empty (G + depositGas sevm base)) (.ok post)) ∧
      post.gasLeft = G ∧
      solAcc (Devm.getStor post sevm.currentTarget) = s' ∧
      SolInv (Devm.getStor post sevm.currentTarget)
        (initialHistory ++ committedNodes ca trace ++ [BeaconDeposit.depositDataNode Bytes.sha256
          (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2)
          (BeaconDeposit.le64 (sevm.value.toNat / BeaconDeposit.oneGwei))]) ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor base a) ∧
      post.logs = base.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev]

/-- **The pre-re-pin header is false at any reachable frame where the budgets differ.** -/
theorem not_oldConfiguredHistoryDepositLive_of_gap {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca beaconEntry)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory)
    {sevm : Sevm} {base : Devm} {G d : Nat}
    {s' : BeaconDeposit.Acc} {ev : BeaconDeposit.DepositEvent}
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
    (hbound : G + 1 + bodyGas sevm base < 2 ^ 256)
    (hsentryLive' : gCallStipend < (G + d) + 52 +
      bodyLiveCostOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base))) sevm base)
    (hsentryCount' : gCallStipend < (G + d) + 4 +
      bodyInsertGasOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base))) sevm base +
      countStoreCostOf (base.getOrigStorVal sevm sevm.currentTarget solCountSlot)
        (bodyCount sevm base))
    (hgap : depositGas sevm base =
      depositGasOf (base.getOrigStorVal sevm sevm.currentTarget
          (solBranchSlot (bodyDepth sevm base)))
        (base.getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm base + d)
    (hd : d ≠ 0) : ¬ OldConfiguredHistoryDepositLive := by
  intro H
  obtain ⟨post, ⟨hex⟩, hg, -⟩ := H trace admitted installed invariant sevm base G s' ev target
    state hcode hdataLength hcd hsel hdec hOk hsha hdepth hstatic hsentryLive hsentryCount hbound
  have hbound' : (G + d) + 1 + bodyGasOf (base.getOrigStorVal sevm sevm.currentTarget
        (solBranchSlot (bodyDepth sevm base)))
      (base.getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm base < 2 ^ 256 := by
    unfold depositGas depositGasOf at hgap
    omega
  obtain ⟨post', ⟨hex'⟩, hg', -⟩ := configuredHistory_deposit_live trace admitted installed
    invariant sevm base (G + d) s' ev target state hcode hdataLength hcd hsel hdec hOk hsha hdepth
    hstatic hsentryLive' hsentryCount' hbound'
  rw [hgap, show ∀ x, G + (x + d) = G + d + x from fun x => by omega] at hex
  have he := Blanc.Exec.result_unique hex hex'
  cases he
  omega

end Blanc.Lift.BeaconDeposit
