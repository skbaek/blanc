import Blanc.Lift.BeaconDeposit.HistCommittedExec
import Blanc.ExecutionAccountingHistoryIn
import Blanc.ExecutionAccountingCoreIn
import Blanc.ExecutionHistoryInAppend
import Blanc.ExecutionImmutableCode

/-! Exact ordered settlement-retained Beacon extraction over HistFork.
The admitted core is kept separate from the derived environment headline. -/

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- Nodes of exactly the settlement-retained frames of the supplied historical trace. -/
def committedNodesIn {cfg : ChainConfig} {checkpoint future : BlockChain}
    (ca : Adr) (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future) : List B256 :=
  trace.settledFrames.flatMap (committedFrameNodes ca)

private theorem target_replayIn {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (hcode : sevm.code = code) (target : sevm.currentTarget = ca)
    (fork : HistFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted ca beaconFrameEntryRules run)
    (nodes : (Exec.committedFrames run).flatMap (committedFrameNodes ca) =
      frameAccepted sevm) :
    (sevm.isStatic = true →
      (Exec.committedFrames run).flatMap (committedFrameNodes ca) = []) ∧
    (sum pre.state.bal < 2 ^ 256 → ∃ steps,
      (depositCarrier ca).Replay ((depositCarrier ca).frameEntry sevm pre.state) steps
        ((depositCarrier ca).ofState (Execution.committedPost (.ok post) committed).state) ∧
      (depositObservation ca).obs steps =
        (Exec.committedFrames run).flatMap (committedFrameNodes ca)) := by
  obtain ⟨⟨stack, memory⟩, calldata, nodeleg, warm⟩ := admitted.root target
  refine ⟨?_, ?_⟩
  · intro static
    rw [nodes]
    exact frameAccepted_eq_nil_of_staticH hcode fork.stateGas_none fork.bal_none
      calldata stack memory static run
  · intro _
    refine ⟨frameAccepted sevm, ?_, nodes.symm⟩
    change DepositReplay (Devm.getStor pre ca) (frameAccepted sevm) (Devm.getStor post ca)
    intro history invariant
    have sha : ShaReadyRules sevm pre :=
      ⟨nodeleg, warm, isPrecomp_two_hist fork, fork.stateGas_none, fork.bal_none⟩
    rw [← target] at invariant ⊢
    exact frame_solInvH_of_rules hcode fork.stateGas_none fork.bal_none calldata stack memory sha invariant run

private theorem beacon_coreIn (ca : Adr) :
    Exec.Fa (Exec.WknSem ca beaconSem
      (fun pc s d e _ => Blanc.Exec.CoreAccountingIn HistFork ca beaconSem beaconFrameEntryRules
        (depositCarrier ca) (depositObservation ca) pc s d e)) := by
  apply Blanc.Exec.coreAccountingIn HistFork ca beaconSem beaconFrameEntryRules
    (depositCarrier ca) (depositObservation ca) DepositReplay.append (fun _ _ => ())
  · intro sevm state foreign
    rfl
  · intro frame foreign
    change committedFrameNodes ca frame = []
    simp only [committedFrameNodes, ite_eq_right foreign]
  · exact fun hf => hf.stateGas_none
  · intro sevm pre post hcode target deeper run committed fork installed admitted
    apply target_replayIn run committed hcode target fork admitted
    apply target_committedFrameNodesH_of_entry run committed hcode target installed fork admitted
    intro pc s d out child childCommitted childFork depth childAt childAdmitted static
    exact (deeper pc s d out child depth childAt
      child childCommitted childFork childAt childAdmitted).1 static

private def beaconAccountingLadderIn (ca : Adr) :
    AccountingLadderAdmittedIn HistFork beaconSpec ca beaconFrameEntryRules where
  carrier := depositCarrier ca
  append := DepositReplay.append
  tag := fun _ _ => ()
  preserves := beaconSpec_preservesAdmittedIn_of_rules ca
  view := depositObservation ca
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed
      admitted ready _ fork bound
    obtain ⟨installed, entryBound⟩ :=
      Blanc.Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    exact (beacon_coreIn ca pc sevm pre out run installed
      run committed fork installed admitted).2 entryBound

/-- The checked installed runtime supplies historical settlement's no-deletion producer. -/
theorem beaconInstalledCertH : InstalledCert code where
  exists_cert := ⟨cert, cert_check, by decide +kernel, by decide +kernel⟩
  notDelegation := beaconSem.not_delegation rfl
  nonempty := by
    intro empty
    have length := code_toList_length
    rw [empty] at length
    cases length

/-- Transport the original transaction admission to selected-rule readiness on the same roots. -/
theorem transactionListIn_beaconEntry_toRules
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca beaconEntry) :
    trace.FrameAdmitted ca beaconEntryRules := by
  rw [trace.frameAdmitted_iff_rawFrames] at admitted ⊢
  intro root member target
  exact beaconEntry_toRules (admitted root member target)

/-- The actual transaction suffix preserves installed code and the exact extracted history.
This intermediate exposes admission; its entry invariant belongs to the supplied initial state. -/
theorem transactionListIn_code_solInv_admitted_of_rules
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} {initialHistory : List B256}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca beaconEntryRules)
    (installed : benv.state.getCode ca = code)
    (invariant : SolInv (benv.state.getStor ca) initialHistory)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (fork : HistFork benv.stat.fork) (blockIndex : Nat) :
    finalBenv.state.getCode ca = code ∧
      SolInv (finalBenv.state.getStor ca)
        (initialHistory ++ trace.settledFrames.flatMap (committedFrameNodes ca)) := by
  have initial : beaconSpec.StateInv ca benv.state :=
    ⟨by rw [installed]; rfl, trivial, ⟨initialHistory, invariant⟩⟩
  have admittedFull := (trace.freshFrameAdmitted ca).and admitted
  have final := trace.benvInv_admitted_semIn (beaconSpec_preservesAdmittedIn_of_rules ca)
    fork fork.stateGas_none admittedFull sumNof ⟨initial, notCreated⟩ beaconInstalledCertH rfl
  obtain ⟨nodes, replay, observed⟩ := (beaconAccountingLadderIn ca).transactionListIn trace
    admittedFull initial notCreated sumNof fork fork.stateGas_none beaconInstalledCertH rfl blockIndex
  change DepositReplay (benv.state.getStor ca) nodes (finalBenv.state.getStor ca) at replay
  change nodes = trace.settledFrames.flatMap (committedFrameNodes ca) at observed
  rw [observed] at replay
  exact ⟨bytes_eq_of_image final.state.code, replay initialHistory invariant⟩

/-- Compatibility form for the original transaction admission. -/
theorem transactionListIn_code_solInv_admitted
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} {initialHistory : List B256}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca beaconEntry)
    (installed : benv.state.getCode ca = code)
    (invariant : SolInv (benv.state.getStor ca) initialHistory)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (fork : HistFork benv.stat.fork) (blockIndex : Nat) :
    finalBenv.state.getCode ca = code ∧
      SolInv (finalBenv.state.getStor ca)
        (initialHistory ++ trace.settledFrames.flatMap (committedFrameNodes ca)) :=
  transactionListIn_code_solInv_admitted_of_rules trace
    (transactionListIn_beaconEntry_toRules trace admitted) installed invariant
    notCreated sumNof fork blockIndex

/-- The historical admitted core extracts precisely the ordered committed nodes.
Only this intermediate theorem exposes frame admission. -/
theorem configuredHistoryIn_solInv_admitted {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca beaconEntry)
    (rewards : trace.RewardCreditsFunded)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    SolInv (future.state.getStor ca) (initialHistory ++ committedNodesIn ca trace) := by
  have initial : beaconSpec.StateInv ca checkpoint.state :=
    ⟨by rw [installed]; rfl, trivial, ⟨initialHistory, invariant⟩⟩
  have admittedRules : trace.FrameAdmitted ca beaconEntryRules := by
    rw [trace.frameAdmitted_iff_rawFrames] at admitted ⊢
    intro root member target
    exact beaconEntry_toRules (admitted root member target)
  obtain ⟨nodes, replay, observed⟩ :=
    (beaconAccountingLadderIn ca).configuredHistoryIn trace
      ((trace.freshFrameAdmitted ca).and admittedRules) BodyStageCapabilities.historical rewards
      initial beaconInstalledCertH rfl
  change DepositReplay (checkpoint.state.getStor ca) nodes (future.state.getStor ca) at replay
  change nodes = committedNodesIn ca trace at observed
  rw [observed] at replay
  exact replay initialHistory invariant

/-- Ordered extraction composes at an actual historical trace cut. -/
theorem committedNodesIn_append {ca : Adr} {cfg : ChainConfig}
    {checkpoint middle future : BlockChain}
    (left : ConfiguredHistoryTraceIn HistFork cfg checkpoint middle)
    (right : ConfiguredHistoryTraceIn HistFork cfg middle future) :
    committedNodesIn ca (left.append right) = committedNodesIn ca left ++ committedNodesIn ca right := by
  simp only [committedNodesIn, ConfiguredHistoryTraceIn.settledFrames_append, List.flatMap_append]

end Blanc.Lift.BeaconDeposit

