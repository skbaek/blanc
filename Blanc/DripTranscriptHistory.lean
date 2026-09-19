import Blanc.DripTranscriptExec
import Blanc.DripConcreteRealized

namespace Blanc.Drip

open Jaune

variable {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}

/-- R2, executed flow: every term is a function of the actual history. -/
theorem history_transcript_accounting_exact
    (root : DeploymentRoot cfg base deployed ca) (coalition : Finset Adr)
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg deployed future) :
    coalitionUnits coalition ca future.state * chiN (future.state.getStor ca) +
        (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).joinResidue +
        scale.toNat * (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).paid +
        (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).exitResidue =
      (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).accrual +
        scale.toNat * (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).joined := by
  obtain ⟨steps, realizes, faithful⟩ :=
    dripTraceRealizes_transcript root coalition history
  have tally := Chain.transcriptTally_eq realizes.toRealizedChain
  rw [root.snapshot_eq coalition] at tally
  rw [← faithful, tally]
  exact history_accounting_exact root realizes

/-- The target balance: DRIP-call flows are the transcript's; everything else
is outside credit, the same for every faithful ledger. -/
theorem history_transcript_balance_exact
    (root : DeploymentRoot cfg base deployed ca) {coalition : Finset Adr}
    {steps : List RealizedStep}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg deployed future)
    (realizes : DripTraceRealizes root coalition steps future)
    (faithful : callKinds steps = history.dripCalls coalition ca) :
    (future.state.bal ca).toNat +
        (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).allPaid =
      (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).allJoined + Chain.giftSum steps := by
  have tally := Chain.transcriptTally_eq realizes.toRealizedChain
  rw [root.snapshot_eq coalition] at tally
  rw [← faithful, tally]
  exact history_balance_exact root realizes

/-- R3, executed flow: the coalition's actual cumulative exit receipts never
exceed its actual principal plus the floor of its actual realized accrual. -/
theorem history_transcript_entitlement
    (root : DeploymentRoot cfg base deployed ca) (coalition : Finset Adr)
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg deployed future) :
    (transcriptTally scale.toNat freshNat scale.toNat 0
        (history.dripCalls coalition ca)).paid ≤
      (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).joined +
        (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).accrual / scale.toNat := by
  obtain ⟨steps, realizes, faithful⟩ :=
    dripTraceRealizes_transcript root coalition history
  have tally := Chain.transcriptTally_eq realizes.toRealizedChain
  rw [root.snapshot_eq coalition] at tally
  rw [← faithful, tally]
  exact history_entitlement root realizes

/-- R3 segmentation, compiled and realized: two real histories whose DRIP
calls are exactly equal-total drip schedules end within the certified bound. -/
theorem realized_segment_certified
    {futureL futureR : BlockChain}
    (root : DeploymentRoot cfg base deployed ca) (coalition : Finset Adr)
    (historyL : ExecutionTrace.ConfiguredHistoryTrace cfg deployed futureL)
    (historyR : ExecutionTrace.ConfiguredHistoryTrace cfg deployed futureR)
    {left right : List Nat}
    (callsL : historyL.dripCalls coalition ca = left.map Kind.drip)
    (callsR : historyR.dripCalls coalition ca = right.map Kind.drip)
    (sameElapsed : left.sum = right.sum) :
    natDistance (chiN (futureL.state.getStor ca)) (chiN (futureR.state.getStor ca)) ≤
      max (segmentDriftForward scale.toNat half.toNat rate.toNat scale.toNat left right)
          (segmentDriftForward scale.toNat half.toNat rate.toNat scale.toNat right left) := by
  obtain ⟨stepsL, realizesL, faithfulL⟩ :=
    dripTraceRealizes_transcript root coalition historyL
  obtain ⟨stepsR, realizesR, faithfulR⟩ :=
    dripTraceRealizes_transcript root coalition historyR
  have stateL := Chain.transcriptState_eq realizesL.toRealizedChain
  have stateR := Chain.transcriptState_eq realizesR.toRealizedChain
  rw [root.snapshot_eq coalition, faithfulL, callsL] at stateL
  rw [root.snapshot_eq coalition, faithfulR, callsR] at stateR
  have chiL := congrArg Prod.fst stateL
  have chiR := congrArg Prod.fst stateR
  rw [transcriptState_drips] at chiL
  rw [transcriptState_drips] at chiR
  have chiL' :
      segmentIndex scale.toNat half.toNat rate.toNat scale.toNat left =
        chiN (futureL.state.getStor ca) := by
    simpa [snapshot] using chiL
  have chiR' :
      segmentIndex scale.toNat half.toNat rate.toNat scale.toNat right =
        chiN (futureR.state.getStor ca) := by
    simpa [snapshot] using chiR
  have certified := drip_segment_certified (chi := scale.toNat) sameElapsed
  rw [chiL', chiR'] at certified
  exact certified

/-- Anti-vacuity of the transcript: a history that moved the supply made calls. -/
theorem dripCalls_ne_nil_of_totalUnits
    (root : DeploymentRoot cfg base deployed ca) (coalition : Finset Adr)
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg deployed future)
    (moved : totalN (future.state.getStor ca) ≠ 0) :
    history.dripCalls coalition ca ≠ [] := by
  obtain ⟨steps, realizes, faithful⟩ :=
    dripTraceRealizes_transcript root coalition history
  intro none
  have total := Chain.totalUnits_eq_of_callKinds_nil realizes.toRealizedChain
    (by rw [faithful, none])
  rw [root.snapshot_eq coalition] at total
  apply moved
  simpa [snapshot] using total

noncomputable def concreteHistoryTrace :
    ExecutionTrace.ConfiguredHistoryTrace concreteConfig concreteDeployed concreteExited :=
  .step (.step (.step
    (.refl concreteDeploymentRoot.configValid
      concreteDeploymentRoot.deployed_validContext
      concreteDeploymentRoot.deployed_chainId)
    concreteJoinBlockTrace)
    concreteDripBlockTrace)
    concreteExitBlockTrace

theorem concreteHistory_dripCalls_ne_nil :
    concreteHistoryTrace.dripCalls {concreteCreateSender} concreteCreateTarget ≠ [] := by
  apply dripCalls_ne_nil_of_totalUnits concreteDeploymentRoot
    {concreteCreateSender} concreteHistoryTrace
  unfold totalN
  rw [concreteExited_values.2.2.2]
  decide

end Blanc.Drip
