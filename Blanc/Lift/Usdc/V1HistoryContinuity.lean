import Blanc.Lift.Usdc.V1TransactionContinuity
import Blanc.ExecutionHistoryCommittedCell
import Blanc.ExecutionNoDelHistory

/-! Proxy/V1 control continuity across actual historical blocks and their settled roots. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
  (capabilities : BodyStageCapabilities F)
  (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
  {P I : Adr} {initial : HistoricalMappingKey → Prop}
  (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
  (fresh : V1MappingFreshKeys P history initial)

include capabilities bal initialApart fresh

/-- A block whose actual rules disable system stages carries Proxy/V1 control
through its original transaction sequence, withdrawals, rewards and settlement.
The stage-bit premise is separate from historical inclusion or governance. -/
theorem ConfiguredHistoryTraceIn.v1_block_preserves
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post)
    (rootsIn : ∀ R ∈ block.settledRoots, R ∈ history.settledRoots)
    (disabled : block.bodyTrace.SystemStagesDisabled)
    (proxy : pre.state.getCode P = Proxy.code)
    (impl : pre.state.getCode I = ImplV1.code)
    (slot : ((pre.state.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ∀ R ∈ block.settledRoots, ¬ ∃ entry ∈ R.post.logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]) :
    block.NoDelScheduled P ∧
      post.state.getCode P = Proxy.code ∧ post.state.getCode I = ImplV1.code ∧
      (post.state.getStor P).get implSlot = (pre.state.getStor P).get implSlot ∧
      ∀ R ∈ block.settledRoots,
        R.pre.getCode P = Proxy.code ∧ R.pre.getCode I = ImplV1.code ∧
        (R.pre.getStor P).get implSlot = (pre.state.getStor P).get implSlot := by
  have proxyFam : UsdcContextCode Proxy.code := .inl rfl
  have implFam : UsdcContextCode ImplV1.code := .inr (.inl rfl)
  have hsg := capabilities.stateGas_none block.forkIn
  have rootsEq : block.settledRoots = block.bodyTrace.transactions.settledRoots :=
    block.bodyTrace.settledRoots_eq_transactions_of_disabled disabled
  have historyState : block.bodyTrace.historyState = pre.state := by
    rw [block.bodyTrace.history.state_eq_of_disabled disabled.2.1]
    change block.bodyTrace.beaconState = pre.state
    exact block.bodyTrace.beacon.state_eq_of_disabled disabled.1
  have transactions := ConfiguredHistoryTraceIn.v1_transactions_preserve
    history capabilities bal initialApart fresh block.bodyTrace.transactions
    (fun R member => rootsIn R (by rw [rootsEq]; exact member))
    hsg
    (by change block.bodyTrace.historyState.getCode P = Proxy.code; rw [historyState]; exact proxy)
    (by change block.bodyTrace.historyState.getCode I = ImplV1.code; rw [historyState]; exact impl)
    (by change ((block.bodyTrace.historyState.getStor P).get implSlot).toAdr = I
        rw [historyState]; exact slot)
    AdrSet.not_mem_empty AdrSet.not_mem_empty
    (fun R member => noUpgraded R (by rw [rootsEq]; exact member))
  have ready : ∀ R ∈ block.settledRoots,
      R.pre.getCode P = Proxy.code ∧ R.pre.getCode I = ImplV1.code ∧
      (R.pre.getStor P).get implSlot = (pre.state.getStor P).get implSlot := by
    intro R member
    have facts := transactions.2.2.2.2 R (by rw [← rootsEq]; exact member)
    refine ⟨facts.1, facts.2.1, ?_⟩
    have cell := facts.2.2
    change (R.pre.getStor P).get implSlot =
      (block.bodyTrace.historyState.getStor P).get implSlot at cell
    rw [historyState] at cell
    exact cell
  have cell := block.cell_property_of_settledRoots implSlot hsg proxy
    proxyFam.ne_nil proxyFam.not_delegation
    ((block.bodyTrace.transactions.outputNotDeleted_iff_noDelScheduled P).mpr transactions.1)
    (fun value => value = (pre.state.getStor P).get implSlot)
    (by
      intro R member initialCell
      obtain ⟨rootProxy, rootImpl, rootCell⟩ := ready R member
      have rootSlot := (congrArg B256.toAdr rootCell).trans slot
      exact (ConfiguredHistoryTraceIn.settledRoot_proxyV1_implSlot_eq_of_freshKeys
        history capabilities initialApart fresh bal (rootsIn R member)
        rootProxy rootImpl rootSlot (noUpgraded R member)).trans initialCell)
    rfl
  have installedV1 : InstalledCert ImplV1.code :=
    ⟨⟨_, ImplV1.cert_check, ImplV1.cert_callOnly, ImplV1.cert_noSelfdestruct⟩,
      implFam.not_delegation, implFam.ne_nil⟩
  have implPreserved := block.noDel_of_installedCert installedV1 capabilities impl
  exact ⟨transactions.1, cell.2, implPreserved.2, cell.1, ready⟩

/-- The actual configured segment propagates initial Proxy/V1 control from
block to block and derives the entry control of every retained root.
Freshness and root inclusion refer to the same consumed outer history. -/
theorem ConfiguredHistoryTraceIn.v1_history_preserves
    {start finish : BlockChain} (segment : ConfiguredHistoryTraceIn F cfg start finish)
    (rootsIn : ∀ R ∈ segment.settledRoots, R ∈ history.settledRoots)
    (disabled : segment.SystemStagesDisabled)
    (proxy : start.state.getCode P = Proxy.code)
    (impl : start.state.getCode I = ImplV1.code)
    (slot : ((start.state.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ∀ R ∈ segment.settledRoots, ¬ ∃ entry ∈ R.post.logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]) :
    segment.NoDelScheduled P ∧
      finish.state.getCode P = Proxy.code ∧ finish.state.getCode I = ImplV1.code ∧
      (finish.state.getStor P).get implSlot = (start.state.getStor P).get implSlot ∧
      ∀ R ∈ segment.settledRoots,
        R.pre.getCode P = Proxy.code ∧ R.pre.getCode I = ImplV1.code ∧
        (R.pre.getStor P).get implSlot = (start.state.getStor P).get implSlot := by
  induction segment with
  | refl => exact ⟨trivial, proxy, impl, rfl, by intro R member; cases member⟩
  | step prior block ih =>
    simp only [Blanc.ExecutionTrace.ConfiguredHistoryTraceIn.SystemStagesDisabled] at disabled
    have priorResult := ih
      (fun R member => rootsIn R (List.mem_append_left _ member))
      disabled.1 (fun R member => noUpgraded R (List.mem_append_left _ member))
    have blockResult := ConfiguredHistoryTraceIn.v1_block_preserves
      history capabilities bal initialApart fresh block
      (fun R member => rootsIn R (List.mem_append_right _ member))
      disabled.2 priorResult.2.1 priorResult.2.2.1
      ((congrArg B256.toAdr priorResult.2.2.2.1).trans slot)
      (fun R member => noUpgraded R (List.mem_append_right _ member))
    refine ⟨⟨priorResult.1, blockResult.1⟩, blockResult.2.1, blockResult.2.2.1,
      blockResult.2.2.2.1.trans priorResult.2.2.2.1, ?_⟩
    intro R member
    rcases List.mem_append.mp member with earlier | later
    · exact priorResult.2.2.2.2 R earlier
    · obtain ⟨codeP, codeI, cell⟩ := blockResult.2.2.2.2 R later
      exact ⟨codeP, codeI, cell.trans priorResult.2.2.2.1⟩

end Blanc.Lift.Usdc
