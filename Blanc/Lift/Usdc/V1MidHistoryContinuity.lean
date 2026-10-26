import Blanc.Lift.Usdc.V1HistoryContinuity
import Blanc.ExecutionMidHistoryInNoDel

/-! Proxy/V1 control at genuine after-transaction and before-transaction cuts. -/

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

/-- Start immediately after the selected transaction, even if that transaction
created the proxy. Only the actual suffix and post-transaction request stage
are consumed; no pre-creation code premise or block-end substitute is used. -/
theorem ConfiguredHistoryTraceIn.v1_tail_preserves
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i)
    (rootsIn : ∀ R ∈ (MidHistoryTraceIn.tail block cut).settledRoots,
      R ∈ history.settledRoots)
    (requestsDisabled : block.fork.ruleSet.header.requestsHash = false)
    (proxy : cut.afterBenv.state.getCode P = Proxy.code)
    (impl : cut.afterBenv.state.getCode I = ImplV1.code)
    (slot : ((cut.afterBenv.state.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ∀ R ∈ (MidHistoryTraceIn.tail block cut).settledRoots,
      ¬ ∃ entry ∈ R.post.logs,
        entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]) :
    (MidHistoryTraceIn.tail block cut).OutputNotDeleted P ∧
      post.state.getCode P = Proxy.code ∧ post.state.getCode I = ImplV1.code ∧
      (post.state.getStor P).get implSlot = (cut.afterBenv.state.getStor P).get implSlot ∧
      ∀ R ∈ (MidHistoryTraceIn.tail block cut).settledRoots,
        R.pre.getCode P = Proxy.code ∧ R.pre.getCode I = ImplV1.code ∧
        (R.pre.getStor P).get implSlot = (cut.afterBenv.state.getStor P).get implSlot := by
  have proxyFam : UsdcContextCode Proxy.code := .inl rfl
  have implFam : UsdcContextCode ImplV1.code := .inr (.inl rfl)
  have requestRoots := block.bodyTrace.requests.settledRoots_eq_nil_of_disabled requestsDisabled
  have rootsEq : (MidHistoryTraceIn.tail block cut).settledRoots = cut.after.settledRoots := by
    simp only [MidHistoryTraceIn.settledRoots, requestRoots, List.append_nil]
  have hsg := capabilities.stateGas_none block.forkIn
  have suffixSg : cut.afterBenv.stat.rules.stateGas = none := by
    rw [block.txSplit_stat cut]
    exact hsg
  have transactions := ConfiguredHistoryTraceIn.v1_transactions_preserve
    history capabilities bal initialApart fresh cut.after
    (fun R member => rootsIn R (by rw [rootsEq]; exact member))
    suffixSg proxy impl slot (block.txSplit_notCreated cut P) (block.txSplit_notCreated cut I)
    (fun R member => noUpgraded R (by rw [rootsEq]; exact member))
  have proxyTail := block.bodyTrace.cell_property_after_transactions_of_settledRoots
    implSlot hsg transactions.2.1 proxyFam.ne_nil proxyFam.not_delegation
    (fun value => value = (cut.afterBenv.state.getStor P).get implSlot)
    (by intro R member; rw [requestRoots] at member; cases member) transactions.2.2.2.1
  have implTail := block.bodyTrace.cell_property_after_transactions_of_settledRoots
    implSlot hsg transactions.2.2.1 implFam.ne_nil implFam.not_delegation
    (fun _ => True) (by intro R member; rw [requestRoots] at member; cases member) trivial
  have postState := congrArg BlockChain.state block.postEq
  refine ⟨(cut.after.outputNotDeleted_iff_noDelScheduled P).mpr transactions.1,
    ?_, ?_, ?_, ?_⟩
  · rw [postState]; exact proxyTail.2
  · rw [postState]; exact implTail.2
  · rw [postState]; exact proxyTail.1
  · intro R member
    exact transactions.2.2.2.2 R (by rw [← rootsEq]; exact member)

/-- Append the actual later configured blocks to the genuine after-cut tail.
The original root lists, deletion outputs and exact initial word are retained. -/
theorem ConfiguredHistoryTraceIn.v1_mid_preserves
    {pre completed finish : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre completed)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed finish)
    (rootsIn : ∀ R ∈ ((MidHistoryTraceIn.tail block cut).append later).settledRoots,
      R ∈ history.settledRoots)
    (requestsDisabled : block.fork.ruleSet.header.requestsHash = false)
    (laterDisabled : later.SystemStagesDisabled)
    (proxy : cut.afterBenv.state.getCode P = Proxy.code)
    (impl : cut.afterBenv.state.getCode I = ImplV1.code)
    (slot : ((cut.afterBenv.state.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ∀ R ∈ ((MidHistoryTraceIn.tail block cut).append later).settledRoots,
      ¬ ∃ entry ∈ R.post.logs,
        entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]) :
    ((MidHistoryTraceIn.tail block cut).append later).OutputNotDeleted P ∧
      finish.state.getCode P = Proxy.code ∧ finish.state.getCode I = ImplV1.code ∧
      (finish.state.getStor P).get implSlot = (cut.afterBenv.state.getStor P).get implSlot ∧
      ∀ R ∈ ((MidHistoryTraceIn.tail block cut).append later).settledRoots,
        R.pre.getCode P = Proxy.code ∧ R.pre.getCode I = ImplV1.code ∧
        (R.pre.getStor P).get implSlot = (cut.afterBenv.state.getStor P).get implSlot := by
  rw [(MidHistoryTraceIn.tail block cut).append_settledRoots later] at rootsIn noUpgraded ⊢
  have tail := ConfiguredHistoryTraceIn.v1_tail_preserves history capabilities bal
    initialApart fresh block cut
    (fun R member => rootsIn R (List.mem_append_left _ member))
    requestsDisabled proxy impl slot
    (fun R member => noUpgraded R (List.mem_append_left _ member))
  have rest := ConfiguredHistoryTraceIn.v1_history_preserves history capabilities bal
    initialApart fresh later (fun R member => rootsIn R (List.mem_append_right _ member))
    laterDisabled tail.2.1 tail.2.2.1 ((congrArg B256.toAdr tail.2.2.2.1).trans slot)
    (fun R member => noUpgraded R (List.mem_append_right _ member))
  refine ⟨((MidHistoryTraceIn.tail block cut).outputNotDeleted_append later P).mpr
    ⟨tail.1, (later.noDelScheduled_iff_outputNotDeleted P).mp rest.1⟩,
    rest.2.1, rest.2.2.1, rest.2.2.2.1.trans tail.2.2.2.1, ?_⟩
  intro R member
  rcases List.mem_append.mp member with earlier | later
  · exact tail.2.2.2.2 R earlier
  · obtain ⟨codeP, codeI, cell⟩ := rest.2.2.2.2 R later
    exact ⟨codeP, codeI, cell.trans tail.2.2.2.1⟩

/-- Stop at the original selected transaction's input. Only the opening stages
and actual before-trace are consumed; the head and remainder are unrestricted. -/
theorem ConfiguredHistoryTraceIn.v1_before_txSplit_preserves
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i)
    (rootsIn : ∀ R ∈ block.rootsBeforeTxSplit cut, R ∈ history.settledRoots)
    (openingDisabled : block.fork.ruleSet.sys.beaconRoots = false ∧
      block.fork.ruleSet.sys.historyStorage = false)
    (proxy : pre.state.getCode P = Proxy.code)
    (impl : pre.state.getCode I = ImplV1.code)
    (slot : ((pre.state.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ∀ R ∈ block.rootsBeforeTxSplit cut,
      ¬ ∃ entry ∈ R.post.logs,
        entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]) :
    cut.before.OutputNotDeleted P ∧
      cut.benv.state.getCode P = Proxy.code ∧ cut.benv.state.getCode I = ImplV1.code ∧
      (cut.benv.state.getStor P).get implSlot = (pre.state.getStor P).get implSlot ∧
      ∀ R ∈ block.rootsBeforeTxSplit cut,
        R.pre.getCode P = Proxy.code ∧ R.pre.getCode I = ImplV1.code ∧
        (R.pre.getStor P).get implSlot = (pre.state.getStor P).get implSlot := by
  have rootsEq : block.rootsBeforeTxSplit cut = cut.before.settledRoots := by
    simp only [ConfiguredBlockTraceIn.rootsBeforeTxSplit,
      block.bodyTrace.beacon.settledRoots_eq_nil_of_disabled openingDisabled.1,
      block.bodyTrace.history.settledRoots_eq_nil_of_disabled openingDisabled.2,
      List.nil_append]
  have historyState : block.bodyTrace.historyState = pre.state := by
    rw [block.bodyTrace.history.state_eq_of_disabled openingDisabled.2]
    change block.bodyTrace.beaconState = pre.state
    exact block.bodyTrace.beacon.state_eq_of_disabled openingDisabled.1
  have before := ConfiguredHistoryTraceIn.v1_transactions_preserve history capabilities bal
    initialApart fresh cut.before
    (fun R member => rootsIn R (by rw [rootsEq]; exact member))
    (capabilities.stateGas_none block.forkIn)
    (by change block.bodyTrace.historyState.getCode P = Proxy.code; rw [historyState]; exact proxy)
    (by change block.bodyTrace.historyState.getCode I = ImplV1.code; rw [historyState]; exact impl)
    (by change ((block.bodyTrace.historyState.getStor P).get implSlot).toAdr = I
        rw [historyState]; exact slot)
    AdrSet.not_mem_empty AdrSet.not_mem_empty
    (fun R member => noUpgraded R (by rw [rootsEq]; exact member))
  have word := before.2.2.2.1
  change (cut.benv.state.getStor P).get implSlot =
    (block.bodyTrace.historyState.getStor P).get implSlot at word
  have openingWord := congrArg (fun state : State => (state.getStor P).get implSlot) historyState
  refine ⟨(cut.before.outputNotDeleted_iff_noDelScheduled P).mpr before.1,
    before.2.1, before.2.2.1, word.trans openingWord, ?_⟩
  intro R member
  have root := before.2.2.2.2 R (by rw [← rootsEq]; exact member)
  refine ⟨root.1, root.2.1, ?_⟩
  have cell := root.2.2
  change (R.pre.getStor P).get implSlot =
    (block.bodyTrace.historyState.getStor P).get implSlot at cell
  rw [historyState] at cell
  exact cell

/-- Control from an original settled-after cut to a later original before-cut.
All root conditions are restricted to the actual intervening interval. The
selected final transaction and every later root are outside those conditions. -/
theorem ConfiguredHistoryTraceIn.v1_between_txSplits_preserves
    {origin completed pre post : BlockChain}
    (first : ConfiguredBlockTraceIn F cfg origin completed)
    {i : Nat} (afterCut : first.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed pre)
    (last : ConfiguredBlockTraceIn F cfg pre post)
    {j : Nat} (beforeCut : last.bodyTrace.transactions.TxSplit j)
    (rootsIn : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, R ∈ history.settledRoots)
    (requestsDisabled : first.fork.ruleSet.header.requestsHash = false)
    (laterDisabled : later.SystemStagesDisabled)
    (openingDisabled : last.fork.ruleSet.sys.beaconRoots = false ∧
      last.fork.ruleSet.sys.historyStorage = false)
    (proxy : afterCut.afterBenv.state.getCode P = Proxy.code)
    (impl : afterCut.afterBenv.state.getCode I = ImplV1.code)
    (slot : ((afterCut.afterBenv.state.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, ¬ ∃ entry ∈ R.post.logs,
        entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]) :
    (((MidHistoryTraceIn.tail first afterCut).append later).OutputNotDeleted P ∧
      beforeCut.before.OutputNotDeleted P) ∧
      beforeCut.benv.state.getCode P = Proxy.code ∧
      beforeCut.benv.state.getCode I = ImplV1.code ∧
      (beforeCut.benv.state.getStor P).get implSlot =
        (afterCut.afterBenv.state.getStor P).get implSlot ∧
      ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
          last.rootsBeforeTxSplit beforeCut,
        R.pre.getCode P = Proxy.code ∧ R.pre.getCode I = ImplV1.code ∧
        (R.pre.getStor P).get implSlot = (afterCut.afterBenv.state.getStor P).get implSlot := by
  have mid := ConfiguredHistoryTraceIn.v1_mid_preserves history capabilities bal
    initialApart fresh first afterCut later
    (fun R member => rootsIn R (List.mem_append_left _ member))
    requestsDisabled laterDisabled proxy impl slot
    (fun R member => noUpgraded R (List.mem_append_left _ member))
  have before := ConfiguredHistoryTraceIn.v1_before_txSplit_preserves
    history capabilities bal initialApart fresh last beforeCut
    (fun R member => rootsIn R (List.mem_append_right _ member)) openingDisabled
    mid.2.1 mid.2.2.1 ((congrArg B256.toAdr mid.2.2.2.1).trans slot)
    (fun R member => noUpgraded R (List.mem_append_right _ member))
  refine ⟨⟨mid.1, before.1⟩, before.2.1, before.2.2.1,
    before.2.2.2.1.trans mid.2.2.2.1, ?_⟩
  intro R member
  rcases List.mem_append.mp member with earlier | later
  · exact mid.2.2.2.2 R earlier
  · obtain ⟨codeP, codeI, cell⟩ := before.2.2.2.2 R later
    exact ⟨codeP, codeI, cell.trans mid.2.2.2.1⟩

end Blanc.Lift.Usdc
