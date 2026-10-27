import Blanc.Lift.Usdc.V1RetainedAllowanceZero
import Blanc.Lift.Usdc.V1ReceiptContinuity

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Carry a constructor-seeded tracked allowance from an original after-cut to
an original later before-cut. Actual receipt-log absence derives root-entry
control and deletion exclusion; actual retained stores derive zero preservation.
Approve evidence is caller exclusion or exact zero-valued tracked Approval logs
in these same original receipts. This internal alternative adopts no observation;
its historical evidence and key-separation producers remain explicit.
The selected final transaction is outside this interval and still needs its
own deployment/settlement proof. -/
theorem ConfiguredHistoryTraceIn.v1_allowance_zero_between_txSplits_of_v1Class
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {P I pair : Adr} {Tr : Adr → Prop} {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : V1MappingFreshKeys P history initial)
    {origin completed pre post : BlockChain}
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed)
    {i : Nat} (afterCut : first.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    {j : Nat} (beforeCut : last.bodyTrace.transactions.TxSplit j)
    (rootsIn : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, R ∈ history.settledRoots)
    (early : last.block.header.timestamp < mainnetCancunTimestamp)
    (proxy : afterCut.afterBenv.state.getCode P = Proxy.code)
    (impl : afterCut.afterBenv.state.getCode I = ImplV1.code)
    (slot : ((afterCut.afterBenv.state.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ∀ entry ∈
      first.receiptLogsBetween (i + 1) first.bodyTrace.decodedTxs.length ++
        later.receiptLogs ++ last.receiptLogsBetween 0 j,
      ¬ (entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]))
    (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
    (v1Class : V1RawWriteClass P pair Tr history.rawFrames)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    (approveEvidence :
      (∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
          last.rootsBeforeTxSplit beforeCut, ∀ G ∈ Exec.committedFrames R.run,
        G.sevm.currentTarget = P → Sevm.selector G.sevm = 0x095ea7b3 →
        G.sevm.caller ≠ pair) ∨
      (∀ entry ∈ first.receiptLogsBetween (i + 1) first.bodyTrace.decodedTxs.length ++
          later.receiptLogs ++ last.receiptLogsBetween 0 j,
        V1ApprovalZeroFor P pair Tr entry))
    {g : Adr} (tracked : Tr g)
    (zero : (afterCut.afterBenv.state.getStor P).get (allowSlot pair g) = 0) :
    (beforeCut.benv.state.getStor P).get (allowSlot pair g) = 0 := by
  have control := ConfiguredHistoryTraceIn.v1_between_txSplits_preserves_from_receipts
    history initialApart fresh first afterCut later last beforeCut rootsIn early
    proxy impl slot noUpgraded
  have rootLogs := ConfiguredHistoryTraceIn.root_logs_between_txSplits_of_mainnet_receipts
    first afterCut later last beforeCut early
    (fun entry => ¬ (entry.address = P ∧ entry.topics = [Proxy.upgradedTopic])) noUpgraded
  have proxyCode : UsdcContextCode Proxy.code := .inl rfl
  apply (((MidHistoryTraceIn.tail first afterCut).append later).cell_zero_before_txSplit
    last beforeCut (allowSlot pair g) (fun _ selected => selected.stateGas_none)
    proxy proxyCode.ne_nil proxyCode.not_delegation control.1 ?_ zero).1
  intro R member incoming
  obtain ⟨rootProxy, rootImpl, rootWord⟩ := control.2.2.2.2 R member
  have rootSlot : ((R.pre.getStor P).get implSlot).toAdr = I := by
    rw [rootWord]
    exact slot
  have rootNoUpgrade : ¬ ∃ entry ∈ R.post.logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic] := by
    rintro ⟨entry, present, event⟩
    exact rootLogs R member entry present event
  have rootApprove : V1ApproveEvidence P pair Tr R := by
    rcases approveEvidence with noCaller | logs
    · exact .inl (noCaller R member)
    · exact .inr (ConfiguredHistoryTraceIn.root_logs_between_txSplits_of_mainnet_receipts
        first afterCut later last beforeCut early (V1ApprovalZeroFor P pair Tr) logs R member)
  exact ConfiguredHistoryTraceIn.settledRoot_v1_allowance_zero_of_v1Class history
    BodyStageCapabilities.historical initialApart fresh (fun selected => selected.bal_none)
    (rootsIn R member) rootProxy rootImpl rootSlot rootNoUpgrade
    proxyApart initApart rootApprove v1Class tracked incoming

/-- Carry a constructor-seeded tracked allowance from an original after-cut to
an original later before-cut. Actual receipt-log absence derives root-entry
control and deletion exclusion; actual retained stores derive zero preservation.
Approve evidence is caller exclusion or exact zero-valued tracked Approval logs
in these same original receipts. This internal alternative adopts no observation;
its historical evidence and key-separation producers remain explicit.
The selected final transaction is outside this interval and still needs its
own deployment/settlement proof. -/
theorem ConfiguredHistoryTraceIn.v1_allowance_zero_between_txSplits_from_approve_evidence
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {P I pair : Adr} {Tr : Adr → Prop} {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : V1MappingFreshKeys P history initial)
    {origin completed pre post : BlockChain}
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed)
    {i : Nat} (afterCut : first.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    {j : Nat} (beforeCut : last.bodyTrace.transactions.TxSplit j)
    (rootsIn : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, R ∈ history.settledRoots)
    (early : last.block.header.timestamp < mainnetCancunTimestamp)
    (proxy : afterCut.afterBenv.state.getCode P = Proxy.code)
    (impl : afterCut.afterBenv.state.getCode I = ImplV1.code)
    (slot : ((afterCut.afterBenv.state.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ∀ entry ∈
      first.receiptLogsBetween (i + 1) first.bodyTrace.decodedTxs.length ++
        later.receiptLogs ++ last.receiptLogsBetween 0 j,
      ¬ (entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]))
    (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
    (rowSep : UsdcRowSep P pair Tr history.rawFrames)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    (approveEvidence :
      (∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
          last.rootsBeforeTxSplit beforeCut, ∀ G ∈ Exec.committedFrames R.run,
        G.sevm.currentTarget = P → Sevm.selector G.sevm = 0x095ea7b3 →
        G.sevm.caller ≠ pair) ∨
      (∀ entry ∈ first.receiptLogsBetween (i + 1) first.bodyTrace.decodedTxs.length ++
          later.receiptLogs ++ last.receiptLogsBetween 0 j,
        V1ApprovalZeroFor P pair Tr entry))
    {g : Adr} (tracked : Tr g)
    (zero : (afterCut.afterBenv.state.getStor P).get (allowSlot pair g) = 0) :
    (beforeCut.benv.state.getStor P).get (allowSlot pair g) = 0 := by
  exact ConfiguredHistoryTraceIn.v1_allowance_zero_between_txSplits_of_v1Class
    history initialApart fresh first afterCut later last beforeCut rootsIn early
    proxy impl slot noUpgraded proxyApart
    (ConfiguredHistoryTraceIn.v1RawWriteClass_of_rowSep history
      BodyStageCapabilities.historical rowSep)
    initApart approveEvidence tracked zero

/-- Compatibility interface preserving the original caller-exclusion statement. -/
theorem ConfiguredHistoryTraceIn.v1_allowance_zero_between_txSplits_from_receipts
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {P I pair : Adr} {Tr : Adr → Prop} {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : V1MappingFreshKeys P history initial)
    {origin completed pre post : BlockChain}
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed)
    {i : Nat} (afterCut : first.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    {j : Nat} (beforeCut : last.bodyTrace.transactions.TxSplit j)
    (rootsIn : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, R ∈ history.settledRoots)
    (early : last.block.header.timestamp < mainnetCancunTimestamp)
    (proxy : afterCut.afterBenv.state.getCode P = Proxy.code)
    (impl : afterCut.afterBenv.state.getCode I = ImplV1.code)
    (slot : ((afterCut.afterBenv.state.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ∀ entry ∈
      first.receiptLogsBetween (i + 1) first.bodyTrace.decodedTxs.length ++
        later.receiptLogs ++ last.receiptLogsBetween 0 j,
      ¬ (entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]))
    (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
    (rowSep : UsdcRowSep P pair Tr history.rawFrames)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    (noCaller : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
        last.rootsBeforeTxSplit beforeCut, ∀ G ∈ Exec.committedFrames R.run,
      G.sevm.currentTarget = P → Sevm.selector G.sevm = 0x095ea7b3 →
      G.sevm.caller ≠ pair)
    {g : Adr} (tracked : Tr g)
    (zero : (afterCut.afterBenv.state.getStor P).get (allowSlot pair g) = 0) :
    (beforeCut.benv.state.getStor P).get (allowSlot pair g) = 0 :=
  ConfiguredHistoryTraceIn.v1_allowance_zero_between_txSplits_from_approve_evidence
    history initialApart fresh first afterCut later last beforeCut rootsIn early
    proxy impl slot noUpgraded proxyApart rowSep initApart (.inl noCaller) tracked zero

end Blanc.Lift.Usdc
