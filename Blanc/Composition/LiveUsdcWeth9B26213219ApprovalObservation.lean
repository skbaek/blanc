import Blanc.Composition.LiveUsdcWeth9B26213219ObservedHistory
import Blanc.ExecutionHistoryReceiptCensus

/-! Correspondence for the completed inclusive WETH Approval census.
The observation concerns original receipts in blocks 4719568 through 10008355.
Provider completeness and binding to this original history remain explicit and
unadopted. Accepted chronology and interval inclusion derive the strict receipt
absence needed by the checkpoint; no further collection is required. -/
namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift
  Blanc.Composition.UniswapV2PairUsdcWeth9

/-- The census filters the log address and first two indexed topics. It puts
no restriction on the spender or data, including zero-valued approvals. -/
def PairApprovalExcluded (entry : Log) : Prop :=
  ¬ (entry.address = weth ∧ entry.topics.take 2 = [Weth9.approvalTopic, pair.toB256])

/-- Empty-query correspondence for the original two boundary blocks and
intervening history. Whole boundary blocks were queried and returned no matches.
This record is a fetched-data boundary, not a proof of RPC completeness. -/
structure OriginalApprovalCensus {checkpoint : BlockChain}
    (h : ObservedDeploymentHistory checkpoint) : Prop where
  first : ∀ entry ∈ h.wethBlock.receiptLogsBetween 0 h.wethBlock.bodyTrace.decodedTxs.length,
    PairApprovalExcluded entry
  middle : h.between.ReceiptCensus Weth9.Creation.ObservationData.blockNumber
    Usdc.HistoryAnchorObservationData.D.blockNumber PairApprovalExcluded
  last : ∀ entry ∈ h.pairBlock.receiptLogsBetween 0 h.pairBlock.bodyTrace.decodedTxs.length,
    PairApprovalExcluded entry

/-- The inclusive block census covers the original strict transaction interval.
Actual header validation proves all intermediate block numbers are in range. -/
theorem OriginalApprovalCensus.beforePairReceiptLogs {checkpoint : BlockChain}
    {h : ObservedDeploymentHistory checkpoint} (observed : OriginalApprovalCensus h) :
    ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉
        h.link.beforePairReceiptLogs := by
  obtain ⟨_, _, _, startTip⟩ := h.wethBlock.tip_number_step
  obtain ⟨parent, parentTip, parentNumber, _⟩ := h.pairBlock.tip_number_step
  have startBound : Weth9.Creation.ObservationData.blockNumber ≤
      h.wethBlock.block.header.number := Nat.le_of_eq h.wethObserved.number.symm
  have endBound : parent.header.number ≤ Usdc.HistoryAnchorObservationData.D.blockNumber := by
    have number := h.pairObserved.number
    omega
  have middle := h.between.receiptLogs_of_census
    ⟨h.wethBlock.block, startTip, startBound⟩ parentTip endBound
    PairApprovalExcluded observed.middle
  have allLogs : ∀ entry ∈ h.link.beforePairReceiptLogs, PairApprovalExcluded entry := by
    intro entry member
    change entry ∈ h.wethBlock.receiptLogsBetween (85 + 1)
      h.wethBlock.bodyTrace.decodedTxs.length ++ h.between.receiptLogs ++
      h.pairBlock.receiptLogsBetween 0 38 at member
    rcases List.mem_append.mp member with before | last
    · rcases List.mem_append.mp before with first | inside
      · exact observed.first entry (h.wethBlock.receiptLogsBetween_subset_full _ _ first)
      · exact middle entry inside
    · exact observed.last entry (h.pairBlock.receiptLogsBetween_subset_full _ _ last)
  intro spender data member
  exact allLogs _ member ⟨rfl, rfl⟩

/-- Original census correspondence now supplies the checkpoint's receipt
absence premise. Observation adoption and the remaining cryptographic inputs
are not discharged by this conditional theorem. -/
theorem ObservedDeploymentHistory.checkpoint_of_approval_census {checkpoint : BlockChain}
    (h : ObservedDeploymentHistory checkpoint) (anchor : ObservedCheckpoint checkpoint)
    (census : OriginalApprovalCensus h)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots
      h.wethDeployment.keys (.bal pair))
    (excluded : ∀ query ∈ h.wethDeployment.trace.senderQueries, query.recover ≠ .ok pair) :
    JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows)
      h.wethDeployment.keys h.pairDeployment.keys h.pairDeployment.model checkpoint.state := by
  exact h.checkpoint anchor holderFresh excluded census.beforePairReceiptLogs

end Blanc.Composition.LiveUsdcWeth9B26213219
