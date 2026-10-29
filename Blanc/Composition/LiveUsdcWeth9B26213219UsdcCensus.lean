import Blanc.Composition.LiveUsdcWeth9B26213219CDObservation
import Blanc.ExecutionHistoryReceiptCensus

/-! Bounded USDC log censuses supply the two intervening-receipt predicates
used by the original C-to-D seed. Fetched-data completeness and correspondence
with the original history remain explicit; this module adopts no observation. -/
namespace Blanc.Composition.LiveUsdcWeth9B26213219.CDObservation

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Usdc
  HistoryAnchorObservationData

/-- The exact Upgraded event predicate consumed by the original V1 history. -/
def UsdcUpgradeExcluded (entry : Log) : Prop :=
  ¬ (entry.address = usdcProxy ∧ entry.topics = [Proxy.upgradedTopic])

/-- The query excludes every spender and value for the Pair's Approval events. -/
def UsdcPairApprovalExcluded (entry : Log) : Prop :=
  ¬ (entry.address = usdcProxy ∧ entry.topics.take 2 =
    [V1ApproveRetainedLog.approvalTopic, UniswapV2Pair.Creation.pairAddress.toB256])

/-- Correspondence for the original intervening history, restricted to the
inclusive observed C/D block range. Boundary receipts are handled separately
by the existing concrete bloom theorems. -/
structure OriginalMiddleCensus {start finish : BlockChain}
    (middle : ConfiguredHistoryTraceIn HistFork mainnetChainConfig start finish) : Prop where
  upgraded : middle.ReceiptCensus C.blockNumber D.blockNumber UsdcUpgradeExcluded
  approval : middle.ReceiptCensus C.blockNumber D.blockNumber UsdcPairApprovalExcluded

/-- The observed original endpoints make the inclusive census cover every
intervening receipt. No per-block range premise is supplied. -/
theorem OriginalC.middle_receipts_of_census
    {cpre cpost dpre dpost : BlockChain}
    {first : ConfiguredBlockTraceIn HistFork mainnetChainConfig cpre cpost}
    {last : ConfiguredBlockTraceIn HistFork mainnetChainConfig dpre dpost}
    (c : OriginalC first) (d : OriginalD last)
    (middle : ConfiguredHistoryTraceIn HistFork mainnetChainConfig cpost dpre)
    (property : Log → Prop)
    (census : middle.ReceiptCensus C.blockNumber D.blockNumber property) :
    ∀ entry ∈ middle.receiptLogs, property entry := by
  obtain ⟨_, _, _, startTip⟩ := first.tip_number_step
  obtain ⟨parent, parentTip, parentNumber, _⟩ := last.tip_number_step
  have startBound : C.blockNumber ≤ first.block.header.number := Nat.le_of_eq c.number.symm
  have endBound : parent.header.number ≤ D.blockNumber := by
    have number := d.number
    omega
  exact middle.receiptLogs_of_census ⟨first.block, startTip, startBound⟩
    parentTip endBound property census

/-- Original census correspondence supplies the existing no-Upgraded input. -/
theorem OriginalMiddleCensus.noUpgraded
    {cpre cpost dpre dpost : BlockChain}
    {first : ConfiguredBlockTraceIn HistFork mainnetChainConfig cpre cpost}
    {last : ConfiguredBlockTraceIn HistFork mainnetChainConfig dpre dpost}
    {middle : ConfiguredHistoryTraceIn HistFork mainnetChainConfig cpost dpre}
    (census : OriginalMiddleCensus middle) (c : OriginalC first) (d : OriginalD last) :
    ∀ entry ∈ middle.receiptLogs,
      ¬ (entry.address = usdcProxy ∧ entry.topics = [Proxy.upgradedTopic]) :=
  c.middle_receipts_of_census d middle UsdcUpgradeExcluded census.upgraded

/-- Absence of all Pair Approval events implies the existing value-aware
predicate for any tracked spender set; zero and unrelated approvals need not
be assumed absent by that downstream predicate itself. -/
theorem OriginalMiddleCensus.approvalZero
    {cpre cpost dpre dpost : BlockChain}
    {first : ConfiguredBlockTraceIn HistFork mainnetChainConfig cpre cpost}
    {last : ConfiguredBlockTraceIn HistFork mainnetChainConfig dpre dpost}
    {middle : ConfiguredHistoryTraceIn HistFork mainnetChainConfig cpost dpre}
    (census : OriginalMiddleCensus middle) (c : OriginalC first) (d : OriginalD last)
    (tracked : Adr → Prop) :
    ∀ entry ∈ middle.receiptLogs,
      V1ApprovalZeroFor usdcProxy UniswapV2Pair.Creation.pairAddress tracked entry := by
  intro entry member spender value _ shape
  have excluded := c.middle_receipts_of_census d middle UsdcPairApprovalExcluded
    census.approval entry member
  subst entry
  exact (excluded ⟨rfl, rfl⟩).elim

end Blanc.Composition.LiveUsdcWeth9B26213219.CDObservation
