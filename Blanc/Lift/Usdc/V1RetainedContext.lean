import Blanc.Lift.Usdc.V1WriteApart
import Blanc.Lift.Usdc.ProxyRetainedNoDel
import Blanc.ExecutionNoninterference

/-! Retained Proxy/V1 context and settlement from actual mapping-key freshness. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
  (capabilities : BodyStageCapabilities F)
  {P : Adr} {initial : HistoricalMappingKey → Prop}
  (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
  (fresh : V1MappingFreshKeys P history initial)

include capabilities initialApart fresh

/-- The complete actual V1 producer supplies the retained-root separation
premise from same-history raw membership, without a separate write oracle. -/
theorem ConfiguredHistoryTraceIn.settledRoot_v1_write_ne_implSlot
    {R : Exec.Frame} (member : R ∈ history.settledRoots) :
    ∀ N ∈ Exec.retainedNodes R.run, N.sevm.currentTarget = P →
      N.sevm.code = ImplV1.code → ∀ write : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? N = some write → write.key ≠ implSlot := by
  intro N retained target code write found
  have rawRoot := history.mem_rawFrames_of_mem_settledRoots R member
  have rawNode := history.rawNodes_of_mem_rawFrames _ rawRoot N
    ((Exec.retainedNodes_sublist_rawNodes R.run).subset retained)
  exact ConfiguredHistoryTraceIn.v1_write_ne_implSlot history capabilities
    initialApart fresh rawNode target code found

/-- Every retained node in the selected root has the coupled Proxy/V1 context,
using the seven actual key lists rather than an independent V1 write premise. -/
theorem ConfiguredHistoryTraceIn.settledRoot_proxyV1_context_of_freshKeys
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {I : Adr} {R : Exec.Frame} (member : R ∈ history.settledRoots)
    (proxy : R.pre.getCode P = Proxy.code) (impl : R.pre.getCode I = ImplV1.code)
    (slot : ((R.pre.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ¬ ∃ entry ∈ R.post.logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]) :
    ∀ N ∈ Exec.retainedNodes R.run,
      (N.devm.getStor P).get implSlot = (R.pre.getStor P).get implSlot ∧
      (N.sevm.currentTarget = P → N.sevm.code = Proxy.code ∨ N.sevm.code = ImplV1.code) ∧
      ∀ write : Exec.StorageWrite, Exec.Deriv.successfulSstore? N = some write →
        write.owner = P → write.key ≠ implSlot := by
  exact ConfiguredHistoryTraceIn.settledRoot_retained_proxyV1_context history capabilities
    bal member proxy impl slot noUpgraded
    (ConfiguredHistoryTraceIn.settledRoot_v1_write_ne_implSlot history capabilities
      initialApart fresh member)

/-- Retained write exclusion preserves the actual implementation word at settlement.
This cell law does not require an incoming deletion-set assumption. -/
theorem ConfiguredHistoryTraceIn.settledRoot_proxyV1_implSlot_eq_of_freshKeys
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {I : Adr} {R : Exec.Frame} (member : R ∈ history.settledRoots)
    (proxy : R.pre.getCode P = Proxy.code) (impl : R.pre.getCode I = ImplV1.code)
    (slot : ((R.pre.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ¬ ∃ entry ∈ R.post.logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]) :
    (R.post.getStor P).get implSlot = (R.pre.getStor P).get implSlot := by
  have classified := ConfiguredHistoryTraceIn.settledRoot_proxyV1_context_of_freshKeys
    history capabilities initialApart fresh bal member proxy impl slot noUpgraded
  have noWrite : Exec.NoRetainedWriteTo R.run P implSlot := by
    intro write retained matching
    obtain ⟨N, nodeMember, found⟩ :=
      (List.mem_filterMap.mp retained)
    have matched := Exec.StorageWrite.matches_eq_true.mp matching
    exact (classified N nodeMember).2.2 write found matched.1 matched.2
  have rawRoot := history.mem_rawFrames_of_mem_settledRoots R member
  have rootFacts := history.rawFrame_entryFacts capabilities _ rawRoot
  have nonempty : (R.pre.getCode P).toList ≠ [] := by
    rw [proxy]
    exact (show UsdcContextCode Proxy.code from .inl rfl).ne_nil
  have cell := Exec.committedCell_eq_of_noRetainedWriteTo_noStateGas R.run R.committed
    rootFacts.2.2.1 P implSlot nonempty noWrite
  exact cell

/-- The same selected root preserves both deletion exclusion and its actual
implementation word. Entry code/slot and absence of a retained upgrade log
remain explicit; no assumption is made about discarded child effects. -/
theorem ConfiguredHistoryTraceIn.settledRoot_proxyV1_preserves_of_freshKeys
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {I : Adr} {R : Exec.Frame} (member : R ∈ history.settledRoots)
    (proxy : R.pre.getCode P = Proxy.code) (impl : R.pre.getCode I = ImplV1.code)
    (slot : ((R.pre.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ¬ ∃ entry ∈ R.post.logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic])
    (initialNoDel : Devm.NoDel P R.pre) :
    Devm.NoDel P R.post ∧
      (R.post.getStor P).get implSlot = (R.pre.getStor P).get implSlot := by
  have v1Apart := ConfiguredHistoryTraceIn.settledRoot_v1_write_ne_implSlot
    history capabilities initialApart fresh member
  exact ⟨ConfiguredHistoryTraceIn.settledRoot_proxyV1_noDel
    history capabilities bal member proxy impl slot noUpgraded v1Apart initialNoDel,
    ConfiguredHistoryTraceIn.settledRoot_proxyV1_implSlot_eq_of_freshKeys
      history capabilities initialApart fresh bal member proxy impl slot noUpgraded⟩

end Blanc.Lift.Usdc
