import Blanc.Lift.Usdc.ProxyUpgradeLog
import Blanc.Lift.Usdc.ProxyContextCodes
import Blanc.Lift.CursorOccurrenceNoStateGas
import Blanc.Lift.CommittedFrameLogs
import Blanc.ExecutionRetainedCellAt

/-!
# A retained implementation-slot write entails an Upgraded log

This is a local implication for one committing raw frame of an In-history.
The implementation-slot separation premise identifies the proxy runtime at
the retained write; no history-wide code or storage continuity is assumed.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Every settlement-retained successful implementation-slot write has an
`Upgraded` log in the same committing raw root's endpoint. This includes
same-value writes and writes whose value is later restored. Direct write
attribution needs no code-at-entry or endpoint-change premise. -/
theorem ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} (apartSlot : ImplSlotApart P history.rawNodes)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.exc)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? N = some write)
    (owner : write.owner = P) (key : write.key = implSlot) :
    ∃ entry ∈ (Execution.committedPost R.exn committed).logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic] := by
  obtain ⟨frame, frameMem, chain⟩ :=
    (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.exc N).mp retained
  have frameRaw := history.committedFrame_mem_rawFrames member frameMem
  have nodeMem : N ∈ history.rawNodes :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix N).mpr
      ⟨Blanc.Exec.Frame.rootDeriv frame, frameRaw, chain⟩
  have nodeTarget : N.sevm.currentTarget = P :=
    (successfulSstore?_node_owner found).2.symm.trans owner
  have nodeCode : N.sevm.code = Proxy.code := by
    by_contra other
    exact (apartSlot N nodeMem nodeTarget other write found key).elim
  have sameSevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  change N.sevm = frame.sevm at sameSevm
  have frameCode : frame.sevm.code = Proxy.code := by
    rw [← sameSevm]
    exact nodeCode
  have target : frame.sevm.currentTarget = P := by
    rw [← sameSevm]
    exact nodeTarget
  obtain ⟨pcZero, forkIn, hsg, _, _⟩ :=
    history.rawFrame_entryFacts capabilities (Blanc.Exec.Frame.rootDeriv frame) frameRaw
  have frameBal : frame.sevm.benvStat.rules.bal = none := bal forkIn
  obtain ⟨actual, _, actualEq⟩ := Exec.Deriv.successfulSstore?_sound retained found
  have actualNode : actual.occurrence.node = N :=
    (congrArg Exec.StorageWrite.node actualEq).trans (successfulSstore?_node_owner found).1
  have decoded : Ninst.At N.sevm.code N.pc (.reg .sstore) := by
    rw [← actualNode, ← actual.instruction_eq]
    exact actual.occurrence.decoded
  have actualKey : actual.key = write.key := congrArg Exec.StorageWrite.key actualEq
  have actualValue : actual.value = write.value := congrArg Exec.StorageWrite.value actualEq
  have slot : ∃ v rest, N.devm.stack = implSlot :: v :: rest := by
    have stackEq := actual.popped
    rw [actualNode, actualKey, actualValue, key] at stackEq
    exact ⟨write.value, _, stackEq⟩
  have frameLog : ∃ entry ∈ frame.post.logs,
      entry.address = frame.sevm.currentTarget ∧ entry.topics = [Proxy.upgradedTopic] := by
    rcases frame with ⟨pc, sevm, pre, out, run, frameCommitted⟩
    dsimp only [Blanc.Exec.Frame.rootDeriv] at pcZero chain
    subst pc
    exact Proxy.proxy_implSstore_emitsUpgraded run frameCommitted frameCode hsg frameBal
      chain decoded slot
  obtain ⟨entry, present, address, topics⟩ := frameLog
  obtain ⟨_, _, rootHsg, _, _⟩ := history.rawFrame_entryFacts capabilities R member
  exact ⟨entry, Exec.committedFrame_logs_subset_noStateGas R.exc committed rootHsg
    frame frameMem present, address.trans target, topics⟩

/-- A change of the proxy implementation slot across a committing raw frame
has an `Upgraded` log in that frame's committed endpoint. The account has
nonempty code at entry, and every non-proxy writer is separated from the
implementation slot. No receipt correspondence is asserted. -/
theorem ConfiguredHistoryTraceIn.implSlot_change_emitsUpgraded
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} (apartSlot : ImplSlotApart P history.rawNodes)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true)
    (hcode : (R.devm.getCode P).toList ≠ [])
    (changed : (Devm.getStor R.devm P).get implSlot ≠
      (Devm.getStor (Execution.committedPost R.exn committed) P).get implSlot) :
    ∃ entry ∈ (Execution.committedPost R.exn committed).logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic] := by
  obtain ⟨_, _, hsg, _, _⟩ := history.rawFrame_entryFacts capabilities R member
  obtain ⟨write, retained, owner, key, _, last⟩ :=
    Exec.exists_lastRetainedSstore_of_getStor_ne_noStateGas R.exc committed hsg hcode changed
  have found : Exec.Deriv.successfulSstore? write.occurrence.node =
      some write.storageWrite := by
    obtain ⟨before, after, split, _⟩ := last
    have present : write.storageWrite ∈ Exec.retainedStorageWrites R.exc := by
      rw [split]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    rw [Exec.retainedStorageWrites, List.mem_filterMap] at present
    obtain ⟨node, _, found⟩ := present
    have same := (successfulSstore?_node_owner found).1
    change write.occurrence.node = node at same
    rw [same]
    exact found
  exact ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded history
    capabilities bal apartSlot member committed
    retained found owner key

/-- Absence of a matching `Upgraded` log in this SAME committed root fixes
the implementation slot at every settlement-retained node entry. Temporary
and later-restored writes are excluded by the retained-write log producer;
reverted raw writes and the final receipt-absence bridge remain separate. -/
theorem ConfiguredHistoryTraceIn.retainedNode_implSlot_eq_of_noUpgraded
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} (apartSlot : ImplSlotApart P history.rawNodes)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true)
    (hcode : (R.devm.getCode P).toList ≠ [])
    (noUpgraded : ¬ ∃ entry ∈ (Execution.committedPost R.exn committed).logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic])
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.exc) :
    (N.devm.getStor P).get implSlot = (R.devm.getStor P).get implSlot := by
  have noWrite : Exec.NoRetainedWriteTo R.exc P implSlot := by
    intro write present matching
    obtain ⟨node, nodeRetained, found⟩ := List.mem_filterMap.mp present
    obtain ⟨owner, key⟩ := Exec.StorageWrite.matches_eq_true.mp matching
    exact noUpgraded (ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded history
      capabilities bal apartSlot member committed nodeRetained found owner key)
  obtain ⟨_, _, hsg, _, _⟩ := history.rawFrame_entryFacts capabilities R member
  exact Exec.retainedNode_cell_eq_of_noRetainedWriteTo_noStateGas R.exc committed hsg
    P implSlot hcode noWrite retained

end Blanc.Lift.Usdc
