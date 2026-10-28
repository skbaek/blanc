import Blanc.Lift.Usdc.ProxyUpgradeLog
import Blanc.Lift.Usdc.ProxyContextCodes
import Blanc.Lift.CursorOccurrenceNoStateGas
import Blanc.Lift.CommittedFrameLogs
import Blanc.ExecutionRetainedCellAt
import Blanc.ExecutionInRootOwnCode
import Blanc.ExecutionHistoryReceiptCensus
import Blanc.ExecutionMidHistoryInNoDel

/-!
# A retained implementation-slot write entails an Upgraded log

This is a local implication for one committing raw frame of an In-history.
The implementation-slot separation premise identifies the proxy runtime at
the retained write; no history-wide code or storage continuity is assumed.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- A settlement-retained implementation-slot write executed by the proxy emits an
`Upgraded` log in the SAME committing raw root. The local code premise replaces
implementation-slot separation; same-value and later-restored writes are included.
The payload is the exact stored word, with memory facts derived from frame entry. -/
theorem ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded_data_of_proxyCode
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr}
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.exc)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? N = some write)
    (owner : write.owner = P) (key : write.key = implSlot)
    (nodeCode : N.sevm.code = Proxy.code) :
    ∃ entry ∈ (Execution.committedPost R.exn committed).logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic] ∧ entry.data = write.value.toBytes := by
  obtain ⟨frame, frameMem, chain⟩ :=
    (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.exc N).mp retained
  have frameRaw := history.committedFrame_mem_rawFrames member frameMem
  have nodeTarget : N.sevm.currentTarget = P :=
    (successfulSstore?_node_owner found).2.symm.trans owner
  have sameSevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  change N.sevm = frame.sevm at sameSevm
  have frameCode : frame.sevm.code = Proxy.code := by
    rw [← sameSevm]
    exact nodeCode
  have target : frame.sevm.currentTarget = P := by
    rw [← sameSevm]
    exact nodeTarget
  obtain ⟨pcZero, forkIn, hsg, fresh, _⟩ :=
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
  have slot : ∃ rest, N.devm.stack = implSlot :: write.value :: rest := by
    have stackEq := actual.popped
    rw [actualNode, actualKey, actualValue, key] at stackEq
    exact ⟨_, stackEq⟩
  obtain ⟨rest, slot⟩ := slot
  have frameLog : ∃ entry ∈ frame.post.logs,
      entry.address = frame.sevm.currentTarget ∧ entry.topics = [Proxy.upgradedTopic] ∧
      entry.data = write.value.toBytes := by
    rcases frame with ⟨pc, sevm, pre, out, run, frameCommitted⟩
    dsimp only [Blanc.Exec.Frame.rootDeriv] at pcZero chain
    subst pc
    have wf : Mem.Wf pre.memory := by
      change Exec.FreshEntry sevm pre at fresh
      rw [fresh.2]
      exact Mem.wf_empty
    exact Proxy.proxy_implSstore_emitsUpgraded_data run frameCommitted frameCode hsg frameBal
      wf chain decoded slot
  obtain ⟨entry, present, address, topics, payload⟩ := frameLog
  obtain ⟨_, _, rootHsg, _, _⟩ := history.rawFrame_entryFacts capabilities R member
  exact ⟨entry, Exec.committedFrame_logs_subset_noStateGas R.exc committed rootHsg
    frame frameMem present, address.trans target, topics, payload⟩

/-- Compatibility projection preserving the original address/topic-only result. -/
theorem ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded_of_proxyCode
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr}
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.exc)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? N = some write)
    (owner : write.owner = P) (key : write.key = implSlot)
    (nodeCode : N.sevm.code = Proxy.code) :
    ∃ entry ∈ (Execution.committedPost R.exn committed).logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic] := by
  obtain ⟨entry, present, address, topics, _⟩ :=
    ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded_data_of_proxyCode history capabilities bal member
      committed retained found owner key nodeCode
  exact ⟨entry, present, address, topics⟩

/-- Every settlement-retained successful implementation-slot write has an
`Upgraded` log in the same committing raw root's endpoint. This includes
same-value writes and writes whose value is later restored. Direct write
attribution needs no code-at-entry or endpoint-change premise. -/
theorem ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded_data
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
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic] ∧ entry.data = write.value.toBytes := by
  have nodeMem : N ∈ history.rawNodes :=
    history.rawNodes_of_mem_rawFrames R member N
      ((Exec.retainedNodes_sublist_rawNodes R.exc).subset retained)
  have nodeTarget : N.sevm.currentTarget = P :=
    (successfulSstore?_node_owner found).2.symm.trans owner
  have nodeCode : N.sevm.code = Proxy.code := by
    by_contra other
    exact (apartSlot N nodeMem nodeTarget other write found key).elim
  exact ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded_data_of_proxyCode history capabilities bal
    member committed retained found owner key nodeCode

/-- Compatibility projection preserving the original separated-slot API. -/
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
  obtain ⟨entry, present, address, topics, _⟩ :=
    ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded_data history capabilities bal apartSlot member
      committed retained found owner key
  exact ⟨entry, present, address, topics⟩

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

/-- A value predicate for the target decoded from an actual proxy Upgraded log.
Other addresses and topics impose no condition. This is correspondence input,
not an assumption about code or selection at a different state. -/
def UpgradedTargetSatisfies (P : Adr) (property : Adr → Prop) (entry : Log) : Prop :=
  entry.address = P → entry.topics = [Proxy.upgradedTopic] →
    property entry.data.toB256.toAdr

/-- The value of every actual retained proxy implementation write satisfies
any target predicate established by the same root's actual Upgraded logs. -/
theorem ConfiguredHistoryTraceIn.retained_implSstore_target_of_logs
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {R : Exec.Frame} (member : R ∈ history.settledRoots)
    (property : Adr → Prop)
    (logs : ∀ entry ∈ R.post.logs, UpgradedTargetSatisfies P property entry)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.run)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? N = some write)
    (owner : write.owner = P) (key : write.key = implSlot)
    (nodeCode : N.sevm.code = Proxy.code) : property write.value.toAdr := by
  obtain ⟨entry, present, address, topics, payload⟩ :=
    ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded_data_of_proxyCode history
      capabilities bal (R := Exec.Frame.rootDeriv R)
      (history.mem_rawFrames_of_mem_settledRoots R member) R.committed retained
      found owner key nodeCode
  have selected := logs entry present address topics
  rw [payload, B256.toB256_toBytes] at selected
  exact selected

/-- A range census on the same original mainnet history constrains every
retained proxy implementation target strictly between the two actual cuts.
Use target inequality to exclude premature selection, or membership to select
an already-created runtime family. Neither conclusion assumes earlier code
emptiness, final runtime readiness, or an order extension to F2prime. -/
theorem ConfiguredHistoryTraceIn.retained_implSstore_target_between_txSplits_of_census
    {checkpoint origin completed pre post future : BlockChain}
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint origin)
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed) {i : Nat}
    (afterCut : first.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post) {j : Nat}
    (beforeCut : last.bodyTrace.transactions.TxSplit j)
    (after : ConfiguredHistoryTraceIn HistFork mainnetChainConfig post future)
    (early : last.block.header.timestamp < mainnetCancunTimestamp)
    {lo hi : Nat} (lower : lo ≤ first.block.header.number)
    (upper : last.block.header.number ≤ hi) {P : Adr} (property : Adr → Prop)
    (census : ((((before.step first).append later).step last).append after).ReceiptCensus
      lo hi (UpgradedTargetSatisfies P property))
    {R : Exec.Frame}
    (member : R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.run)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? N = some write)
    (owner : write.owner = P) (key : write.key = implSlot)
    (nodeCode : N.sevm.code = Proxy.code) : property write.value.toAdr := by
  have logs := ConfiguredHistoryTraceIn.root_logs_between_txSplits_of_mainnet_census
    before first afterCut later last beforeCut after early lower upper
    (UpgradedTargetSatisfies P property) census
  exact ConfiguredHistoryTraceIn.retained_implSstore_target_of_logs
    ((((before.step first).append later).step last).append after)
    BodyStageCapabilities.historical (fun h => h.bal_none)
    (ConfiguredHistoryTraceIn.mem_settledRoots_of_between_txSplits
      before first afterCut later last beforeCut after member)
    property (logs R member) retained found owner key nodeCode

end Blanc.Lift.Usdc
