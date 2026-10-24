import Blanc.Lift.Usdc.ProxyUpgradeLog
import Blanc.Lift.Usdc.ProxyContextCodes
import Blanc.Lift.CursorOccurrenceNoStateGas
import Blanc.Lift.CommittedFrameLogs

/-!
# A committed implementation-slot change entails an Upgraded log

This is a local implication for one committing raw frame of an In-history.
The implementation-slot separation premise identifies the proxy runtime at
the retained write; no history-wide code or storage continuity is assumed.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

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
  obtain ⟨write, frame, retained, owner, key, value, last, frameMem, frameRaw,
    chain, target, stack, cursor⟩ :=
    history.exists_retainedSstore_frame_sstoreCursor capabilities member committed hcode changed
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
  have nodeMem : write.occurrence.node ∈ history.rawNodes :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix write.occurrence.node).mpr
      ⟨Blanc.Exec.Frame.rootDeriv frame, frameRaw, chain⟩
  have nodeTarget : write.occurrence.node.sevm.currentTarget = P := owner
  have nodeCode : write.occurrence.node.sevm.code = Proxy.code := by
    by_contra other
    exact (apartSlot write.occurrence.node nodeMem nodeTarget other
      write.storageWrite found key).elim
  have sameSevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  change write.occurrence.node.sevm = frame.sevm at sameSevm
  have frameCode : frame.sevm.code = Proxy.code := by
    rw [← sameSevm]
    exact nodeCode
  obtain ⟨pcZero, forkIn, hsg, _, _⟩ :=
    history.rawFrame_entryFacts capabilities (Blanc.Exec.Frame.rootDeriv frame) frameRaw
  have frameBal : frame.sevm.benvStat.rules.bal = none := bal forkIn
  have decoded : Ninst.At write.occurrence.node.sevm.code write.occurrence.node.pc
      (.reg .sstore) := by
    rw [← write.instruction_eq]
    exact write.occurrence.decoded
  obtain ⟨rest, stackEq⟩ := stack
  have slot : ∃ v rest, write.occurrence.node.devm.stack = implSlot :: v :: rest := by
    rw [key] at stackEq
    exact ⟨write.value, rest, stackEq⟩
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

end Blanc.Lift.Usdc
