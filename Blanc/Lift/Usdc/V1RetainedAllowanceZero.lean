import Blanc.Lift.Usdc.V1RetainedContext
import Blanc.Lift.Usdc.InitRowsHistory
import Blanc.ExecutionRetainedCellZero
import Blanc.Lift.Usdc.V1ApproveRetainedLog

/-!
Tracked allowance zero under the retained Proxy/V1 context. The surrounding
history supplies entry and separation facts, without restricting discarded
execution to V1. Approve safety comes from caller exclusion or exact retained Approval values.
Neither alternative is asserted as a historical fact here.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- An exact Approval whose computed allowance slot is tracked writes zero.
Slot equality keeps the predicate scoped to the actual protected cells; it does
not assume global hash injectivity or ban unrelated approvals. -/
def V1ApprovalZeroFor (P pair : Adr) (Tr : Adr → Prop) (entry : Log) : Prop :=
  ∀ (spender : Adr) (value : B256),
    (∃ g, Tr g ∧ allowSlot pair g = allowSlot pair spender) →
    entry = ⟨P, [V1ApproveRetainedLog.approvalTopic, pair.toB256, spender.toB256],
      value.toBytes⟩ → value = 0

/-- Two independent ways to discharge V1's approve exception in this original
retained root. The log alternative admits zero writes and unrelated rows. -/
def V1ApproveEvidence (P pair : Adr) (Tr : Adr → Prop) (R : Exec.Frame) : Prop :=
  (∀ G ∈ Exec.committedFrames R.run,
    G.sevm.currentTarget = P → Sevm.selector G.sevm = 0x095ea7b3 →
    G.sevm.caller ≠ pair) ∨
  (∀ entry ∈ R.post.logs, V1ApprovalZeroFor P pair Tr entry)

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
  (capabilities : BodyStageCapabilities F)
  {P pair : Adr} {Tr : Adr → Prop} {initial : HistoricalMappingKey → Prop}
  (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
  (fresh : V1MappingFreshKeys P history initial)
  (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
  {I : Adr} {R : Exec.Frame} (member : R ∈ history.settledRoots)
  (proxy : R.pre.getCode P = Proxy.code) (impl : R.pre.getCode I = ImplV1.code)
  (slot : ((R.pre.getStor P).get implSlot).toAdr = I)
  (noUpgraded : ¬ ∃ entry ∈ R.post.logs,
    entry.address = P ∧ entry.topics = [Proxy.upgradedTopic])
  (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
  (rowSep : UsdcRowSep P pair Tr history.rawFrames)
  (initApart : InitRowsApart P pair Tr history.rawFrames)
  (approveEvidence : V1ApproveEvidence P pair Tr R)

include history capabilities initialApart fresh bal member proxy impl slot noUpgraded
  proxyApart rowSep initApart approveEvidence

omit rowSep in
/-- Every retained tracked-row write in this root is non-increasing. Its actual
parent frame is Proxy or V1 by the retained context theorem. V1 has no owner
exception; its sole caller exception is approve, and initializer stores use
the existing calldata-key separation proof. No raw-code or upgrade-write ban
is imposed on discarded child execution. -/
theorem ConfiguredHistoryTraceIn.settledRoot_v1_allowanceWrite_nonInc_of_v1Class
    (v1Class : V1RawWriteClass P pair Tr history.rawFrames)
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat := by
  obtain ⟨G, committed, chain⟩ :=
    (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run m).mp retained
  have frameMember : G ∈ history.settledFrames := by
    rw [history.settledFrames_eq]
    exact List.mem_flatMap.mpr ⟨R, member, committed⟩
  have rawMember := history.mem_rawFrames_of_mem_settledFrames G frameMember
  have nodeMember : m ∈ history.rawNodes :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix m).mpr ⟨_, rawMember, chain⟩
  have target : m.sevm.currentTarget = P :=
    (successfulSstore?_node_owner found).2.symm.trans owner
  have same : m.sevm = G.sevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  have parentTarget : G.sevm.currentTarget = P := by rw [← same]; exact target
  have context := ConfiguredHistoryTraceIn.settledRoot_proxyV1_context_of_freshKeys
    history capabilities initialApart fresh bal member proxy impl slot noUpgraded
  rcases (context m retained).2.1 target with proxyCode | v1Code
  · exact (proxyApart m nodeMember target proxyCode w found tracked).elim
  have parentCode : G.sevm.code = ImplV1.code := by rw [← same]; exact v1Code
  obtain ⟨pc, forkIn, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities _ rawMember
  rcases v1Class _ rawMember parentTarget parentCode m chain w found tracked with allowed | nonInc
  · rcases allowed with caller | ownerException | initializer
    · have callerFacts : Sevm.selector G.sevm = 0x095ea7b3 ∧ G.sevm.caller = pair := by
        change selV1T.eval (Env.root G.sevm) ∈ [0x095ea7b3] ∧
          G.sevm.caller.toB256.toAdr = pair at caller
        simpa only [selV1T_root, List.mem_singleton, toAdr_toB256] using caller
      rcases approveEvidence with noCaller | approvalLogs
      · exact (noCaller G committed parentTarget callerFacts.1 callerFacts.2).elim
      have event := V1ApproveRetainedLog.frame_approve_write_emits pc parentCode hsg
        (bal forkIn) callerFacts.1 chain found
      have rootFacts := history.rawFrame_entryFacts capabilities _
        (history.mem_rawFrames_of_mem_settledRoots R member)
      have retainedEvent := Exec.committedFrame_logs_subset_noStateGas R.run R.committed
        rootFacts.2.2.1 G committed event.2
      have key := (V1ApproveReach.successfulSstore_ordered_hashes pc parentCode hsg
        chain callerFacts.1 found).1
      change w.key = allowSlot G.sevm.caller (Sevm.dataWord G.sevm 4).toAdr at key
      rw [callerFacts.2] at key
      have zero := approvalLogs _ retainedEvent (Sevm.dataWord G.sevm 4).toAdr w.value
        (by obtain ⟨g, inTr, slotEq⟩ := tracked
            exact ⟨g, inTr, slotEq.trans key⟩)
        (by simp only [V1ApproveRetainedLog.approvalLog, parentTarget, callerFacts.2])
      rw [zero]
      exact Nat.zero_le _
    · exact (List.not_mem_nil ownerException.1).elim
    · exact ConfiguredHistoryTraceIn.initRowWritesNonInc history capabilities initApart
        _ rawMember parentTarget (.inl ⟨parentCode, initializer⟩) m chain w found tracked
  · exact nonInc

omit rowSep in
/-- An actual retained root preserves a tracked allowance cell that enters at
zero, using derived retained code control and actual write-site non-increase.
This is a root transport law; constructor seeding and pre-deployment approve
evidence must still be supplied by their own producers. -/
theorem ConfiguredHistoryTraceIn.settledRoot_v1_allowance_zero_of_v1Class
    (v1Class : V1RawWriteClass P pair Tr history.rawFrames)
    {g : Adr} (tracked : Tr g)
    (zero : (R.pre.getStor P).get (allowSlot pair g) = 0) :
    (R.post.getStor P).get (allowSlot pair g) = 0 := by
  have rawRoot := history.mem_rawFrames_of_mem_settledRoots R member
  have facts := history.rawFrame_entryFacts capabilities _ rawRoot
  have nonempty : (R.pre.getCode P).toList ≠ [] := by
    rw [proxy]
    exact (show UsdcContextCode Proxy.code from .inl rfl).ne_nil
  apply Exec.cell_zero_of_retained_nonInc_noStateGas R.run R.committed
    facts.2.2.1 nonempty _ zero
  intro m retained w found owner key
  have bound := ConfiguredHistoryTraceIn.settledRoot_v1_allowanceWrite_nonInc_of_v1Class
    history capabilities initialApart fresh bal member proxy impl slot noUpgraded
    proxyApart initApart approveEvidence v1Class retained found owner ⟨g, tracked, key.symm⟩
  simpa only [key] using bound

/-- Compatibility with the original descriptor-separation write interface. -/
theorem ConfiguredHistoryTraceIn.settledRoot_v1_allowanceWrite_nonInc_of_approveEvidence
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat := by
  exact ConfiguredHistoryTraceIn.settledRoot_v1_allowanceWrite_nonInc_of_v1Class
    history capabilities initialApart fresh bal member proxy impl slot noUpgraded
    proxyApart initApart approveEvidence
    (ConfiguredHistoryTraceIn.v1RawWriteClass_of_rowSep history capabilities rowSep)
    retained found owner tracked

/-- Compatibility with the original descriptor-separation root-zero interface. -/
theorem ConfiguredHistoryTraceIn.settledRoot_v1_allowance_zero_of_approveEvidence
    {g : Adr} (tracked : Tr g)
    (zero : (R.pre.getStor P).get (allowSlot pair g) = 0) :
    (R.post.getStor P).get (allowSlot pair g) = 0 := by
  exact ConfiguredHistoryTraceIn.settledRoot_v1_allowance_zero_of_v1Class
    history capabilities initialApart fresh bal member proxy impl slot noUpgraded
    proxyApart initApart approveEvidence
    (ConfiguredHistoryTraceIn.v1RawWriteClass_of_rowSep history capabilities rowSep)
    tracked zero

omit approveEvidence in
/-- Compatibility interface using the original caller-exclusion producer. -/
theorem ConfiguredHistoryTraceIn.settledRoot_v1_allowanceWrite_nonInc
    (noCaller : ∀ G ∈ Exec.committedFrames R.run,
      G.sevm.currentTarget = P → Sevm.selector G.sevm = 0x095ea7b3 →
      G.sevm.caller ≠ pair)
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat :=
  ConfiguredHistoryTraceIn.settledRoot_v1_allowanceWrite_nonInc_of_approveEvidence
    history capabilities initialApart fresh bal member proxy impl slot noUpgraded
    proxyApart rowSep initApart (.inl noCaller) retained found owner tracked

omit approveEvidence in
/-- Compatibility interface retaining the original zero-transport statement. -/
theorem ConfiguredHistoryTraceIn.settledRoot_v1_allowance_zero
    (noCaller : ∀ G ∈ Exec.committedFrames R.run,
      G.sevm.currentTarget = P → Sevm.selector G.sevm = 0x095ea7b3 →
      G.sevm.caller ≠ pair)
    {g : Adr} (tracked : Tr g)
    (zero : (R.pre.getStor P).get (allowSlot pair g) = 0) :
    (R.post.getStor P).get (allowSlot pair g) = 0 :=
  ConfiguredHistoryTraceIn.settledRoot_v1_allowance_zero_of_approveEvidence
    history capabilities initialApart fresh bal member proxy impl slot noUpgraded
    proxyApart rowSep initApart (.inl noCaller) tracked zero

end Blanc.Lift.Usdc
