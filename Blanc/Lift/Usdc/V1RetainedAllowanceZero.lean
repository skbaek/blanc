import Blanc.Lift.Usdc.V1RetainedContext
import Blanc.Lift.Usdc.InitRowsHistory
import Blanc.ExecutionRetainedCellZero

/-!
Tracked allowance zero under the retained Proxy/V1 context. The surrounding
history supplies entry and separation facts, without restricting discarded
execution to V1. Caller exclusion is an independent producer obligation.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

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
  (noCaller : ∀ G ∈ Exec.committedFrames R.run,
    G.sevm.currentTarget = P → Sevm.selector G.sevm = 0x095ea7b3 →
    G.sevm.caller ≠ pair)

include history capabilities initialApart fresh bal member proxy impl slot noUpgraded
  proxyApart rowSep initApart noCaller

/-- Every retained tracked-row write in this root is non-increasing. Its actual
parent frame is Proxy or V1 by the retained context theorem. V1 has no owner
exception; its sole caller exception is approve, and initializer stores use
the existing calldata-key separation proof. No raw-code or upgrade-write ban
is imposed on discarded child execution. -/
theorem ConfiguredHistoryTraceIn.settledRoot_v1_allowanceWrite_nonInc
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
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities _ rawMember
  rcases rawWrite_allowClass pc hsg chain ImplV1.cert_check implV1_wsCert parentCode
      (by decide) implV1_allowSitesOk ((rowSep _ rawMember parentTarget).1 parentCode)
      found tracked with allowed | nonInc
  · rcases allowed with caller | ownerException | initializer
    · have callerFacts : Sevm.selector G.sevm = 0x095ea7b3 ∧ G.sevm.caller = pair := by
        change selV1T.eval (Env.root G.sevm) ∈ [0x095ea7b3] ∧
          G.sevm.caller.toB256.toAdr = pair at caller
        simpa only [selV1T_root, List.mem_singleton, toAdr_toB256] using caller
      exact (noCaller G committed parentTarget callerFacts.1 callerFacts.2).elim
    · exact (List.not_mem_nil ownerException.1).elim
    · exact ConfiguredHistoryTraceIn.initRowWritesNonInc history capabilities initApart
        _ rawMember parentTarget (.inl ⟨parentCode, initializer⟩) m chain w found tracked
  · rw [target] at nonInc
    exact nonInc

/-- An actual retained root preserves a tracked allowance cell that enters at
zero, using derived retained code control and actual write-site non-increase.
This is a root transport law; constructor seeding and pre-deployment caller
exclusion must still be supplied by their own execution proofs. -/
theorem ConfiguredHistoryTraceIn.settledRoot_v1_allowance_zero
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
  have bound := ConfiguredHistoryTraceIn.settledRoot_v1_allowanceWrite_nonInc
    history capabilities initialApart fresh bal member proxy impl slot noUpgraded
    proxyApart rowSep initApart noCaller retained found owner ⟨g, tracked, key.symm⟩
  simpa only [key] using bound

end Blanc.Lift.Usdc
