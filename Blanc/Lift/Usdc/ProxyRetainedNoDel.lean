import Blanc.ExecutionRetainedDeletionSafety
import Blanc.ExecutionDeletionProvenance
import Blanc.Lift.Usdc.ProxyRetainedContextCodes

/-!
No-deletion for actual settled USDC roots, from retained context classification
and certificate decoding along actual same-frame prefixes. The original V1 and
installed-world consumers share the same retained deletion-safety proof.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Checked USDC-family code excludes SELFDESTRUCT at each actual retained
node in the selected storage context. No entry installation or no-deletion
invariant is used; actual history membership supplies each frame's entry facts. -/
theorem ConfiguredHistoryTraceIn.settledRoot_usdcContext_terminal_safe
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {P : Adr} {R : Exec.Frame} (member : R ∈ history.settledRoots)
    (classified : ∀ N ∈ Exec.retainedNodes R.run, N.sevm.currentTarget = P →
      UsdcContextCode N.sevm.code) :
    ∀ N ∈ Exec.retainedNodes R.run, N.sevm.currentTarget = P →
      ¬ Linst.At N.sevm.code N.pc .selfdestruct := by
  have rawRoot := history.mem_rawFrames_of_mem_settledRoots R member
  intro N retained target
  obtain ⟨frame, frameMember, chain⟩ :=
    (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run N).mp retained
  have frameRaw := history.committedFrame_mem_rawFrames rawRoot frameMember
  have facts := history.rawFrame_entryFacts capabilities _ frameRaw
  have same : N.sevm = frame.sevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  have family := classified N retained target
  obtain ⟨certificate, checked, noSelfdestruct⟩ := usdcContextCode_certified _ family
  exact not_selfdestruct_of_parentPrefix_noStateGas checked noSelfdestruct facts.1
    (by change frame.sevm.code = N.sevm.code; rw [← same]) facts.2.2.1 chain

/-- Convert the USDC retained-context classification into deletion safety of
one actual settled root. The classifier is an internal producer output: this
lemma does not assume that future implementations exist at root entry. -/
theorem ConfiguredHistoryTraceIn.settledRoot_usdcContext_noDel
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {P : Adr} {R : Exec.Frame} (member : R ∈ history.settledRoots)
    (classified : ∀ N ∈ Exec.retainedNodes R.run, N.sevm.currentTarget = P →
      UsdcContextCode N.sevm.code)
    (initial : Devm.NoDel P R.pre) : Devm.NoDel P R.post := by
  have rawRoot := history.mem_rawFrames_of_mem_settledRoots R member
  have rootFacts := history.rawFrame_entryFacts capabilities _ rawRoot
  have safe := ConfiguredHistoryTraceIn.settledRoot_usdcContext_terminal_safe
    history capabilities member classified
  have result := Exec.inv_noDel_of_retained_terminal_safe R.run R.committed
    rootFacts.2.2.1 safe initial
  rcases R with ⟨pc, sevm, pre, out, run, committed⟩
  cases out with
  | error error => cases committed
  | ok post => exact result

/-- A selected settled root preserves the proxy's NoDel invariant from its
actual input. Implementation-slot separation is required only for retained
V1 writes in this same root; discarded raw children need no safety premise. -/
theorem ConfiguredHistoryTraceIn.settledRoot_proxyV1_noDel
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P I : Adr} {R : Exec.Frame} (member : R ∈ history.settledRoots)
    (proxy : R.pre.getCode P = Proxy.code) (impl : R.pre.getCode I = ImplV1.code)
    (slot : ((R.pre.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ¬ ∃ entry ∈ R.post.logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic])
    (v1Apart : ∀ N ∈ Exec.retainedNodes R.run, N.sevm.currentTarget = P →
      N.sevm.code = ImplV1.code → ∀ write : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? N = some write → write.key ≠ implSlot)
    (initial : Devm.NoDel P R.pre) : Devm.NoDel P R.post := by
  have classified := ConfiguredHistoryTraceIn.settledRoot_retained_proxyV1_context
    history capabilities bal member proxy impl slot noUpgraded v1Apart
  apply ConfiguredHistoryTraceIn.settledRoot_usdcContext_noDel history capabilities
    member ?_ initial
  intro N retained target
  rcases (classified N retained).2.1 target with proxyCode | implCode
  · exact .inl proxyCode
  · exact .inr (.inl implCode)

/-- The existing installed-world classifier discharges retained deletion safety
for every USDC runtime, including retained upgrades authorized by original F2′.
This specialization still needs the listed runtimes installed at the selected
root; it makes no claim about earlier roots before those deployments. -/
theorem ConfiguredHistoryTraceIn.settledRoot_proxyWorld_noDel_of_f2prime
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {W : List UsdcDeployedEntry} {R : Exec.Frame}
    (member : R ∈ history.settledRoots)
    (proxy : R.pre.getCode P = Proxy.code)
    (installed : ∀ e ∈ W, R.pre.getCode e.adr = e.code)
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (slot : ∃ e ∈ W, ((R.pre.getStor P).get implSlot).toAdr = e.adr)
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    (targets : ∀ a ∈ F2prime.upgradeTargets, ∃ e ∈ W, e.adr = a)
    (apart : KnownImplSlotApart P (Exec.retainedNodes R.run))
    (initial : Devm.NoDel P R.pre) : Devm.NoDel P R.post := by
  have classified := ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_of_f2prime
    history capabilities bal member proxy installed impls lib slot governance targets apart
  apply ConfiguredHistoryTraceIn.settledRoot_usdcContext_noDel history capabilities
    member ?_ initial
  intro N retained target
  rcases (classified N retained).2 target with ⟨proxyCode, _⟩ | ⟨e, he, code⟩
  · exact .inl proxyCode
  · rw [code]
    exact (impls e he).context

/-- Nonempty account code observed at an actual retained USDC-family node
survives final transaction settlement. The same selected root belongs to both
the transaction and the configured history. Its retained code classifier
supplies terminal safety, so neither entry installation nor an initial or
final no-deletion premise is required. Earlier creation in this root is allowed. -/
theorem ConfiguredHistoryTraceIn.transaction_retained_usdcContext_code
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    {R : Exec.Frame} (inHistory : R ∈ history.settledRoots)
    (inTransaction : R ∈ trace.settledRoots)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.run) {P : Adr}
    (nonempty : (N.devm.getCode P).toList ≠ [])
    (classified : ∀ node ∈ Exec.retainedNodes R.run, node.sevm.currentTarget = P →
      UsdcContextCode node.sevm.code) :
    state.getCode P = N.devm.getCode P := by
  exact trace.retainedNode_getCode_of_terminal_safe hsg inTransaction retained nonempty
    (ConfiguredHistoryTraceIn.settledRoot_usdcContext_terminal_safe history capabilities inHistory classified)

end Blanc.Lift.Usdc
