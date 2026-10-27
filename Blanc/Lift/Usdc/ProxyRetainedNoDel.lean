import Blanc.ExecutionRetainedDeletionSafety
import Blanc.Lift.Usdc.ProxyRetainedContextCodes

/-!
No-deletion for actual settled USDC roots, from retained context classification
and certificate decoding along actual same-frame prefixes. The original V1 and
installed-world consumers share the same retained deletion-safety proof.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

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
  have safe : ∀ N ∈ Exec.retainedNodes R.run, N.sevm.currentTarget = P →
      ¬ Linst.At N.sevm.code N.pc .selfdestruct := by
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

end Blanc.Lift.Usdc
