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

/-- In an installed implementation account's storage context, retained
execution runs its own runtime or the fixed V2.2 library. The library is needed
only when that installed runtime is V2.2; proxy-slot invariants are irrelevant. -/
theorem ConfiguredHistoryTraceIn.settledRoot_implContext_of_installed
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {I : Adr} {C : ByteArray} {R : Exec.Frame}
    (member : R ∈ history.settledRoots) (family : UsdcImplCode C)
    (installed : R.pre.getCode I = C)
    (library : C = Impl.code → R.pre.getCode usdcLib = Lib.code) :
    ∀ N ∈ Exec.retainedNodes R.run, N.sevm.currentTarget = I →
      N.sevm.code = C ∨ N.sevm.code = Lib.code := by
  have rawRoot := history.mem_rawFrames_of_mem_settledRoots R member
  have libFamily : UsdcContextCode Lib.code := .inr (.inr (.inr (.inr (.inr rfl))))
  have installedAt (N : Exec.Deriv) (retained : N ∈ Exec.retainedNodes R.run) :=
    Exec.rawNodes_getCode R.run installed family.context.ne_nil N
      ((Exec.retainedNodes_sublist_rawNodes R.run).subset retained)
  refine List.forall_mem_of_positional fun before N after split earlier target => ?_
  have priorRetained (m : Exec.Deriv) (hm : m ∈ before) :
      m ∈ Exec.retainedNodes R.run := by
    rw [split]
    exact List.mem_append_left _ hm
  rcases Exec.retainedNodes_split_origin R.run R.committed split with
    ⟨_, root⟩ | ⟨m, hm, same⟩ | ⟨m, hm, spawned⟩
  · subst N
    apply Or.inl
    exact (history.settledRoots_rootOwnCode R member I target
      (by change (R.pre.getCode I).toList ≠ []; rw [installed]; exact family.context.ne_nil)
      (by change ¬ isValidDelegation (R.pre.getCode I)
          rw [installed]; exact family.context.not_delegation)).trans installed
  · rw [← same] at target ⊢
    exact earlier m hm target
  · have mRetained := priorRetained m hm
    have ownCode := installedAt m mRetained
    obtain ⟨f, resume, pc', cevm, step, enter, _, childSevm, _⟩ := spawned
    have childTarget : N.sevm.currentTarget = f.inner.currentTarget := by
      rw [← childSevm]
      exact Frame.enter_run_currentTarget enter
    have childCode : N.sevm.code = f.inner.code := by
      rw [← childSevm]
      exact Frame.enter_run_code enter
    by_cases same : m.sevm.currentTarget = I
    · obtain ⟨x, decoded, spawn, _⟩ := Evm.step_spawn_inv step
      obtain ⟨frame, frameMember, chain⟩ :=
        (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run m).mp mRetained
      have frameRaw := history.committedFrame_mem_rawFrames rawRoot frameMember
      have facts := history.rawFrame_entryFacts capabilities _ frameRaw
      have env : m.sevm = frame.sevm := Exec.Deriv.ParentPrefix.sevm_eq chain
      have frameFamily : UsdcImplCode frame.sevm.code := by
        rw [← env]
        rcases earlier m hm same with code | code
        · rw [code]; exact family
        · exact .inr (.inr (.inr (.inr code)))
      rcases usdc_exec_kind facts.1 facts.2.2.1 (bal facts.2.1) chain
          frameFamily.context decoded with call | staticcall | ⟨rfl, proxyDel | implDel⟩
      · apply Or.inl
        rw [childCode, Xinst.step_directCall_spawn_code (.inl call) spawn
          (by rw [← childTarget, target, ownCode]; exact family.context.not_delegation),
          ← childTarget, target, ownCode]
      · apply Or.inl
        rw [childCode, Xinst.step_directCall_spawn_code (.inr staticcall) spawn
          (by rw [← childTarget, target, ownCode]; exact family.context.not_delegation),
          ← childTarget, target, ownCode]
      · exact (frameFamily.ne_proxy proxyDel.1).elim
      · have implementation : C = Impl.code := by
          rcases earlier m hm same with code | code
          · exact code.symm.trans ((congrArg Sevm.code env).trans implDel.1)
          · exact (lib_ne_impl (code.symm.trans
              ((congrArg Sevm.code env).trans implDel.1))).elim
        have libraryAt := Exec.rawNodes_getCode R.run (library implementation)
          libFamily.ne_nil m ((Exec.retainedNodes_sublist_rawNodes R.run).subset mRetained)
        obtain ⟨g, w, rest, stack⟩ := Xinst.step_delegatecall_spawn_stack spawn
        have addr : w.toAdr = usdcLib := by
          rw [implDel.2 g w rest stack, toAdr_toB256]
        have actual : m.devm.getCode w.toAdr = Lib.code := by rw [addr]; exact libraryAt
        apply Or.inr
        rw [childCode, Xinst.step_delegatecall_spawn_code spawn stack
          (by rw [actual]; exact libFamily.not_delegation), actual]
    · have own := (Evm.step_spawn_child step enter).2.2
        (by rw [childSevm, target]; exact same)
        (by rw [childSevm, target, ownCode]; exact family.context.ne_empty)
        (by rw [childSevm, target, ownCode]; exact family.context.not_delegation)
      rw [childSevm, target] at own
      exact .inl (own.trans ownCode)

/-- Every installed implementation runtime survives complete transaction
settlement, including V2.2 with its fixed library delegation. No created-account
exclusion or caller-supplied terminal classifier is needed. -/
theorem ConfiguredHistoryTraceIn.impl_transaction_preserves_retained
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {I : Adr} {C : ByteArray} (family : UsdcImplCode C)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode I = C)
    (library : C = Impl.code → benv.state.getCode usdcLib = Lib.code) :
    I ∉ trace.messageOut.accountsToDelete ∧ state.getCode I = C ∧
      (C = Impl.code → state.getCode usdcLib = Lib.code) := by
  have libFamily : UsdcContextCode Lib.code := .inr (.inr (.inr (.inr (.inr rfl))))
  have ownEntry := trace.settledRoots_entry_code_cell
    installed family.context.ne_nil family.context.not_delegation 0
  have libraryEntry (implementation : C = Impl.code) := trace.settledRoots_entry_code_cell
    (library implementation) libFamily.ne_nil libFamily.not_delegation 0
  have safe : ∀ R ∈ trace.settledRoots, ∀ N ∈ Exec.retainedNodes R.run,
      N.sevm.currentTarget = I → ¬ Linst.At N.sevm.code N.pc .selfdestruct := by
    intro R member
    have classified := ConfiguredHistoryTraceIn.settledRoot_implContext_of_installed
      history capabilities bal (rootsIn R member) family (ownEntry R member).1
      (fun implementation => (libraryEntry implementation R member).1)
    apply ConfiguredHistoryTraceIn.settledRoot_usdcContext_terminal_safe
      history capabilities (rootsIn R member)
    intro N retained target
    rcases classified N retained target with own | lib
    · rw [own]; exact family.context
    · rw [lib]; exact libFamily
  have kept := trace.code_preserved_of_retained_terminals hsg installed
    family.context.ne_nil family.context.not_delegation safe
  refine ⟨kept.1, kept.2, ?_⟩
  intro implementation
  exact (trace.code_preserved_of_installedCert Lib.cert_check Lib.cert_callOnly
    Lib.cert_noSelfdestruct libFamily.not_delegation libFamily.ne_nil hsg
    (library implementation)).2

/-- The installed implementation and its conditional V2.2 library persist
through the actual ordered transaction list. This can start at the after-state
of the original successful creation cut, including earlier creation in a block. -/
theorem ConfiguredHistoryTraceIn.impl_transactions_preserve_retained
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {I : Adr} {C : ByteArray} (family : UsdcImplCode C)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode I = C)
    (library : C = Impl.code → benv.state.getCode usdcLib = Lib.code) :
    trace.NoDelScheduled I ∧ finalBenv.state.getCode I = C ∧
      (C = Impl.code → finalBenv.state.getCode usdcLib = Lib.code) := by
  induction trace with
  | nil => exact ⟨trivial, installed, library⟩
  | cons head tail ih =>
    have first := ConfiguredHistoryTraceIn.impl_transaction_preserves_retained
      history capabilities bal family head
      (fun R member => rootsIn R (List.mem_append_left _ member)) hsg installed library
    have rest := ih (fun R member => rootsIn R (List.mem_append_right _ member))
      hsg first.2.1 first.2.2
    exact ⟨⟨first.1, rest.1⟩, rest.2⟩

end Blanc.Lift.Usdc
