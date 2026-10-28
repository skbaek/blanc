import Blanc.Lift.ConstructorTransaction
import Blanc.ExecutionHistoryCommittedCuts
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

/-- Starting at the actual post-constructor resume point, installed runtime
code controls later calls. Earlier contexts may be empty or run the checked
constructor; a completed constructor boundary cannot spawn the suffix root.
These structural inputs are separate from the derived terminal-safety result. -/
theorem ConfiguredHistoryTraceIn.settledRoot_implContext_after_constructor
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {I : Adr} {C K : ByteArray} {certificate : Cert} {R : Exec.Frame}
    (member : R ∈ history.settledRoots) (family : UsdcImplCode C)
    (checked : Cert.check K certificate = true)
    (noExecs : ∀ f ∈ certificate.prog, f.execsSatisfy (fun _ => false) = true)
    (noSelfdestruct : certificate.noSelfdestruct = true)
    {earlierPart suffix : List Exec.Deriv} {resumeNode : Exec.Deriv}
    (chronology : Exec.retainedNodes R.run = earlierPart ++ resumeNode :: suffix)
    (prefixNonempty : earlierPart ≠ [])
    (prefixCodes : ∀ n ∈ earlierPart, n.sevm.currentTarget = I →
      n.sevm.code.size = 0 ∨ n.sevm.code = K)
    (boundary : ∀ prior m, earlierPart = prior ++ [m] →
      ∀ n, ¬ Exec.Deriv.SpawnedAt m n)
    (installed : resumeNode.devm.getCode I = C)
    (library : C = Impl.code → resumeNode.devm.getCode usdcLib = Lib.code) :
    (∀ N ∈ resumeNode :: suffix, N.sevm.currentTarget = I →
      N.sevm.code.size = 0 ∨ N.sevm.code = K ∨ N.sevm.code = C ∨ N.sevm.code = Lib.code) ∧
    (∀ N ∈ resumeNode :: suffix, N.sevm.currentTarget = I →
      ¬ Linst.At N.sevm.code N.pc .selfdestruct) := by
  have rawRoot := history.mem_rawFrames_of_mem_settledRoots R member
  have rootFacts := history.rawFrame_entryFacts capabilities _ rawRoot
  have libFamily : UsdcContextCode Lib.code := .inr (.inr (.inr (.inr (.inr rfl))))
  have suffixRetained (N : Exec.Deriv) (inside : N ∈ resumeNode :: suffix) :
      N ∈ Exec.retainedNodes R.run := by
    rw [chronology]
    exact List.mem_append_right _ inside
  have installedAt (N : Exec.Deriv) (inside : N ∈ resumeNode :: suffix) :
      N.devm.getCode I = C := by
    rcases List.mem_cons.mp inside with rfl | later
    · exact installed
    · exact ((Exec.retainedNodes_code_after_split_noStateGas R.run R.committed
        rootFacts.2.2.1 chronology (by rw [installed]; exact family.context.ne_nil)).2
        N later).trans installed
  have libraryAt (implementation : C = Impl.code) (N : Exec.Deriv)
      (inside : N ∈ resumeNode :: suffix) : N.devm.getCode usdcLib = Lib.code := by
    rcases List.mem_cons.mp inside with rfl | later
    · exact library implementation
    · exact ((Exec.retainedNodes_code_after_split_noStateGas R.run R.committed
        rootFacts.2.2.1 chronology (by rw [library implementation]; exact libFamily.ne_nil)).2
        N later).trans (library implementation)
  have classified : ∀ N ∈ resumeNode :: suffix, N.sevm.currentTarget = I →
      N.sevm.code.size = 0 ∨ N.sevm.code = K ∨ N.sevm.code = C ∨ N.sevm.code = Lib.code := by
    refine List.forall_mem_of_positional fun before N after split earlier target => ?_
    have fullSplit : Exec.retainedNodes R.run = (earlierPart ++ before) ++ N :: after := by
      rw [chronology, split, List.append_assoc]
    have priorSuffix (m : Exec.Deriv) (inside : m ∈ before) :
        m ∈ resumeNode :: suffix := by
      rw [split]
      exact List.mem_append_left _ inside
    rcases Exec.retainedNodes_split_immediate_origin R.run R.committed fullSplit with
      ⟨empty, _⟩ | ⟨m, inside, same⟩ | ⟨prior, m, last, spawned⟩
    · cases earlierPart with
      | nil => exact (prefixNonempty rfl).elim
      | cons x xs => cases empty
    · rw [← same] at target ⊢
      rcases List.mem_append.mp inside with old | recent
      · rcases prefixCodes m old target with empty | ctor
        · exact .inl empty
        · exact .inr (.inl ctor)
      · exact earlier m recent target
    · have hm : m ∈ before := by
        by_cases empty : before = []
        · have lastPrefix : earlierPart = prior ++ [m] := by
            simpa only [empty, List.append_nil] using last
          exact (boundary prior m lastPrefix N spawned).elim
        · apply List.mem_of_getLast?
          have final := congrArg List.getLast? last
          simpa only [List.getLast?_append_of_ne_nil earlierPart empty,
            List.getLast?_append_of_ne_nil prior (List.cons_ne_nil m []),
            List.getLast?_singleton] using final
      have mRetained := suffixRetained m (priorSuffix m hm)
      have ownCode := installedAt m (priorSuffix m hm)
      obtain ⟨f, rsm, pc', cevm, step, enter, _, childSevm, _⟩ := spawned
      have childTarget : N.sevm.currentTarget = f.inner.currentTarget := by
        rw [← childSevm]
        exact Frame.enter_run_currentTarget enter
      have childCode : N.sevm.code = f.inner.code := by
        rw [← childSevm]
        exact Frame.enter_run_code enter
      apply Or.inr
      apply Or.inr
      by_cases same : m.sevm.currentTarget = I
      · obtain ⟨x, decoded, spawn, _⟩ := Evm.step_spawn_inv step
        obtain ⟨frame, frameMember, chain⟩ :=
          (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run m).mp mRetained
        have frameRaw := history.committedFrame_mem_rawFrames rawRoot frameMember
        have facts := history.rawFrame_entryFacts capabilities _ frameRaw
        have env : m.sevm = frame.sevm := Exec.Deriv.ParentPrefix.sevm_eq chain
        have codes : m.sevm.code = C ∨ m.sevm.code = Lib.code := by
          rcases earlier m hm same with empty | ctor | own | lib
          · simp only [Xinst.At, ByteArray.getInst, empty, Nat.not_lt_zero, ↓reduceDIte] at decoded
            cases decoded
          · obtain ⟨cursor, reachable, ok⟩ := cursor_of_parentPrefix_noStateGas checked
              facts.1 (by change frame.sevm.code = K; rw [← env]; exact ctor) facts.2.2.1 chain
            have impossible := ok.execsSatisfy
              (Cursor.execsSatisfy_of_reachable noExecs reachable) decoded
            cases impossible
          · exact .inl own
          · exact .inr lib
        have frameFamily : UsdcImplCode frame.sevm.code := by
          rw [← env]
          rcases codes with own | lib
          · rw [own]; exact family
          · exact .inr (.inr (.inr (.inr lib)))
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
            rcases codes with own | lib
            · exact own.symm.trans ((congrArg Sevm.code env).trans implDel.1)
            · exact (lib_ne_impl (lib.symm.trans
                ((congrArg Sevm.code env).trans implDel.1))).elim
          obtain ⟨g, w, rest, stack⟩ := Xinst.step_delegatecall_spawn_stack spawn
          have addr : w.toAdr = usdcLib := by
            rw [implDel.2 g w rest stack, toAdr_toB256]
          have actual : m.devm.getCode w.toAdr = Lib.code := by
            rw [addr]
            exact libraryAt implementation m (priorSuffix m hm)
          apply Or.inr
          rw [childCode, Xinst.step_delegatecall_spawn_code spawn stack
            (by rw [actual]; exact libFamily.not_delegation), actual]
      · have own := (Evm.step_spawn_child step enter).2.2
          (by rw [childSevm, target]; exact same)
          (by rw [childSevm, target, ownCode]; exact family.context.ne_empty)
          (by rw [childSevm, target, ownCode]; exact family.context.not_delegation)
        rw [childSevm, target] at own
        exact .inl (own.trans ownCode)
  refine ⟨classified, ?_⟩
  intro N inside target
  obtain ⟨frame, frameMember, chain⟩ :=
    (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run N).mp
      (suffixRetained N inside)
  have frameRaw := history.committedFrame_mem_rawFrames rawRoot frameMember
  have facts := history.rawFrame_entryFacts capabilities _ frameRaw
  have env : N.sevm = frame.sevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  rcases classified N inside target with empty | ctor | runtime
  · intro destruct
    simp only [Linst.At, ByteArray.getInst, empty, Nat.not_lt_zero, ↓reduceDIte] at destruct
    cases destruct
  · exact not_selfdestruct_of_parentPrefix_noStateGas checked noSelfdestruct facts.1
      (by change frame.sevm.code = K; rw [← env]; exact ctor) facts.2.2.1 chain
  · have context : UsdcContextCode N.sevm.code := by
      rcases runtime with own | lib
      · rw [own]; exact family.context
      · rw [lib]; exact libFamily
    obtain ⟨cert, certChecked, safe⟩ := usdcContextCode_certified _ context
    exact not_selfdestruct_of_parentPrefix_noStateGas certChecked safe facts.1
      (by change frame.sevm.code = N.sevm.code; rw [← env]) facts.2.2.1 chain


/-- An actual retained CREATE segment supplies the prefix and boundary facts
for the post-constructor classifier. The installed USDC runtime then survives
complete settlement of the same outer transaction. -/
theorem ConfiguredHistoryTraceIn.created_impl_runtime_survives_segment
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (stateGas : benv.stat.rules.stateGas = none)
    {R : Exec.Frame} (root : R ∈ trace.settledRoots)
    (member : R ∈ history.settledRoots)
    {before suffix : List Exec.Deriv} {spawnNode resumeNode : Exec.Deriv}
    {frame : Frame} {resume : Resume} {pc' : Nat} {child : Evm} {raw : Execution}
    (step : Evm.step ⟨spawnNode.pc, spawnNode.sevm, spawnNode.devm⟩ =
      .spawn frame resume pc')
    (enter : frame.enter = .run child) (create : frame.isCreate = true)
    (childRun : Exec child.pc child.sta child.dyna raw)
    (settles : frame.settlementCommits raw = true)
    (nodeGas : spawnNode.sevm.benvStat.rules.stateGas = none)
    (chronology : Exec.retainedNodes R.run =
      before ++ spawnNode :: (Exec.retainedNodes childRun ++ resumeNode :: suffix))
    {C K : ByteArray} {certificate : Cert} (family : UsdcImplCode C)
    (checked : Cert.check K certificate = true) (constructorImage : child.sta.code = K)
    (noExecs : ∀ f ∈ certificate.prog, f.execsSatisfy (fun _ => false) = true)
    (noSelfdestruct : certificate.noSelfdestruct = true)
    (installed : resumeNode.devm.getCode frame.inner.currentTarget = C)
    (library : C = Impl.code → resumeNode.devm.getCode usdcLib = Lib.code) :
    frame.inner.currentTarget ∉ trace.messageOut.accountsToDelete ∧
      state.getCode frame.inner.currentTarget = C := by
  have facts := history.rawFrame_entryFacts capabilities _
    (history.mem_rawFrames_of_mem_settledRoots R member)
  have rootGas : R.sevm.benvStat.rules.stateGas = none := facts.2.2.1
  have childGas : child.sta.benvStat.rules.stateGas = none := by
    rw [Evm.step_spawn_child_benvStat step enter]
    exact nodeGas
  have childCommits := Frame.raw_commits_of_settlementCommits settles
  have childRootMember : Exec.Frame.rootDeriv (Exec.Frame.ofRun childRun childCommits) ∈
      Exec.retainedNodes childRun := by
    apply (Exec.committedFrameRoots_sublist_retainedNodes childRun).subset
    apply List.mem_map.mpr
    refine ⟨Exec.Frame.ofRun childRun childCommits, ?_, rfl⟩
    simp only [Exec.committedFrames, childCommits, ↓reduceDIte]
    exact List.mem_cons_self
  have childNonempty : Exec.retainedNodes childRun ≠ [] := by
    intro empty
    rw [empty] at childRootMember
    cases childRootMember
  have constructorChain (n : Exec.Deriv) (inside : n ∈ Exec.retainedNodes childRun) :
      Exec.Deriv.ParentPrefix ⟨child.pc, child.sta, child.dyna, raw, childRun⟩ n :=
    rawNodes_parentPrefix_of_noExecs_noStateGas checked noExecs
      (Frame.enter_run_pc enter) constructorImage childGas n
      ((Exec.retainedNodes_sublist_rawNodes childRun).subset inside)
  have spawnMember : spawnNode ∈ Exec.retainedNodes R.run := by
    rw [chronology]
    exact List.mem_append_right _ List.mem_cons_self
  have spawnNonempty : spawnNode.sevm.code.size ≠ 0 := by
    intro empty
    obtain ⟨x, decoded, _, _⟩ := Evm.step_spawn_inv step
    simp only [Xinst.At, ByteArray.getInst, empty, Nat.not_lt_zero, ↓reduceDIte] at decoded
    cases decoded
  have spawnDifferent : spawnNode.sevm.currentTarget ≠ frame.inner.currentTarget := by
    intro same
    apply Evm.step_spawn_create_unprotected_noStateGas nodeGas step create
    rw [← same]
    exact Exec.rawNodes_context_protected_noStateGas R.run rootGas
      (trace.settledRoots_context_protected R root) spawnNode
      ((Exec.retainedNodes_sublist_rawNodes R.run).subset spawnMember) spawnNonempty
  have prefixCodes : ∀ n ∈ (before ++ [spawnNode]) ++ Exec.retainedNodes childRun,
      n.sevm.currentTarget = frame.inner.currentTarget →
        n.sevm.code.size = 0 ∨ n.sevm.code = K := by
    intro n inside target
    rcases List.mem_append.mp inside with earlier | constructor
    · rcases List.mem_append.mp earlier with prior | self
      · exact .inl (trace.settledRoot_before_create_context_empty root rootGas chronology
          nodeGas step create n prior target)
      · have equal := List.mem_singleton.mp self
        subst n
        exact (spawnDifferent target).elim
    · exact .inr ((congrArg Sevm.code
        (Exec.Deriv.ParentPrefix.sevm_eq (constructorChain n constructor))).trans constructorImage)
  have nonempty : (before ++ [spawnNode]) ++ Exec.retainedNodes childRun ≠ [] := by
    intro empty
    have inside : spawnNode ∈ (before ++ [spawnNode]) ++ Exec.retainedNodes childRun :=
      List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    rw [empty] at inside
    cases inside
  have boundary : ∀ prior m,
      (before ++ [spawnNode]) ++ Exec.retainedNodes childRun = prior ++ [m] →
      ∀ n, ¬ Exec.Deriv.SpawnedAt m n := by
    intro prior m last n spawned
    have lastChild : (Exec.retainedNodes childRun).getLast? = some m := by
      have final := congrArg List.getLast? last
      simpa only [List.getLast?_append_of_ne_nil (before ++ [spawnNode]) childNonempty,
        List.getLast?_append_of_ne_nil prior (List.cons_ne_nil m []),
        List.getLast?_singleton] using final
    have chain := constructorChain m (List.mem_of_getLast? lastChild)
    obtain ⟨cursor, reached, ok⟩ := cursor_of_parentPrefix_noStateGas checked
      (Frame.enter_run_pc enter) constructorImage childGas chain
    obtain ⟨f, rsm, pc, evm, spawn, _⟩ := spawned
    obtain ⟨x, decoded, _, _⟩ := Evm.step_spawn_inv spawn
    have impossible := ok.execsSatisfy (Cursor.execsSatisfy_of_reachable noExecs reached) decoded
    cases impossible
  have split : Exec.retainedNodes R.run =
      ((before ++ [spawnNode]) ++ Exec.retainedNodes childRun) ++ resumeNode :: suffix := by
    rw [chronology]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have laterSafe := (ConfiguredHistoryTraceIn.settledRoot_implContext_after_constructor history capabilities bal
    member family checked noExecs noSelfdestruct split nonempty prefixCodes boundary
    installed library).2
  have survived := trace.created_runtime_survives_of_later_terminal_safe stateGas root
    rootGas step enter create childRun nodeGas chronology checked constructorImage noExecs
    noSelfdestruct laterSafe (List.mem_cons_self) (by rw [installed]; exact family.context.ne_nil)
  exact ⟨survived.1, survived.2.trans installed⟩

/-- A retained successful CREATE execution supplies its actual child/resume
segment. Installation in that resumed state survives the outer transaction;
no separate chronology or terminal-safety witness is required. -/
theorem ConfiguredHistoryTraceIn.created_impl_runtime_survives_runOk
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (stateGas : benv.stat.rules.stateGas = none)
    {R : Exec.Frame} (root : R ∈ trace.settledRoots)
    (member : R ∈ history.settledRoots)
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {child : Evm} {raw out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run child) (create : frame.isCreate = true)
    (childRun : Exec child.pc child.sta child.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (next : Exec pc' sevm post out)
    (retained : (⟨pc, sevm, pre, out, .runOk step enter childRun resumed next⟩ : Exec.Deriv)
      ∈ Exec.retainedNodes R.run)
    (settles : frame.settlementCommits raw = true)
    (nodeGas : sevm.benvStat.rules.stateGas = none)
    {C K : ByteArray} {certificate : Cert} (family : UsdcImplCode C)
    (checked : Cert.check K certificate = true) (constructorImage : child.sta.code = K)
    (noExecs : ∀ f ∈ certificate.prog, f.execsSatisfy (fun _ => false) = true)
    (noSelfdestruct : certificate.noSelfdestruct = true)
    (installed : post.getCode frame.inner.currentTarget = C)
    (library : C = Impl.code → post.getCode usdcLib = Lib.code) :
    frame.inner.currentTarget ∉ trace.messageOut.accountsToDelete ∧
      state.getCode frame.inner.currentTarget = C := by
  have committed := (Exec.retainedNodes_segment_of_mem R.run R.committed retained).1
  obtain ⟨before, after, segment⟩ := Exec.retainedNodes_settled_spawn_segment
    (root := Exec.Frame.rootDeriv R) R.committed step enter childRun resumed next retained settles
  obtain ⟨tail, nextNodes⟩ := Exec.retainedNodes_eq_root_cons next committed
  have chronology : Exec.retainedNodes R.run = before ++
      (⟨pc, sevm, pre, out, .runOk step enter childRun resumed next⟩ : Exec.Deriv) ::
        (Exec.retainedNodes childRun ++
          (⟨pc', sevm, post, out, next⟩ : Exec.Deriv) :: (tail ++ after)) := by
    change Exec.retainedNodes R.run = _ at segment
    simpa only [nextNodes, List.cons_append] using segment
  exact ConfiguredHistoryTraceIn.created_impl_runtime_survives_segment history capabilities bal
    trace stateGas root member step enter create childRun settles nodeGas chronology
    family checked constructorImage noExecs noSelfdestruct installed library

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

/-- Proxy code, current implementation identity and the conditional V2.2 library
at one actual state. Future implementations are not required to be installed. -/
def UsdcSelectedReady (P : Adr) (W : List UsdcDeployedEntry) (state : State) : Prop :=
  state.getCode P = Proxy.code ∧
    ∃ e ∈ W, ((state.getStor P).get implSlot).toAdr = e.adr ∧
      state.getCode e.adr = e.code ∧
      (e.code = Impl.code → state.getCode usdcLib = Lib.code)

section RuntimeOrigins

variable {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
  {state : State} {bout' : BlockOutput}

/-- Selected readiness at transaction entry supplies each actual root entry.
This requires no allowance invariant or caller theorem. -/
theorem TransactionTrace.usdc_root_ready
    (trace : TransactionTrace benv bout tx index state bout')
    {P : Adr} {W : List UsdcDeployedEntry} (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (ready : UsdcSelectedReady P W benv.state)
    (R : Exec.Frame) (member : R ∈ trace.settledRoots) :
    R.pre.getCode P = Proxy.code ∧
      ∃ e ∈ W, ((R.pre.getStor P).get implSlot).toAdr = e.adr ∧ e.RuntimeReady R.pre := by
  have proxyFamily : UsdcContextCode Proxy.code := .inl rfl
  have libraryFamily : UsdcContextCode Lib.code := .inr (.inr (.inr (.inr (.inr rfl))))
  obtain ⟨e, he, address, runtime, library⟩ := ready.2
  obtain ⟨rootProxy, rootSlot⟩ := trace.settledRoots_entry_code_cell
    ready.1 proxyFamily.ne_nil proxyFamily.not_delegation implSlot R member
  refine ⟨rootProxy, e, he, ?_, ?_, ?_⟩
  · rw [rootSlot]; exact address
  · exact (trace.settledRoots_entry_code_cell runtime (impls e he).context.ne_nil
      (impls e he).context.not_delegation 0 R member).1
  · intro implementation
    exact (trace.settledRoots_entry_code_cell (library implementation) libraryFamily.ne_nil
      libraryFamily.not_delegation 0 R member).1

/-- Actual retained CREATE provenance for a USDC runtime within one transaction.
The witness keeps the original child, complete settlement and resumed parent;
its installation is local to that resume, never the final transaction state. -/
structure UsdcRuntimeCreation (trace : TransactionTrace benv bout tx index state bout')
    (I : Adr) (C : ByteArray) where
  root : Exec.Frame
  rootIn : root ∈ trace.settledRoots
  pc : Nat
  nextPc : Nat
  sevm : Sevm
  pre : Devm
  post : Devm
  frame : Frame
  resume : Resume
  child : Evm
  raw : Execution
  out : Execution
  step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume nextPc
  enter : frame.enter = .run child
  create : frame.isCreate = true
  childRun : Exec child.pc child.sta child.dyna raw
  resumed : resume.run (frame.settle raw) = .ok post
  next : Exec nextPc sevm post out
  retained : (⟨pc, sevm, pre, out, .runOk step enter childRun resumed next⟩ : Exec.Deriv)
    ∈ Exec.retainedNodes root.run
  settles : frame.settlementCommits raw = true
  nodeGas : sevm.benvStat.rules.stateGas = none
  constructor : ByteArray
  certificate : Cert
  checked : Cert.check constructor certificate = true
  constructorImage : child.sta.code = constructor
  noExecs : ∀ f ∈ certificate.prog, f.execsSatisfy (fun _ => false) = true
  noSelfdestruct : certificate.noSelfdestruct = true
  address : frame.inner.currentTarget = I
  installed : post.getCode frame.inner.currentTarget = C
  library : C = Impl.code → post.getCode usdcLib = Lib.code

/-- Runtime origin is either actual transaction-entry installation or a retained
successful CREATE with a checked constructor. It states no final-state fact. -/
def UsdcRuntimeOrigin (trace : TransactionTrace benv bout tx index state bout')
    (I : Adr) (C : ByteArray) : Prop :=
  (benv.state.getCode I = C ∧
    (C = Impl.code → benv.state.getCode usdcLib = Lib.code)) ∨
  Nonempty (UsdcRuntimeCreation trace I C)

/-- A selected implementation carries its own origin and, only for V2.2, the
origin of the fixed library. Later unused implementations need no origin here. -/
def UsdcDeployedEntry.TransactionOrigin (e : UsdcDeployedEntry)
    (trace : TransactionTrace benv bout tx index state bout') : Prop :=
  UsdcRuntimeOrigin trace e.adr e.code ∧
    (e.code = Impl.code → UsdcRuntimeOrigin trace usdcLib Lib.code)

/-- Installation and origin evidence is needed only at actual guarded writes
inside this transaction's retained roots. -/
def UsdcTransactionOrigins (P : Adr) (W : List UsdcDeployedEntry)
    (trace : TransactionTrace benv bout tx index state bout') : Prop :=
  ∀ R ∈ trace.settledRoots, ∀ N ∈ Exec.retainedNodes R.run,
    N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
    N.sevm.codeAddress = some P → ∀ write : Exec.StorageWrite,
    Exec.Deriv.successfulSstore? N = some write → write.key = implSlot →
    write.value.toAdr ∈ F2prime.upgradeTargets →
    (N.devm.getCode write.value.toAdr).toList ≠ [] →
    ∃ e ∈ W, write.value.toAdr = e.adr ∧ e.RuntimeReady N.devm ∧
      e.TransactionOrigin trace

/-- Initial selected readiness supplies both relevant entry origins. -/
theorem UsdcDeployedEntry.transactionOrigin_of_entry (e : UsdcDeployedEntry)
    (trace : TransactionTrace benv bout tx index state bout')
    (installed : benv.state.getCode e.adr = e.code)
    (library : e.code = Impl.code → benv.state.getCode usdcLib = Lib.code) :
    e.TransactionOrigin trace := by
  refine ⟨.inl ⟨installed, library⟩, ?_⟩
  intro implementation
  exact .inl ⟨library implementation, fun impossible => (lib_ne_impl impossible).elim⟩

/-- The two concrete origins share complete transaction-settlement preservation.
A newly created runtime uses its actual constructor/resume, not a final oracle. -/
theorem ConfiguredHistoryTraceIn.runtimeOrigin_preserves
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (trace : TransactionTrace benv bout tx index state bout')
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    {I : Adr} {C : ByteArray} (family : UsdcImplCode C)
    (origin : UsdcRuntimeOrigin trace I C) :
    I ∉ trace.messageOut.accountsToDelete ∧ state.getCode I = C := by
  rcases origin with ⟨installed, library⟩ | ⟨created⟩
  · have kept := ConfiguredHistoryTraceIn.impl_transaction_preserves_retained history capabilities bal family
      trace rootsIn hsg installed library
    exact ⟨kept.1, kept.2.1⟩
  · obtain ⟨created⟩ := created
    have kept := ConfiguredHistoryTraceIn.created_impl_runtime_survives_runOk history capabilities bal trace hsg
      created.rootIn (rootsIn created.root created.rootIn) created.step created.enter
      created.create created.childRun created.resumed created.next created.retained
      created.settles created.nodeGas family created.checked created.constructorImage
      created.noExecs created.noSelfdestruct created.installed created.library
    simpa only [created.address] using kept

/-- Own and conditional library origins give the selected runtime at the actual
final State, after account deletion, fee settlement and touched-account sweep. -/
theorem ConfiguredHistoryTraceIn.entryOrigin_finalReady
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    (trace : TransactionTrace benv bout tx index state bout')
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    {e : UsdcDeployedEntry} (family : UsdcImplCode e.code)
    (origin : e.TransactionOrigin trace) :
    state.getCode e.adr = e.code ∧
      (e.code = Impl.code → state.getCode usdcLib = Lib.code) := by
  refine ⟨(ConfiguredHistoryTraceIn.runtimeOrigin_preserves history capabilities bal trace rootsIn hsg family origin.1).2, ?_⟩
  intro implementation
  exact (ConfiguredHistoryTraceIn.runtimeOrigin_preserves history capabilities bal trace rootsIn hsg
    (show UsdcImplCode Lib.code from .inr (.inr (.inr (.inr rfl))))
    (origin.2 implementation)).2

/-- Actual guarded upgrade origins make selected runtime readiness survive the
whole transaction. Only initial selection and actual guarded writes need an
origin; no future-runtime installation, final readiness or deletion is assumed. -/
theorem ConfiguredHistoryTraceIn.transaction_dynamic_runtimeReady_of_origins
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {W : List UsdcDeployedEntry}
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    (trace : TransactionTrace benv bout tx index state bout')
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (proxy : benv.state.getCode P = Proxy.code)
    (slot : ∃ e ∈ W, ((benv.state.getStor P).get implSlot).toAdr = e.adr ∧
      benv.state.getCode e.adr = e.code ∧
      (e.code = Impl.code → benv.state.getCode usdcLib = Lib.code))
    (installations : ∀ R ∈ trace.settledRoots, ∀ N ∈ Exec.retainedNodes R.run,
      N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
      N.sevm.codeAddress = some P → ∀ write : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? N = some write → write.key = implSlot →
      write.value.toAdr ∈ F2prime.upgradeTargets →
      (N.devm.getCode write.value.toAdr).toList ≠ [] →
      ∃ e ∈ W, write.value.toAdr = e.adr ∧ e.RuntimeReady N.devm ∧
        e.TransactionOrigin trace)
    (apart : ∀ R ∈ trace.settledRoots, KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    P ∉ trace.messageOut.accountsToDelete ∧ state.getCode P = Proxy.code ∧
      ∃ e ∈ W, ((state.getStor P).get implSlot).toAdr = e.adr ∧
        state.getCode e.adr = e.code ∧
        (e.code = Impl.code → state.getCode usdcLib = Lib.code) := by
  have proxyFamily : UsdcContextCode Proxy.code := .inl rfl
  have ready := TransactionTrace.usdc_root_ready trace impls
    (show UsdcSelectedReady P W benv.state from ⟨proxy, slot⟩)
  have localInstall (R : Exec.Frame) (member : R ∈ trace.settledRoots)
      (N : Exec.Deriv) (retained : N ∈ Exec.retainedNodes R.run)
      (target : N.sevm.currentTarget = P) (code : N.sevm.code = Proxy.code)
      (own : N.sevm.codeAddress = some P) (write : Exec.StorageWrite)
      (found : Exec.Deriv.successfulSstore? N = some write) (key : write.key = implSlot)
      (allowed : write.value.toAdr ∈ F2prime.upgradeTargets)
      (nonempty : (N.devm.getCode write.value.toAdr).toList ≠ []) :
      ∃ e ∈ W, write.value.toAdr = e.adr ∧ e.RuntimeReady N.devm := by
    obtain ⟨e, he, address, localReady, _⟩ :=
      installations R member N retained target code own write found key allowed nonempty
    exact ⟨e, he, address, localReady⟩
  have context (R : Exec.Frame) (member : R ∈ trace.settledRoots) :=
    ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_from_installations history capabilities bal
      (rootsIn R member) (ready R member).1 impls lib (ready R member).2 governance
      (localInstall R member) (apart R member)
  have notDeleted := trace.not_deleted_of_retained_terminals hsg (a := P) (by
    intro R member
    apply ConfiguredHistoryTraceIn.settledRoot_usdcContext_terminal_safe history capabilities (rootsIn R member)
    intro N retained target
    rcases (context R member N retained).2 target with ⟨code, _⟩ | ⟨e, he, code, _⟩
    · exact .inl code
    · rw [code]; exact (impls e he).context)
  let property (word : B256) : Prop := ∃ e ∈ W, word.toAdr = e.adr ∧
    state.getCode e.adr = e.code ∧ (e.code = Impl.code → state.getCode usdcLib = Lib.code)
  have initial : property ((benv.state.getStor P).get implSlot) := by
    obtain ⟨e, he, address, runtime, library⟩ := slot
    exact ⟨e, he, address, ConfiguredHistoryTraceIn.entryOrigin_finalReady history capabilities bal trace rootsIn hsg
      (impls e he) (e.transactionOrigin_of_entry trace runtime library)⟩
  have transported := trace.cell_property_of_settledRoots implSlot hsg proxy proxyFamily.ne_nil
    proxyFamily.not_delegation notDeleted property (by
      intro R member entry
      rcases ConfiguredHistoryTraceIn.settledRoot_dynamic_implSlot_origin_code_of_f2prime history capabilities bal
          (rootsIn R member) (ready R member).1 impls lib (ready R member).2 governance
          (localInstall R member) (apart R member) with
          unchanged | ⟨N, retained, write, found, owner, key, value, allowed, nonempty, _⟩
      · rw [unchanged]; exact entry
      · have target : N.sevm.currentTarget = P :=
          (successfulSstore?_node_owner found).2.symm.trans owner
        rcases (context R member N retained).2 target with ⟨code, own⟩ | ⟨e, he, code, _⟩
        · obtain ⟨e, he, address, _, origin⟩ :=
            installations R member N retained target code own write found key allowed nonempty
          refine ⟨e, he, ?_, ConfiguredHistoryTraceIn.entryOrigin_finalReady history capabilities bal trace rootsIn hsg
            (impls e he) origin⟩
          rw [← value]; exact address
        · exact (apart R member N retained target (by rw [code]; exact impls e he)
            write found key).elim) initial
  exact ⟨notDeleted, transported.2, transported.1⟩

end RuntimeOrigins

/-- Pointwise origin evidence on the actual ordered transaction constructors.
This is a producer obligation on those traces, not an alternative replay. -/
def UsdcTransactionsOrigins (P : Adr) (W : List UsdcDeployedEntry) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    ApplyTransactionsTrace txs benv bout finalBenv finalBout → Prop
  | _, _, _, _, _, .nil .. => True
  | _, _, _, _, _, .cons head tail =>
      UsdcTransactionOrigins P W head ∧ UsdcTransactionsOrigins P W tail

/-- Selected readiness propagates through the actual transaction list and
supplies all of its root-entry facts independently of allowance caller proofs.
Actual guarded origins still have to be produced for the original history. -/
theorem ConfiguredHistoryTraceIn.transactions_dynamic_runtimeReady_of_origins
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {W : List UsdcDeployedEntry}
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (origins : UsdcTransactionsOrigins P W trace)
    (apart : ∀ R ∈ trace.settledRoots, KnownImplSlotApart P (Exec.retainedNodes R.run))
    (initial : UsdcSelectedReady P W benv.state) :
    trace.NoDelScheduled P ∧ UsdcSelectedReady P W finalBenv.state ∧
      ∀ R ∈ trace.settledRoots, R.pre.getCode P = Proxy.code ∧
        ∃ e ∈ W, ((R.pre.getStor P).get implSlot).toAdr = e.adr ∧ e.RuntimeReady R.pre := by
  induction trace with
  | nil =>
    refine ⟨trivial, initial, ?_⟩
    intro R member
    cases member
  | cons head tail ih =>
    have first := ConfiguredHistoryTraceIn.transaction_dynamic_runtimeReady_of_origins
      history capabilities bal impls lib governance head
      (fun R member => rootsIn R (List.mem_append_left _ member)) hsg initial.1 initial.2
      origins.1 (fun R member => apart R (List.mem_append_left _ member))
    have rest := ih (fun R member => rootsIn R (List.mem_append_right _ member)) hsg
      origins.2 (fun R member => apart R (List.mem_append_right _ member)) first.2
    refine ⟨⟨first.1, rest.1⟩, rest.2.1, ?_⟩
    intro R member
    rcases List.mem_append.mp member with before | after
    · exact TransactionTrace.usdc_root_ready head impls initial R before
    · exact rest.2.2 R after


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

/-- Implementation readiness crosses every actual stage of a configured
block. Enabled system calls use the common code-transport result; actual
transaction settlement uses the implementation-family safety proof. -/
theorem ConfiguredHistoryTraceIn.impl_block_preserves_retained
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {I : Adr} {C : ByteArray} (family : UsdcImplCode C)
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post)
    (rootsIn : ∀ R ∈ block.settledRoots, R ∈ history.settledRoots)
    (installed : pre.state.getCode I = C)
    (library : C = Impl.code → pre.state.getCode usdcLib = Lib.code) :
    block.NoDelScheduled I ∧ post.state.getCode I = C ∧
      (C = Impl.code → post.state.getCode usdcLib = Lib.code) := by
  have hsg := capabilities.stateGas_none block.forkIn
  have libFamily : UsdcContextCode Lib.code := .inr (.inr (.inr (.inr (.inr rfl))))
  have opening {a : Adr} {code : ByteArray} (fam : UsdcContextCode code)
      (present : pre.state.getCode a = code) : block.bodyTrace.historyState.getCode a = code := by
    have beacon := (block.bodyTrace.beacon.cell_property_of_settledRoots 0 hsg
      present fam.ne_nil fam.not_delegation (fun _ => True)
      (by intro R member ready; trivial) trivial).2
    exact (block.bodyTrace.history.cell_property_of_settledRoots 0 hsg beacon
      fam.ne_nil fam.not_delegation (fun _ => True)
      (by intro R member ready; trivial) trivial).2
  have transactions := ConfiguredHistoryTraceIn.impl_transactions_preserve_retained
    history capabilities bal family block.bodyTrace.transactions
    (fun R member => rootsIn R (List.mem_append_left _ (List.mem_append_right _ member)))
    hsg (opening family.context installed) (fun implementation => opening libFamily (library implementation))
  have closing {a : Adr} {code : ByteArray} (fam : UsdcContextCode code)
      (present : block.bodyTrace.transactionBenv.state.getCode a = code) :
      post.state.getCode a = code := by
    rw [block.postEq]
    exact (block.bodyTrace.cell_property_after_transactions_of_settledRoots 0 hsg present
      fam.ne_nil fam.not_delegation (fun _ => True)
      (by intro R member ready; trivial) trivial).2
  exact ⟨transactions.1, closing family.context transactions.2.1,
    fun implementation => closing libFamily (transactions.2.2 implementation)⟩

/-- Start at the actual after-state of a selected transaction, then retain its
suffix transactions and the source block's withdrawals, requests and rewards.
The implementation need not exist in the source block's prestate. -/
theorem ConfiguredHistoryTraceIn.impl_after_txSplit_preserves_retained
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {I : Adr} {C : ByteArray} (family : UsdcImplCode C)
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (rootsIn : ∀ R ∈ cut.after.settledRoots, R ∈ history.settledRoots)
    (installed : cut.afterBenv.state.getCode I = C)
    (library : C = Impl.code → cut.afterBenv.state.getCode usdcLib = Lib.code) :
    cut.after.NoDelScheduled I ∧ post.state.getCode I = C ∧
      (C = Impl.code → post.state.getCode usdcLib = Lib.code) := by
  have hsg := capabilities.stateGas_none block.forkIn
  have cutSg : cut.afterBenv.stat.rules.stateGas = none := by
    rw [block.txSplit_stat cut]
    exact hsg
  have transactions := ConfiguredHistoryTraceIn.impl_transactions_preserve_retained
    history capabilities bal family cut.after rootsIn cutSg installed library
  have closing {a : Adr} {code : ByteArray} (fam : UsdcContextCode code)
      (present : block.bodyTrace.transactionBenv.state.getCode a = code) :
      post.state.getCode a = code := by
    rw [block.postEq]
    exact (block.bodyTrace.cell_property_after_transactions_of_settledRoots 0 hsg present
      fam.ne_nil fam.not_delegation (fun _ => True)
      (by intro R member ready; trivial) trivial).2
  exact ⟨transactions.1, closing family.context transactions.2.1,
    fun implementation => closing (.inr (.inr (.inr (.inr (.inr rfl)))))
      (transactions.2.2 implementation)⟩

/-- Installation after an original creation cut persists through the actual
mid-history spine, including the source-block remainder and every later block. -/
theorem ConfiguredHistoryTraceIn.impl_midHistory_preserves_retained
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {I : Adr} {C : ByteArray} (family : UsdcImplCode C)
    {start : Benv} {finish : BlockChain} (mid : MidHistoryTraceIn F cfg start finish)
    (rootsIn : ∀ R ∈ mid.settledRoots, R ∈ history.settledRoots)
    (installed : start.state.getCode I = C)
    (library : C = Impl.code → start.state.getCode usdcLib = Lib.code) :
    finish.state.getCode I = C ∧
      (C = Impl.code → finish.state.getCode usdcLib = Lib.code) := by
  induction mid with
  | tail block cut =>
    exact (ConfiguredHistoryTraceIn.impl_after_txSplit_preserves_retained
      history capabilities bal family block cut
      (fun R member => rootsIn R (List.mem_append_left _ member)) installed library).2
  | step prior block ih =>
    have ready := ih (fun R member => rootsIn R (List.mem_append_left _ member)) installed library
    exact (ConfiguredHistoryTraceIn.impl_block_preserves_retained history capabilities bal
      family block (fun R member => rootsIn R (List.mem_append_right _ member)) ready.1 ready.2).2

/-- At a genuine target cut, retain the block's actual opening stages and its
original transaction prefix. No transaction after that cut is used. -/
theorem ConfiguredHistoryTraceIn.impl_before_txSplit_preserves_retained
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {I : Adr} {C : ByteArray} (family : UsdcImplCode C)
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (rootsIn : ∀ R ∈ cut.before.settledRoots, R ∈ history.settledRoots)
    (installed : pre.state.getCode I = C)
    (library : C = Impl.code → pre.state.getCode usdcLib = Lib.code) :
    cut.before.NoDelScheduled I ∧ cut.benv.state.getCode I = C ∧
      (C = Impl.code → cut.benv.state.getCode usdcLib = Lib.code) := by
  have hsg := capabilities.stateGas_none block.forkIn
  have opening {a : Adr} {code : ByteArray} (fam : UsdcContextCode code)
      (present : pre.state.getCode a = code) : block.bodyTrace.historyState.getCode a = code := by
    have beacon := (block.bodyTrace.beacon.cell_property_of_settledRoots 0 hsg
      present fam.ne_nil fam.not_delegation (fun _ => True)
      (by intro R member ready; trivial) trivial).2
    exact (block.bodyTrace.history.cell_property_of_settledRoots 0 hsg beacon
      fam.ne_nil fam.not_delegation (fun _ => True)
      (by intro R member ready; trivial) trivial).2
  exact ConfiguredHistoryTraceIn.impl_transactions_preserve_retained
    history capabilities bal family cut.before rootsIn hsg (opening family.context installed)
    (fun implementation => opening (.inr (.inr (.inr (.inr (.inr rfl))))) (library implementation))

/-- Compose a source-cut mid history with a target block's original prefix.
Both installation and historical membership refer to those exact carriers;
the source block's prestate need not contain the implementation. -/
theorem ConfiguredHistoryTraceIn.impl_midHistory_before_txSplit_preserves_retained
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {I : Adr} {C : ByteArray} (family : UsdcImplCode C)
    {start : Benv} {pre post : BlockChain} (mid : MidHistoryTraceIn F cfg start pre)
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (midRootsIn : ∀ R ∈ mid.settledRoots, R ∈ history.settledRoots)
    (prefixRootsIn : ∀ R ∈ cut.before.settledRoots, R ∈ history.settledRoots)
    (installed : start.state.getCode I = C)
    (library : C = Impl.code → start.state.getCode usdcLib = Lib.code) :
    cut.benv.state.getCode I = C ∧
      (C = Impl.code → cut.benv.state.getCode usdcLib = Lib.code) := by
  have ready := ConfiguredHistoryTraceIn.impl_midHistory_preserves_retained
    history capabilities bal family mid midRootsIn installed library
  exact (ConfiguredHistoryTraceIn.impl_before_txSplit_preserves_retained
    history capabilities bal family block cut prefixRootsIn ready.1 ready.2).2

/-- Runtime readiness at an actual retained target-transaction node follows
from installation at an earlier genuine cut and the original intervening
history. This is the form consumed at an actual proxy upgrade write. -/
theorem ConfiguredHistoryTraceIn.impl_midHistory_txSplit_retained_ready
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {e : UsdcDeployedEntry} (family : UsdcImplCode e.code)
    {start : Benv} {pre post : BlockChain} (mid : MidHistoryTraceIn F cfg start pre)
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (midRootsIn : ∀ R ∈ mid.settledRoots, R ∈ history.settledRoots)
    (prefixRootsIn : ∀ R ∈ cut.before.settledRoots, R ∈ history.settledRoots)
    (installed : start.state.getCode e.adr = e.code)
    (library : e.code = Impl.code → start.state.getCode usdcLib = Lib.code)
    {R : Exec.Frame} (root : R ∈ cut.head.settledRoots)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.run) :
    e.RuntimeReady N.devm := by
  have ready := ConfiguredHistoryTraceIn.impl_midHistory_before_txSplit_preserves_retained
    history capabilities bal family mid block cut midRootsIn prefixRootsIn installed library
  have own := (cut.head.settledRoots_entry_code_cell ready.1 family.context.ne_nil
    family.context.not_delegation 0 R root).1
  refine ⟨Exec.rawNodes_getCode R.run own family.context.ne_nil N
    ((Exec.retainedNodes_sublist_rawNodes R.run).subset retained), ?_⟩
  intro implementation
  have libFamily : UsdcContextCode Lib.code := .inr (.inr (.inr (.inr (.inr rfl))))
  have lib := (cut.head.settledRoots_entry_code_cell (ready.2 implementation)
    libFamily.ne_nil libFamily.not_delegation 0 R root).1
  exact Exec.rawNodes_getCode R.run lib libFamily.ne_nil N
    ((Exec.retainedNodes_sublist_rawNodes R.run).subset retained)

/-- An earlier genuine installation cut supplies both local readiness and the
entry-origin branch for an actual target transaction. The same original span
and target cut are used for both; no final-state origin premise is introduced. -/
theorem ConfiguredHistoryTraceIn.impl_midHistory_txSplit_retained_origin
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {e : UsdcDeployedEntry} (family : UsdcImplCode e.code)
    {start : Benv} {pre post : BlockChain} (mid : MidHistoryTraceIn F cfg start pre)
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (midRootsIn : ∀ R ∈ mid.settledRoots, R ∈ history.settledRoots)
    (prefixRootsIn : ∀ R ∈ cut.before.settledRoots, R ∈ history.settledRoots)
    (installed : start.state.getCode e.adr = e.code)
    (library : e.code = Impl.code → start.state.getCode usdcLib = Lib.code)
    {R : Exec.Frame} (root : R ∈ cut.head.settledRoots)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.run) :
    e.RuntimeReady N.devm ∧ e.TransactionOrigin cut.head := by
  have entry := ConfiguredHistoryTraceIn.impl_midHistory_before_txSplit_preserves_retained
    history capabilities bal family mid block cut midRootsIn prefixRootsIn installed library
  exact ⟨ConfiguredHistoryTraceIn.impl_midHistory_txSplit_retained_ready
    history capabilities bal family mid block cut midRootsIn prefixRootsIn installed library root retained,
    e.transactionOrigin_of_entry cut.head entry.1 entry.2⟩


/-- System CALL entry gives the same selected runtime at its actual root.
Beginning the system transaction does not replace the world state. -/
theorem SystemMessageTrace.usdc_root_ready
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    {P : Adr} {W : List UsdcDeployedEntry} (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (ready : UsdcSelectedReady P W benv.state)
    (R : Exec.Frame) (member : R ∈ trace.settledRoots) :
    R.pre.getCode P = Proxy.code ∧
      ∃ e ∈ W, ((R.pre.getStor P).get implSlot).toAdr = e.adr ∧ e.RuntimeReady R.pre := by
  have entry {a : Adr} {C : ByteArray} (family : UsdcContextCode C)
      (present : benv.state.getCode a = C) (key : B256) :
      R.pre.getCode a = C ∧ (R.pre.getStor a).get key = (benv.state.getStor a).get key := by
    simpa only [systemTransactionMessage_benv_state] using
      trace.message.settledRoots_entry_code_cell
        (by rw [systemTransactionMessage_benv_state]; exact present)
        family.ne_nil family.not_delegation key R member
  obtain ⟨e, he, address, runtime, library⟩ := ready.2
  have proxy := entry (.inl rfl) ready.1 implSlot
  refine ⟨proxy.1, e, he, ?_, (entry (impls e he).context runtime 0).1, ?_⟩
  · rw [proxy.2]; exact address
  · intro implementation
    exact (entry (.inr (.inr (.inr (.inr (.inr rfl))))) (library implementation) 0).1

/-- Selected readiness crosses an actual system CALL by its complete root
post-state. Only local guarded installations are needed: system CALL settlement
does not run the transaction's deletion and fee-sweep boundary. -/
theorem ConfiguredHistoryTraceIn.system_dynamic_runtimeReady_from_installations
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {W : List UsdcDeployedEntry}
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (initial : UsdcSelectedReady P W benv.state)
    (installations : ∀ R ∈ trace.settledRoots, ∀ N ∈ Exec.retainedNodes R.run,
      N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
      N.sevm.codeAddress = some P → ∀ write : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? N = some write → write.key = implSlot →
      write.value.toAdr ∈ F2prime.upgradeTargets →
      (N.devm.getCode write.value.toAdr).toList ≠ [] →
      ∃ e ∈ W, write.value.toAdr = e.adr ∧ e.RuntimeReady N.devm)
    (apart : ∀ R ∈ trace.settledRoots, KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    UsdcSelectedReady P W state ∧
      ∀ R ∈ trace.settledRoots, R.pre.getCode P = Proxy.code ∧
        ∃ e ∈ W, ((R.pre.getStor P).get implSlot).toAdr = e.adr ∧ e.RuntimeReady R.pre := by
  have ready := SystemMessageTrace.usdc_root_ready trace impls initial
  have finalCode {a : Adr} {C : ByteArray} (family : UsdcContextCode C)
      (present : benv.state.getCode a = C) : state.getCode a = C :=
    (trace.cell_property_of_settledRoots 0 hsg present family.ne_nil family.not_delegation
      (fun _ => True) (by intro R member entry; trivial) trivial).2
  let property (word : B256) : Prop := ∃ e ∈ W, word.toAdr = e.adr ∧
    state.getCode e.adr = e.code ∧ (e.code = Impl.code → state.getCode usdcLib = Lib.code)
  have first : property ((benv.state.getStor P).get implSlot) := by
    obtain ⟨e, he, address, runtime, library⟩ := initial.2
    exact ⟨e, he, address, finalCode (impls e he).context runtime,
      fun implementation => finalCode (.inr (.inr (.inr (.inr (.inr rfl)))))
        (library implementation)⟩
  have msgGas : (systemTransactionMessage benv target data).benv.stat.rules.stateGas = none := by
    simpa only [BenvStat.rules, systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hsg
  have final := trace.cell_property_of_settledRoots implSlot hsg initial.1
    (show UsdcContextCode Proxy.code from .inl rfl).ne_nil
    (show UsdcContextCode Proxy.code from .inl rfl).not_delegation property (by
      intro R member _
      have post := ConfiguredHistoryTraceIn.settledRoot_dynamic_runtimeReady_of_f2prime
        history capabilities bal (rootsIn R member) (ready R member).1 impls lib
        (ready R member).2 governance (installations R member) (apart R member)
      have stateEq := trace.message.settledRoots_post_state_of_call msgGas rfl R member
      obtain ⟨e, he, address, runtime, library⟩ := post.2
      refine ⟨e, he, address, ?_, ?_⟩
      · simpa only [Devm.getCode_state, stateEq] using runtime
      · intro implementation
        simpa only [Devm.getCode_state, stateEq] using library implementation) first
  exact ⟨⟨final.2, final.1⟩, ready⟩


/-- Actual guarded writes select locally installed entries; no endpoint code
or transaction-survival witness is asserted by this system-stage predicate. -/
def UsdcGuardedInstallations (P : Adr) (W : List UsdcDeployedEntry)
    (roots : List Exec.Frame) : Prop :=
  ∀ R ∈ roots, ∀ N ∈ Exec.retainedNodes R.run,
    N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
    N.sevm.codeAddress = some P → ∀ write : Exec.StorageWrite,
    Exec.Deriv.successfulSstore? N = some write → write.key = implSlot →
    write.value.toAdr ∈ F2prime.upgradeTargets →
    (N.devm.getCode write.value.toAdr).toList ≠ [] →
    ∃ e ∈ W, write.value.toAdr = e.adr ∧ e.RuntimeReady N.devm

/-- Selected runtime facts at the entries of these actual settled roots. -/
def UsdcRootsReady (P : Adr) (W : List UsdcDeployedEntry)
    (roots : List Exec.Frame) : Prop :=
  ∀ R ∈ roots, R.pre.getCode P = Proxy.code ∧
    ∃ e ∈ W, ((R.pre.getStor P).get implSlot).toAdr = e.adr ∧ e.RuntimeReady R.pre

section SelectedSystemStages

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
  (capabilities : BodyStageCapabilities F)
  (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
  {P : Adr} {W : List UsdcDeployedEntry}
  (impls : ∀ e ∈ W, UsdcImplCode e.code)
  (lib : ∀ e ∈ W, e.code = Impl.code → ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
  (governance : UsdcGovernanceF2primeOn P history.settledFrames)

include capabilities bal impls lib governance

/-- The two actual request CALLs carry selected readiness in request order. -/
theorem ConfiguredHistoryTraceIn.requests_dynamic_runtimeReady_from_installations
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (initial : UsdcSelectedReady P W benv.state)
    (installations : UsdcGuardedInstallations P W trace.settledRoots)
    (apart : ∀ R ∈ trace.settledRoots, KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    UsdcSelectedReady P W state ∧ UsdcRootsReady P W trace.settledRoots := by
  have first := ConfiguredHistoryTraceIn.system_dynamic_runtimeReady_from_installations
    history capabilities bal impls lib governance trace.withdrawal
    (fun R member => rootsIn R (List.mem_append_left _ member)) hsg initial
    (fun R member => installations R (List.mem_append_left _ member))
    (fun R member => apart R (List.mem_append_left _ member))
  have second := ConfiguredHistoryTraceIn.system_dynamic_runtimeReady_from_installations
    history capabilities bal impls lib governance trace.consolidation
    (fun R member => rootsIn R (List.mem_append_right _ member)) hsg first.1
    (fun R member => installations R (List.mem_append_right _ member))
    (fun R member => apart R (List.mem_append_right _ member))
  refine ⟨?_, ?_⟩
  · rw [trace.state_eq_consolidationState]; exact second.1
  · intro R member
    rcases List.mem_append.mp member with before | after
    · exact first.2 R before
    · exact second.2 R after

/-- The actual optional beaconStage preserves selected readiness, including the skipped arm. -/
theorem ConfiguredHistoryTraceIn.beaconStage_dynamic_runtimeReady_from_installations
    {rules : ForkRules} {benv : Benv} {state : State} {outputBal : BalBuilder}
    (trace : BeaconStageTrace rules benv state outputBal)
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (initial : UsdcSelectedReady P W benv.state)
    (installations : UsdcGuardedInstallations P W trace.settledRoots)
    (apart : ∀ R ∈ trace.settledRoots, KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    UsdcSelectedReady P W state ∧ UsdcRootsReady P W trace.settledRoots := by
  cases trace with
  | skipped =>
    refine ⟨initial, ?_⟩
    intro R member
    cases member
  | called _ _ message _ _ =>
    exact ConfiguredHistoryTraceIn.system_dynamic_runtimeReady_from_installations
      history capabilities bal impls lib governance message rootsIn hsg initial installations apart

/-- The actual optional historyStage preserves selected readiness, including the skipped arm. -/
theorem ConfiguredHistoryTraceIn.historyStage_dynamic_runtimeReady_from_installations
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State} {outputBal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state outputBal)
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (initial : UsdcSelectedReady P W benv.state)
    (installations : UsdcGuardedInstallations P W trace.settledRoots)
    (apart : ∀ R ∈ trace.settledRoots, KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    UsdcSelectedReady P W state ∧ UsdcRootsReady P W trace.settledRoots := by
  cases trace with
  | skipped =>
    refine ⟨initial, ?_⟩
    intro R member
    cases member
  | called _ _ _ _ message _ _ =>
    exact ConfiguredHistoryTraceIn.system_dynamic_runtimeReady_from_installations
      history capabilities bal impls lib governance message rootsIn hsg initial installations apart

/-- The actual optional requestStage preserves selected readiness, including the skipped arm. -/
theorem ConfiguredHistoryTraceIn.requestStage_dynamic_runtimeReady_from_installations
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (initial : UsdcSelectedReady P W benv.state)
    (installations : UsdcGuardedInstallations P W trace.settledRoots)
    (apart : ∀ R ∈ trace.settledRoots, KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    UsdcSelectedReady P W state ∧ UsdcRootsReady P W trace.settledRoots := by
  cases trace with
  | skipped =>
    refine ⟨initial, ?_⟩
    intro R member
    cases member
  | called _ message _ =>
    exact ConfiguredHistoryTraceIn.requests_dynamic_runtimeReady_from_installations
      history capabilities bal impls lib governance message rootsIn hsg initial installations apart

end SelectedSystemStages


/-- The actual withdrawal pass preserves the selected pointer and every
installed code image, including the selected implementation's library. -/
theorem StagedBodyTrace.usdc_withdrawal_ready
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    {P : Adr} {W : List UsdcDeployedEntry}
    (initial : UsdcSelectedReady P W trace.transactionBenv.state) :
    UsdcSelectedReady P W trace.withdrawalState := by
  obtain ⟨e, he, address, runtime, library⟩ := initial.2
  refine ⟨trace.withdrawalCode_of_code initial.1, e, he, ?_,
    trace.withdrawalCode_of_code runtime, fun implementation =>
      trace.withdrawalCode_of_code (library implementation)⟩
  rw [trace.withdrawalCell_of_code initial.1
    (show UsdcContextCode Proxy.code from .inl rfl).ne_nil implSlot]
  exact address

/-- Reward credits and final body projection preserve selected readiness at
the actual request-result boundary. -/
theorem StagedBodyTrace.usdc_reward_ready
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    {P : Adr} {W : List UsdcDeployedEntry}
    (initial : UsdcSelectedReady P W trace.requestState) :
    UsdcSelectedReady P W state := by
  have code (a : Adr) : state.getCode a = trace.requestState.getCode a := by
    simp only [trace.finalState_eq, trace.rewardState_eq]
    split
    · rfl
    · exact payRewards_getCode _ _ _ _ _ _
  have cell : (state.getStor P).get implSlot = (trace.requestState.getStor P).get implSlot := by
    simp only [trace.finalState_eq, trace.rewardState_eq]
    split
    · rfl
    · rw [payRewards_getStor _ _ _ _ _ (by
        rw [initial.1]; exact (show UsdcContextCode Proxy.code from .inl rfl).ne_nil)]
  obtain ⟨e, he, address, runtime, library⟩ := initial.2
  refine ⟨(code P).trans initial.1, e, he, ?_, (code e.adr).trans runtime,
    fun implementation => (code usdcLib).trans (library implementation)⟩
  rw [cell]; exact address

/-- Guarded origins follow the original source-block suffix and later blocks.
This carrier contains no final-runtime or allowance endpoint premise. -/
def UsdcMidHistoryOrigins (P : Adr) (W : List UsdcDeployedEntry)
    {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {finish : BlockChain} → MidHistoryTraceIn F cfg start finish → Prop
  | _, _, .tail _ cut => UsdcTransactionsOrigins P W cut.after
  | _, _, .step prior block =>
      UsdcMidHistoryOrigins P W prior ∧ UsdcTransactionsOrigins P W block.bodyTrace.transactions

section SelectedHistory

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
  (capabilities : BodyStageCapabilities F)
  (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
  {P : Adr} {W : List UsdcDeployedEntry}
  (impls : ∀ e ∈ W, UsdcImplCode e.code)
  (lib : ∀ e ∈ W, e.code = Impl.code → ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
  (governance : UsdcGovernanceF2primeOn P history.settledFrames)

include capabilities bal impls lib governance

/-- After the transaction list, follow the actual withdrawals, optional
requests and rewards. Readiness is derived for every actual request root. -/
theorem ConfiguredHistoryTraceIn.body_tail_dynamic_runtimeReady_from_installations
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (rootsIn : ∀ R ∈ trace.requests.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (initial : UsdcSelectedReady P W trace.transactionBenv.state)
    (installations : UsdcGuardedInstallations P W trace.requests.settledRoots)
    (apart : ∀ R ∈ trace.requests.settledRoots, KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    UsdcSelectedReady P W state ∧ UsdcRootsReady P W trace.requests.settledRoots := by
  have requestGas : (trace.transactionBenv.withState trace.withdrawalState).stat.rules.stateGas = none := by
    change trace.transactionBenv.stat.rules.stateGas = none
    rw [trace.transactions.stat_eq]
    exact hsg
  have requests := ConfiguredHistoryTraceIn.requestStage_dynamic_runtimeReady_from_installations
    history capabilities bal impls lib governance trace.requests rootsIn requestGas
    (StagedBodyTrace.usdc_withdrawal_ready trace initial) installations apart
  exact ⟨StagedBodyTrace.usdc_reward_ready trace requests.1, requests.2⟩

/-- Every actual stage of a configured block preserves selected readiness.
Transaction origins remain obligations only on that block's actual list. -/
theorem ConfiguredHistoryTraceIn.block_dynamic_runtimeReady_of_origins
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post)
    (rootsIn : ∀ R ∈ block.settledRoots, R ∈ history.settledRoots)
    (initial : UsdcSelectedReady P W pre.state)
    (origins : UsdcTransactionsOrigins P W block.bodyTrace.transactions)
    (installations : UsdcGuardedInstallations P W block.settledRoots)
    (apart : ∀ R ∈ block.settledRoots, KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    block.NoDelScheduled P ∧ UsdcSelectedReady P W post.state ∧
      UsdcRootsReady P W block.settledRoots := by
  have beaconIn (R : Exec.Frame) (member : R ∈ block.bodyTrace.beacon.settledRoots) :
      R ∈ block.settledRoots :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))
  have historyIn (R : Exec.Frame) (member : R ∈ block.bodyTrace.history.settledRoots) :
      R ∈ block.settledRoots :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member))
  have transactionIn (R : Exec.Frame) (member : R ∈ block.bodyTrace.transactions.settledRoots) :
      R ∈ block.settledRoots := List.mem_append_left _ (List.mem_append_right _ member)
  have requestIn (R : Exec.Frame) (member : R ∈ block.bodyTrace.requests.settledRoots) :
      R ∈ block.settledRoots := List.mem_append_right _ member
  have hsg := capabilities.stateGas_none block.forkIn
  have beacon := ConfiguredHistoryTraceIn.beaconStage_dynamic_runtimeReady_from_installations
    history capabilities bal impls lib governance block.bodyTrace.beacon
    (fun R member => rootsIn R (beaconIn R member)) hsg initial
    (fun R member => installations R (beaconIn R member))
    (fun R member => apart R (beaconIn R member))
  have opening := ConfiguredHistoryTraceIn.historyStage_dynamic_runtimeReady_from_installations
    history capabilities bal impls lib governance block.bodyTrace.history
    (fun R member => rootsIn R (historyIn R member)) hsg beacon.1
    (fun R member => installations R (historyIn R member))
    (fun R member => apart R (historyIn R member))
  have transactions := ConfiguredHistoryTraceIn.transactions_dynamic_runtimeReady_of_origins
    history capabilities bal impls lib governance block.bodyTrace.transactions
    (fun R member => rootsIn R (transactionIn R member)) hsg origins
    (fun R member => apart R (transactionIn R member)) opening.1
  have closing := ConfiguredHistoryTraceIn.body_tail_dynamic_runtimeReady_from_installations
    history capabilities bal impls lib governance block.bodyTrace
    (fun R member => rootsIn R (requestIn R member)) hsg transactions.2.1
    (fun R member => installations R (requestIn R member))
    (fun R member => apart R (requestIn R member))
  refine ⟨transactions.1, ?_, ?_⟩
  · rw [block.postEq]; exact closing.1
  · intro R member
    rcases List.mem_append.mp member with before | requests
    · rcases List.mem_append.mp before with openingRoots | transactionRoots
      · rcases List.mem_append.mp openingRoots with beaconRoots | historyRoots
        · exact beacon.2 R beaconRoots
        · exact opening.2 R historyRoots
      · exact transactions.2.2 R transactionRoots
    · exact closing.2 R requests


/-- Readiness starts after the actual selected transaction and crosses only
its suffix plus the source block's closing stages. -/
theorem ConfiguredHistoryTraceIn.after_txSplit_dynamic_runtimeReady_of_origins
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (rootsIn : ∀ R ∈ (MidHistoryTraceIn.tail block cut).settledRoots,
      R ∈ history.settledRoots)
    (initial : UsdcSelectedReady P W cut.afterBenv.state)
    (origins : UsdcTransactionsOrigins P W cut.after)
    (installations : UsdcGuardedInstallations P W (MidHistoryTraceIn.tail block cut).settledRoots)
    (apart : ∀ R ∈ (MidHistoryTraceIn.tail block cut).settledRoots,
      KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    cut.after.NoDelScheduled P ∧ UsdcSelectedReady P W post.state ∧
      UsdcRootsReady P W (MidHistoryTraceIn.tail block cut).settledRoots := by
  have hsg := capabilities.stateGas_none block.forkIn
  have cutGas : cut.afterBenv.stat.rules.stateGas = none := by
    rw [block.txSplit_stat cut]; exact hsg
  have transactions := ConfiguredHistoryTraceIn.transactions_dynamic_runtimeReady_of_origins
    history capabilities bal impls lib governance cut.after
    (fun R member => rootsIn R (List.mem_append_left _ member)) cutGas origins
    (fun R member => apart R (List.mem_append_left _ member)) initial
  have closing := ConfiguredHistoryTraceIn.body_tail_dynamic_runtimeReady_from_installations
    history capabilities bal impls lib governance block.bodyTrace
    (fun R member => rootsIn R (List.mem_append_right _ member)) hsg transactions.2.1
    (fun R member => installations R (List.mem_append_right _ member))
    (fun R member => apart R (List.mem_append_right _ member))
  refine ⟨transactions.1, ?_, ?_⟩
  · rw [block.postEq]; exact closing.1
  · intro R member
    rcases List.mem_append.mp member with transactionRoots | requestRoots
    · exact transactions.2.2 R transactionRoots
    · exact closing.2 R requestRoots

/-- Original suffix and later-block origins suffice for all selected-runtime
root entries, without using an allowance invariant or caller exclusion. -/
theorem ConfiguredHistoryTraceIn.mid_dynamic_runtimeReady_of_origins
    {start : Benv} {finish : BlockChain} (mid : MidHistoryTraceIn F cfg start finish)
    (rootsIn : ∀ R ∈ mid.settledRoots, R ∈ history.settledRoots)
    (initial : UsdcSelectedReady P W start.state)
    (origins : UsdcMidHistoryOrigins P W mid)
    (installations : UsdcGuardedInstallations P W mid.settledRoots)
    (apart : ∀ R ∈ mid.settledRoots, KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    mid.OutputNotDeleted P ∧ UsdcSelectedReady P W finish.state ∧
      UsdcRootsReady P W mid.settledRoots := by
  induction mid with
  | tail block cut =>
    have result := ConfiguredHistoryTraceIn.after_txSplit_dynamic_runtimeReady_of_origins
      history capabilities bal impls lib governance block cut rootsIn initial origins installations apart
    exact ⟨(cut.after.outputNotDeleted_iff_noDelScheduled P).mpr result.1, result.2⟩
  | step prior block ih =>
    have first := ih (fun R member => rootsIn R (List.mem_append_left _ member)) initial
      origins.1 (fun R member => installations R (List.mem_append_left _ member))
      (fun R member => apart R (List.mem_append_left _ member))
    have next := ConfiguredHistoryTraceIn.block_dynamic_runtimeReady_of_origins
      history capabilities bal impls lib governance block
      (fun R member => rootsIn R (List.mem_append_right _ member)) first.2.1 origins.2
      (fun R member => installations R (List.mem_append_right _ member))
      (fun R member => apart R (List.mem_append_right _ member))
    refine ⟨⟨first.1, (block.bodyTrace.transactions.outputNotDeleted_iff_noDelScheduled P).mpr next.1⟩,
      next.2.1, ?_⟩
    intro R member
    rcases List.mem_append.mp member with earlier | later
    · exact first.2.2 R earlier
    · exact next.2.2 R later

end SelectedHistory

end Blanc.Lift.Usdc
