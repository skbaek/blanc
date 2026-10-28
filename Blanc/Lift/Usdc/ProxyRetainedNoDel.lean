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

end Blanc.Lift.Usdc
