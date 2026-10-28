import Blanc.ExecutionRetainedNodeOrigin
import Blanc.ExecutionInRootOwnCode
import Blanc.ExecutionNonceCode
import Blanc.Lift.Usdc.ProxyCommittedUpgradeLog
import Blanc.Lift.Usdc.GovernanceHistory

/-! Coupled USDC context and implementation-pointer induction within one retained root. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Runtime identity at an actual execution position, together with the library
needed when that runtime is V2.2. This is a local installation fact, not a
code-family classification of arbitrary execution nodes. -/
def UsdcDeployedEntry.RuntimeReady (e : UsdcDeployedEntry) (d : Devm) : Prop :=
  d.getCode e.adr = e.code ∧ (e.code = Impl.code → d.getCode usdcLib = Lib.code)

/-- Coupled retained induction from the initial selected implementation and
actual upgrade-position installations. Future implementations need not exist
at root entry; nonempty code is carried from the original earlier position.
The library requirement follows the running implementation even if a nested
call subsequently changes the proxy pointer. -/
theorem ConfiguredHistoryTraceIn.retained_proxyWorld_context_from_installations
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {W : List UsdcDeployedEntry} {R : Exec.Deriv}
    (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) (rootOwn : RootOwnCode R)
    (proxy : R.devm.getCode P = Proxy.code)
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (slot : ∃ e ∈ W, ((R.devm.getStor P).get implSlot).toAdr = e.adr ∧
      e.RuntimeReady R.devm)
    (upgrades : ∀ N ∈ Exec.retainedNodes R.exc,
      N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
      (RootOwnEntry R → N.sevm.codeAddress = some P) →
      ∀ write : Exec.StorageWrite, Exec.Deriv.successfulSstore? N = some write →
      write.key = implSlot → ∃ e ∈ W, write.value.toAdr = e.adr ∧
        e.RuntimeReady N.devm)
    (apart : ∀ N ∈ Exec.retainedNodes R.exc, N.sevm.currentTarget = P →
      ∀ e ∈ W, N.sevm.code = e.code → ∀ write : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? N = some write → write.key ≠ implSlot) :
    ∀ N ∈ Exec.retainedNodes R.exc,
      (∃ e ∈ W, ((N.devm.getStor P).get implSlot).toAdr = e.adr ∧ e.RuntimeReady N.devm) ∧
      (N.sevm.currentTarget = P →
        (N.sevm.code = Proxy.code ∧
          (RootOwnEntry R → N.sevm.codeAddress = some P)) ∨ ∃ e ∈ W, N.sevm.code = e.code ∧
          (e.code = Impl.code → N.devm.getCode usdcLib = Lib.code)) := by
  have proxyFam : UsdcContextCode Proxy.code := .inl rfl
  have nonempty : (R.devm.getCode P).toList ≠ [] := by
    rw [proxy]
    exact proxyFam.ne_nil
  have rootHsg := (history.rawFrame_entryFacts capabilities R member).2.2.1
  have installedP (N : Exec.Deriv) (retained : N ∈ Exec.retainedNodes R.exc) :=
    Exec.rawNodes_getCode R.exc proxy proxyFam.ne_nil N
      ((Exec.retainedNodes_sublist_rawNodes R.exc).subset retained)
  have all : ∀ before N after, Exec.retainedNodes R.exc = before ++ N :: after →
      (∃ e ∈ W, ((N.devm.getStor P).get implSlot).toAdr = e.adr ∧ e.RuntimeReady N.devm) ∧
      (N.sevm.currentTarget = P →
        (N.sevm.code = Proxy.code ∧
          (RootOwnEntry R → N.sevm.codeAddress = some P)) ∨ ∃ e ∈ W, N.sevm.code = e.code ∧
          (e.code = Impl.code → N.devm.getCode usdcLib = Lib.code)) := by
    refine List.forall_split_of_positional fun before N after split earlier => ?_
    have retained : N ∈ Exec.retainedNodes R.exc := by
      rw [split]
      exact List.mem_append_right _ List.mem_cons_self
    have previous (m : Exec.Deriv) (hm : m ∈ before) :
        (∃ e ∈ W, ((m.devm.getStor P).get implSlot).toAdr = e.adr ∧ e.RuntimeReady m.devm) ∧
        (m.sevm.currentTarget = P →
          (m.sevm.code = Proxy.code ∧
          (RootOwnEntry R → m.sevm.codeAddress = some P)) ∨ ∃ e ∈ W, m.sevm.code = e.code ∧
          (e.code = Impl.code → m.devm.getCode usdcLib = Lib.code)) := by
      obtain ⟨b₁, b₂, equal⟩ := List.append_of_mem hm
      exact earlier b₁ m b₂ equal
    have priorRetained (m : Exec.Deriv) (hm : m ∈ before) :
        m ∈ Exec.retainedNodes R.exc := by
      rw [split]
      exact List.mem_append_left _ hm
    have codeEarlier (m : Exec.Deriv) (hm : m ∈ before) {a : Adr} {code : ByteArray}
        (actual : m.devm.getCode a = code) (positive : code.toList ≠ []) :
        N.devm.getCode a = code := by
      obtain ⟨b₁, b₂, equal⟩ := List.append_of_mem hm
      have ordered : Exec.retainedNodes R.exc = b₁ ++ m :: (b₂ ++ N :: after) := by
        rw [split, equal, List.append_assoc, List.cons_append]
      exact (Exec.retainedNodes_getCode_of_ordered_noStateGas R.exc committed rootHsg
        ordered (by rw [actual]; exact positive)).trans actual
    have libraryEarlier (m : Exec.Deriv) (hm : m ∈ before) {code : ByteArray}
        (ready : code = Impl.code → m.devm.getCode usdcLib = Lib.code) :
        code = Impl.code → N.devm.getCode usdcLib = Lib.code := by
      intro implementation
      exact codeEarlier m hm (ready implementation)
        (show UsdcContextCode Lib.code from .inr (.inr (.inr (.inr (.inr rfl))))).ne_nil
    have readyEarlier (m : Exec.Deriv) (hm : m ∈ before) (e : UsdcDeployedEntry)
        (he : e ∈ W) (ready : e.RuntimeReady m.devm) : e.RuntimeReady N.devm :=
      ⟨codeEarlier m hm ready.1 (impls e he).context.ne_nil,
        libraryEarlier m hm ready.2⟩
    have cell : ∃ e ∈ W, ((N.devm.getStor P).get implSlot).toAdr = e.adr ∧
        e.RuntimeReady N.devm := by
      rcases Exec.retainedNodes_cellProv_noStateGas R.exc committed implSlot
          rootHsg nonempty split with equal | ⟨b₁, b₂, m, write, equal, found, own, key, value⟩
      · obtain ⟨e, he, address, ready⟩ := slot
        refine ⟨e, he, ?_, ?_⟩
        · rw [equal]; exact address
        · refine ⟨Exec.rawNodes_getCode R.exc ready.1 (impls e he).context.ne_nil N
            ((Exec.retainedNodes_sublist_rawNodes R.exc).subset retained), ?_⟩
          intro implementation
          exact Exec.rawNodes_getCode R.exc (ready.2 implementation)
            (show UsdcContextCode Lib.code from .inr (.inr (.inr (.inr (.inr rfl))))).ne_nil N
            ((Exec.retainedNodes_sublist_rawNodes R.exc).subset retained)
      · have hm : m ∈ before := by
          rw [equal]
          exact List.mem_append_right _ List.mem_cons_self
        have target : m.sevm.currentTarget = P :=
          (successfulSstore?_node_owner found).2.symm.trans own
        rcases (previous m hm).2 target with ⟨proxyCode, address⟩ | ⟨e, he, code, _⟩
        · obtain ⟨e, he, address, ready⟩ :=
            upgrades m (priorRetained m hm) target proxyCode address write found key
          exact ⟨e, he, by rw [← value]; exact address, readyEarlier m hm e he ready⟩
        · exact (apart m (priorRetained m hm) target e he code write found key).elim
    refine ⟨cell, ?_⟩
    intro target
    rcases Exec.retainedNodes_split_origin R.exc committed split with
      ⟨_, root⟩ | ⟨m, hm, same⟩ | ⟨m, hm, spawned⟩
    · change N = R at root
      subst N
      have notDelegation : ¬ isValidDelegation (R.devm.getCode P) := by
        rw [proxy]
        exact proxyFam.not_delegation
      exact .inl ⟨(rootOwn P target nonempty notDelegation).trans proxy,
        fun own => (own P target nonempty notDelegation).2⟩
    · rw [← same] at target ⊢
      rcases (previous m hm).2 target with own | ⟨e, he, code, ready⟩
      · exact .inl own
      · exact .inr ⟨e, he, code, libraryEarlier m hm ready⟩
    · have mRetained := priorRetained m hm
      have proxyCode := installedP m mRetained
      obtain ⟨f, resume, pc', cevm, step, enter, _, childSevm, _⟩ := spawned
      have childTarget : N.sevm.currentTarget = f.inner.currentTarget := by
        rw [← childSevm]
        exact Frame.enter_run_currentTarget enter
      have childCode : N.sevm.code = f.inner.code := by
        rw [← childSevm]
        exact Frame.enter_run_code enter
      by_cases same : m.sevm.currentTarget = P
      · obtain ⟨x, decoded, spawn, _⟩ := Evm.step_spawn_inv step
        obtain ⟨frame, frameMember, chain⟩ :=
          (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.exc m).mp mRetained
        have frameRaw := history.committedFrame_mem_rawFrames member frameMember
        have facts := history.rawFrame_entryFacts capabilities _ frameRaw
        have env := Exec.Deriv.ParentPrefix.sevm_eq chain
        change m.sevm = frame.sevm at env
        have frameTarget : frame.sevm.currentTarget = P := by rw [← env]; exact same
        have family : UsdcContextCode frame.sevm.code := by
          rw [← env]
          rcases (previous m hm).2 same with ⟨code, _⟩ | ⟨e, he, code, _⟩
          · exact .inl code
          · rw [code]
            exact (impls e he).context
        rcases usdc_exec_kind facts.1 facts.2.2.1 (bal facts.2.1) chain family decoded with
          call | staticcall | ⟨rfl, proxyDel | implDel⟩
        · refine .inl ⟨?_, fun _ => ?_⟩
          · rw [childCode, Xinst.step_directCall_spawn_code (.inl call) spawn
              (by rw [← childTarget, target, proxyCode]; exact proxyFam.not_delegation),
              ← childTarget, target, proxyCode]
          · rw [← childSevm, Frame.enter_run_codeAddress enter,
              Xinst.step_callKind_spawn_codeAddress (.inl call) spawn
                (by rw [← childTarget, target, proxyCode]; exact proxy_undelegated),
              ← childTarget, target]
        · refine .inl ⟨?_, fun _ => ?_⟩
          · rw [childCode, Xinst.step_directCall_spawn_code (.inr staticcall) spawn
              (by rw [← childTarget, target, proxyCode]; exact proxyFam.not_delegation),
              ← childTarget, target, proxyCode]
          · rw [← childSevm, Frame.enter_run_codeAddress enter,
              Xinst.step_callKind_spawn_codeAddress (.inr staticcall) spawn
                (by rw [← childTarget, target, proxyCode]; exact proxy_undelegated),
              ← childTarget, target]
        · obtain ⟨g, w, rest, stack⟩ := Xinst.step_delegatecall_spawn_stack spawn
          obtain ⟨e, he, address, ready⟩ := (previous m hm).1
          have addr : w.toAdr = e.adr := by
            rw [proxyDel.2 g w rest stack]
            change (m.devm.getStorVal frame.sevm.currentTarget implSlot).toAdr = e.adr
            rw [frameTarget]
            exact address
          have actual : m.devm.getCode w.toAdr = e.code := by
            rw [addr]
            exact ready.1
          refine .inr ⟨e, he, ?_, libraryEarlier m hm ready.2⟩
          rw [childCode, Xinst.step_delegatecall_spawn_code spawn stack
            (by rw [actual]; exact (impls e he).context.not_delegation), actual]
        · obtain ⟨e, he, code, ready⟩ : ∃ e ∈ W, m.sevm.code = e.code ∧
            (e.code = Impl.code → m.devm.getCode usdcLib = Lib.code) := by
            rcases (previous m hm).2 same with ⟨code, _⟩ | entry
            · exact (proxy_ne_impl (code.symm.trans
                ((congrArg Sevm.code env).trans implDel.1))).elim
            · exact entry
          obtain ⟨l, hl, address, libCode⟩ := lib e he
            (code.symm.trans ((congrArg Sevm.code env).trans implDel.1))
          obtain ⟨g, w, rest, stack⟩ := Xinst.step_delegatecall_spawn_stack spawn
          have addr : w.toAdr = l.adr := by
            rw [implDel.2 g w rest stack, toAdr_toB256, address]
          have actual : m.devm.getCode w.toAdr = l.code := by
            rw [addr]
            rw [address]
            exact (ready (code.symm.trans ((congrArg Sevm.code env).trans implDel.1))).trans libCode.symm
          refine .inr ⟨l, hl, ?_, ?_⟩
          · rw [childCode, Xinst.step_delegatecall_spawn_code spawn stack
              (by rw [actual]; exact (impls l hl).context.not_delegation), actual]
          · intro implementation
            exact (lib_ne_impl (libCode.symm.trans implementation)).elim
      · have own := (Evm.step_spawn_child step enter).2.2
          (by rw [childSevm, target]; exact same)
          (by rw [childSevm, target, proxyCode]; exact proxyFam.ne_empty)
          (by rw [childSevm, target, proxyCode]; exact proxyFam.not_delegation)
        rw [childSevm, target] at own
        refine .inl ⟨own.trans proxyCode, fun _ => ?_⟩
        obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
        rw [← childSevm, Frame.enter_run_codeAddress enter,
          Xinst.step_spawn_codeAddress_eq_currentTarget spawn
            (by rw [← childTarget, target]; exact same)
            (by rw [← childTarget, target, proxyCode]; exact proxyFam.ne_empty)
            (by rw [← childTarget, target, proxyCode]; exact proxy_undelegated),
          ← childTarget, target]
  intro N retained
  obtain ⟨before, after, split⟩ := List.append_of_mem retained
  exact all before N after split

/-- Compatibility projection for a world already installed at root entry. -/
theorem ConfiguredHistoryTraceIn.retained_proxyWorld_context_with_entry
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {W : List UsdcDeployedEntry} {R : Exec.Deriv}
    (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) (rootOwn : RootOwnCode R)
    (proxy : R.devm.getCode P = Proxy.code)
    (installed : ∀ e ∈ W, R.devm.getCode e.adr = e.code)
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (slot : ∃ e ∈ W, ((R.devm.getStor P).get implSlot).toAdr = e.adr)
    (upgrades : ∀ N ∈ Exec.retainedNodes R.exc,
      N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
      (RootOwnEntry R → N.sevm.codeAddress = some P) →
      ∀ write : Exec.StorageWrite, Exec.Deriv.successfulSstore? N = some write →
      write.key = implSlot → ∃ e ∈ W, write.value.toAdr = e.adr)
    (apart : ∀ N ∈ Exec.retainedNodes R.exc, N.sevm.currentTarget = P →
      ∀ e ∈ W, N.sevm.code = e.code → ∀ write : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? N = some write → write.key ≠ implSlot) :
    ∀ N ∈ Exec.retainedNodes R.exc,
      (∃ e ∈ W, ((N.devm.getStor P).get implSlot).toAdr = e.adr) ∧
      (N.sevm.currentTarget = P →
        (N.sevm.code = Proxy.code ∧
          (RootOwnEntry R → N.sevm.codeAddress = some P)) ∨ ∃ e ∈ W, N.sevm.code = e.code) := by
  have installedAt (e : UsdcDeployedEntry) (he : e ∈ W) (N : Exec.Deriv)
      (retained : N ∈ Exec.retainedNodes R.exc) : N.devm.getCode e.adr = e.code :=
    Exec.rawNodes_getCode R.exc (installed e he) (impls e he).context.ne_nil N
      ((Exec.retainedNodes_sublist_rawNodes R.exc).subset retained)
  have initial : ∃ e ∈ W, ((R.devm.getStor P).get implSlot).toAdr = e.adr ∧
      e.RuntimeReady R.devm := by
    obtain ⟨e, he, address⟩ := slot
    refine ⟨e, he, address, installed e he, ?_⟩
    intro implementation
    obtain ⟨l, hl, address, code⟩ := lib e he implementation
    rw [← address, ← code]
    exact installed l hl
  have context := ConfiguredHistoryTraceIn.retained_proxyWorld_context_from_installations
    history capabilities bal member committed rootOwn proxy impls lib initial
    (by
      intro N retained target code own write found key
      obtain ⟨e, he, address⟩ := upgrades N retained target code own write found key
      refine ⟨e, he, address, installedAt e he N retained, ?_⟩
      intro implementation
      obtain ⟨l, hl, address, code⟩ := lib e he implementation
      rw [← address, ← code]
      exact installedAt l hl N retained) apart
  intro N retained
  obtain ⟨cell, execution⟩ := context N retained
  refine ⟨?_, ?_⟩
  · obtain ⟨e, he, address, _⟩ := cell
    exact ⟨e, he, address⟩
  · intro target
    rcases execution target with own | ⟨e, he, code, _⟩
    · exact .inl own
    · exact .inr ⟨e, he, code⟩

/-- Code and pointer projection of the retained induction. Its original signature
needs only root code provenance; code-address provenance is retained separately. -/
theorem ConfiguredHistoryTraceIn.retained_proxyWorld_context
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {W : List UsdcDeployedEntry} {R : Exec.Deriv}
    (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) (rootOwn : RootOwnCode R)
    (proxy : R.devm.getCode P = Proxy.code)
    (installed : ∀ e ∈ W, R.devm.getCode e.adr = e.code)
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (slot : ∃ e ∈ W, ((R.devm.getStor P).get implSlot).toAdr = e.adr)
    (upgrades : ∀ N ∈ Exec.retainedNodes R.exc,
      N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
      ∀ write : Exec.StorageWrite, Exec.Deriv.successfulSstore? N = some write →
      write.key = implSlot → ∃ e ∈ W, write.value.toAdr = e.adr)
    (apart : ∀ N ∈ Exec.retainedNodes R.exc, N.sevm.currentTarget = P →
      ∀ e ∈ W, N.sevm.code = e.code → ∀ write : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? N = some write → write.key ≠ implSlot) :
    ∀ N ∈ Exec.retainedNodes R.exc,
      (∃ e ∈ W, ((N.devm.getStor P).get implSlot).toAdr = e.adr) ∧
      (N.sevm.currentTarget = P →
        N.sevm.code = Proxy.code ∨ ∃ e ∈ W, N.sevm.code = e.code) := by
  have context := ConfiguredHistoryTraceIn.retained_proxyWorld_context_with_entry history
    capabilities bal member committed rootOwn proxy installed impls lib slot
    (by
      intro N retained target code _ write found key
      exact upgrades N retained target code write found key) apart
  intro N retained
  refine ⟨(context N retained).1, ?_⟩
  intro target
  rcases (context N retained).2 target with ⟨code, _⟩ | entry
  · exact .inl code
  · exact .inr entry

/-- Strictly earlier retained write exclusion supplies the implementation word used
to classify the current context. Known V1 separation remains an explicit local input. -/
theorem ConfiguredHistoryTraceIn.retained_proxyV1_context
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P I : Adr} {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) (rootOwn : RootOwnCode R)
    (proxy : R.devm.getCode P = Proxy.code) (impl : R.devm.getCode I = ImplV1.code)
    (slot : ((R.devm.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ¬ ∃ entry ∈ (Execution.committedPost R.exn committed).logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic])
    (v1Apart : ∀ N ∈ Exec.retainedNodes R.exc, N.sevm.currentTarget = P →
      N.sevm.code = ImplV1.code → ∀ write : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? N = some write → write.key ≠ implSlot) :
    ∀ N ∈ Exec.retainedNodes R.exc,
      (N.devm.getStor P).get implSlot = (R.devm.getStor P).get implSlot ∧
      (N.sevm.currentTarget = P → N.sevm.code = Proxy.code ∨ N.sevm.code = ImplV1.code) ∧
      ∀ write : Exec.StorageWrite, Exec.Deriv.successfulSstore? N = some write →
        write.owner = P → write.key ≠ implSlot := by
  let entry : UsdcDeployedEntry := ⟨I, ImplV1.code, R.devm.state, []⟩
  have context := ConfiguredHistoryTraceIn.retained_proxyWorld_context history capabilities bal
    (W := [entry]) member committed rootOwn proxy
    (by intro e he; obtain rfl := List.mem_singleton.mp he; exact impl)
    (by intro e he; obtain rfl := List.mem_singleton.mp he; exact .inl rfl)
    (by
      intro e he code
      obtain rfl := List.mem_singleton.mp he
      have sizes := congrArg ByteArray.size code
      exact ((by decide +kernel : ImplV1.code.size ≠ Impl.code.size) sizes).elim)
    ⟨entry, List.mem_singleton_self _, slot⟩
    (by
      intro N retained target code write found key
      exact (noUpgraded
        (ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded_of_proxyCode history
          capabilities bal member committed retained found
          ((successfulSstore?_node_owner found).2.trans target) key code)).elim)
    (by
      intro N retained target e he code write found
      obtain rfl := List.mem_singleton.mp he
      exact v1Apart N retained target code write found)
  have codes (N : Exec.Deriv) (retained : N ∈ Exec.retainedNodes R.exc)
      (target : N.sevm.currentTarget = P) :
      N.sevm.code = Proxy.code ∨ N.sevm.code = ImplV1.code := by
    rcases (context N retained).2 target with code | ⟨e, he, code⟩
    · exact .inl code
    · obtain rfl := List.mem_singleton.mp he
      exact .inr code
  have writes (N : Exec.Deriv) (retained : N ∈ Exec.retainedNodes R.exc)
      (write : Exec.StorageWrite) (found : Exec.Deriv.successfulSstore? N = some write)
      (own : write.owner = P) : write.key ≠ implSlot := by
    intro key
    have target : N.sevm.currentTarget = P :=
      (successfulSstore?_node_owner found).2.symm.trans own
    rcases codes N retained target with proxyCode | implCode
    · exact noUpgraded
        (ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded_of_proxyCode history
          capabilities bal member committed retained found own key proxyCode)
    · exact v1Apart N retained target implCode write found key
  intro N retained
  refine ⟨?_, codes N retained, writes N retained⟩
  obtain ⟨before, after, split⟩ := List.append_of_mem retained
  have nonempty : (R.devm.getCode P).toList ≠ [] := by
    rw [proxy]
    exact (show UsdcContextCode Proxy.code from .inl rfl).ne_nil
  rcases Exec.retainedNodes_cellProv_noStateGas R.exc committed implSlot
      (history.rawFrame_entryFacts capabilities R member).2.2.1 nonempty split with
    equal | ⟨b₁, b₂, m, write, equal, found, own, key, _⟩
  · exact equal
  · have hm : m ∈ Exec.retainedNodes R.exc := by
      rw [split, equal]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    exact (writes m hm write found own key).elim

/-- Actual complete-settlement outer roots supply their own-code and raw-entry
facts. The installed code, implementation word and known-V1 separation remain explicit. -/
theorem ConfiguredHistoryTraceIn.settledRoot_retained_proxyV1_context
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
      Exec.Deriv.successfulSstore? N = some write → write.key ≠ implSlot) :
    ∀ N ∈ Exec.retainedNodes R.run,
      (N.devm.getStor P).get implSlot = (R.pre.getStor P).get implSlot ∧
      (N.sevm.currentTarget = P → N.sevm.code = Proxy.code ∨ N.sevm.code = ImplV1.code) ∧
      ∀ write : Exec.StorageWrite, Exec.Deriv.successfulSstore? N = some write →
        write.owner = P → write.key ≠ implSlot := by
  exact ConfiguredHistoryTraceIn.retained_proxyV1_context history capabilities bal
    (R := Exec.Frame.rootDeriv R)
    (history.mem_rawFrames_of_mem_settledRoots R member) R.committed
    (history.settledRoots_rootOwnCode R member) proxy impl slot noUpgraded v1Apart

/-- The installed-world induction for an actual complete-settlement outer root.
Root membership supplies commitment, raw entry facts and own-code. Installation
at this root and retained upgrade-target membership remain explicit producers. -/
theorem ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_context
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
    (upgrades : ∀ N ∈ Exec.retainedNodes R.run,
      N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
      ∀ write : Exec.StorageWrite, Exec.Deriv.successfulSstore? N = some write →
      write.key = implSlot → ∃ e ∈ W, write.value.toAdr = e.adr)
    (apart : KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    ∀ N ∈ Exec.retainedNodes R.run,
      (∃ e ∈ W, ((N.devm.getStor P).get implSlot).toAdr = e.adr) ∧
      (N.sevm.currentTarget = P →
        N.sevm.code = Proxy.code ∨ ∃ e ∈ W, N.sevm.code = e.code) := by
  apply ConfiguredHistoryTraceIn.retained_proxyWorld_context history capabilities bal
    (R := Exec.Frame.rootDeriv R)
    (history.mem_rawFrames_of_mem_settledRoots R member) R.committed
    (history.settledRoots_rootOwnCode R member) proxy installed impls lib slot upgrades
  intro N retained target e he code write found
  exact apart N retained target (by rw [code]; exact impls e he) write found

/-- An actual settled outer root supplies the address provenance needed to
recognize retained proxy frames as token entries. Delegated implementation and
library contexts remain the other branch. -/
theorem ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_entry
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
    (upgrades : ∀ N ∈ Exec.retainedNodes R.run,
      N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
      N.sevm.codeAddress = some P →
      ∀ write : Exec.StorageWrite, Exec.Deriv.successfulSstore? N = some write →
      write.key = implSlot → ∃ e ∈ W, write.value.toAdr = e.adr)
    (apart : KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    ∀ N ∈ Exec.retainedNodes R.run,
      (∃ e ∈ W, ((N.devm.getStor P).get implSlot).toAdr = e.adr) ∧
      (N.sevm.currentTarget = P →
        (N.sevm.code = Proxy.code ∧ N.sevm.codeAddress = some P) ∨
          ∃ e ∈ W, N.sevm.code = e.code) := by
  have context := ConfiguredHistoryTraceIn.retained_proxyWorld_context_with_entry history
    capabilities bal (R := Exec.Frame.rootDeriv R)
    (history.mem_rawFrames_of_mem_settledRoots R member) R.committed
    (history.settledRoots_rootOwnCode R member) proxy installed impls lib slot
    (by
      intro N retained target code address write found key
      exact upgrades N retained target code
        (address (history.settledRoots_rootOwnEntry R member)) write found key)
    (by
      intro N retained target e he code write found
      exact apart N retained target (by rw [code]; exact impls e he) write found)
  intro N retained
  refine ⟨(context N retained).1, ?_⟩
  intro target
  rcases (context N retained).2 target with ⟨code, address⟩ | entry
  · exact .inl ⟨code, address (history.settledRoots_rootOwnEntry R member)⟩
  · exact .inr entry

/-- Consume approved F2′ in the coupled retained induction, using entry
provenance already derived at each earlier write. This local specialization
applies when the listed implementations are installed at the selected root;
it does not assert that future implementations were installed at earlier
roots, or exclude creation and upgrade in the same root. -/
theorem ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_of_f2prime
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
    (apart : KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    ∀ N ∈ Exec.retainedNodes R.run,
      (∃ e ∈ W, ((N.devm.getStor P).get implSlot).toAdr = e.adr) ∧
      (N.sevm.currentTarget = P →
        (N.sevm.code = Proxy.code ∧ N.sevm.codeAddress = some P) ∨
          ∃ e ∈ W, N.sevm.code = e.code) := by
  apply ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_entry history
    capabilities bal member proxy installed impls lib slot ?_ apart
  intro N retained target code address write found key
  have inTargets := ConfiguredHistoryTraceIn.retained_proxyUpgrade_target_of_f2prime
    history capabilities bal governance member retained target code address found key
  obtain ⟨e, he, adr⟩ := targets write.value.toAdr inTargets
  exact ⟨e, he, adr.symm⟩

/-- A changed endpoint implementation word comes from an actual retained proxy
write. Original F2′ and the source guard identify its literal target and code
existence at that write. The context classifier is a producer output; no
installation at root entry is assumed by this provenance lemma. -/
theorem ConfiguredHistoryTraceIn.settledRoot_implSlot_origin_of_f2prime
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {R : Exec.Frame} (member : R ∈ history.settledRoots)
    (proxy : R.pre.getCode P = Proxy.code)
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    (classified : ∀ N ∈ Exec.retainedNodes R.run, N.sevm.currentTarget = P →
      (N.sevm.code = Proxy.code ∧ N.sevm.codeAddress = some P) ∨
        UsdcImplCode N.sevm.code)
    (apart : KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    (R.post.getStor P).get implSlot = (R.pre.getStor P).get implSlot ∨
      ∃ N ∈ Exec.retainedNodes R.run, ∃ write : Exec.StorageWrite,
        Exec.Deriv.successfulSstore? N = some write ∧ write.owner = P ∧
        write.key = implSlot ∧ write.value = (R.post.getStor P).get implSlot ∧
        write.value.toAdr ∈ F2prime.upgradeTargets ∧
        (N.devm.getCode write.value.toAdr).toList ≠ [] := by
  by_cases unchanged : (R.post.getStor P).get implSlot = (R.pre.getStor P).get implSlot
  · exact .inl unchanged
  have rawRoot := history.mem_rawFrames_of_mem_settledRoots R member
  have hsg := (history.rawFrame_entryFacts capabilities _ rawRoot).2.2.1
  have nonempty : (R.pre.getCode P).toList ≠ [] := by
    rw [proxy]
    exact (show UsdcContextCode Proxy.code from .inl rfl).ne_nil
  obtain ⟨actual, _, owner, key, value, before, after, split, _⟩ :=
    Exec.exists_lastRetainedSstore_of_getStor_ne_noStateGas R.run R.committed hsg
      nonempty (Ne.symm unchanged)
  have present : actual.storageWrite ∈ Exec.retainedStorageWrites R.run := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨N, retained, found⟩ := List.mem_filterMap.mp present
  have target : N.sevm.currentTarget = P :=
    (successfulSstore?_node_owner found).2.symm.trans owner
  rcases classified N retained target with ⟨code, address⟩ | implementation
  · have allowed := ConfiguredHistoryTraceIn.retained_proxyUpgrade_target_of_f2prime_with_code
      history capabilities bal governance member retained target code address found key
    exact .inr ⟨N, retained, actual.storageWrite, found, owner, key, value, allowed⟩
  · exact (apart N retained target implementation actual.storageWrite found key).elim

/-- Endpoint write provenance with its context obligation discharged by the
existing installed-world induction. This consumer retains that induction's
explicit entry-installation condition; the provenance core is also usable
with a dynamic classifier once its historical producers are supplied. -/
theorem ConfiguredHistoryTraceIn.settledRoot_proxyWorld_implSlot_origin_of_f2prime
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
    (apart : KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    (R.post.getStor P).get implSlot = (R.pre.getStor P).get implSlot ∨
      ∃ N ∈ Exec.retainedNodes R.run, ∃ write : Exec.StorageWrite,
        Exec.Deriv.successfulSstore? N = some write ∧ write.owner = P ∧
        write.key = implSlot ∧ write.value = (R.post.getStor P).get implSlot ∧
        write.value.toAdr ∈ F2prime.upgradeTargets ∧
        (N.devm.getCode write.value.toAdr).toList ≠ [] := by
  have context := ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_of_f2prime
    history capabilities bal member proxy installed impls lib slot governance targets apart
  apply ConfiguredHistoryTraceIn.settledRoot_implSlot_origin_of_f2prime history capabilities
    bal member proxy governance ?_ apart
  intro N retained target
  rcases (context N retained).2 target with own | ⟨e, he, code⟩
  · exact .inl own
  · exact .inr (code ▸ impls e he)

/-- The final implementation target keeps the exact nonempty code observed at
its retained upgrade write, including when creation occurred earlier in this
same root. This is the committed execution endpoint, before outer transaction
settlement; runtime identity remains an installation-provenance obligation. -/
theorem ConfiguredHistoryTraceIn.settledRoot_implSlot_origin_code_of_f2prime
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {R : Exec.Frame} (member : R ∈ history.settledRoots)
    (proxy : R.pre.getCode P = Proxy.code)
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    (classified : ∀ N ∈ Exec.retainedNodes R.run, N.sevm.currentTarget = P →
      (N.sevm.code = Proxy.code ∧ N.sevm.codeAddress = some P) ∨
        UsdcImplCode N.sevm.code)
    (apart : KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    (R.post.getStor P).get implSlot = (R.pre.getStor P).get implSlot ∨
      ∃ N ∈ Exec.retainedNodes R.run, ∃ write : Exec.StorageWrite,
        Exec.Deriv.successfulSstore? N = some write ∧ write.owner = P ∧
        write.key = implSlot ∧ write.value = (R.post.getStor P).get implSlot ∧
        write.value.toAdr ∈ F2prime.upgradeTargets ∧
        (N.devm.getCode write.value.toAdr).toList ≠ [] ∧
        R.post.getCode write.value.toAdr = N.devm.getCode write.value.toAdr := by
  rcases ConfiguredHistoryTraceIn.settledRoot_implSlot_origin_of_f2prime history
      capabilities bal member proxy governance classified apart with unchanged |
      ⟨N, retained, write, found, owner, key, value, allowed, nonempty⟩
  · exact .inl unchanged
  · obtain ⟨before, after, split⟩ := List.append_of_mem retained
    have rawRoot := history.mem_rawFrames_of_mem_settledRoots R member
    have hsg := (history.rawFrame_entryFacts capabilities _ rawRoot).2.2.1
    have preserved := (Exec.retainedNodes_code_after_split_noStateGas
      R.run R.committed hsg split nonempty).1
    exact .inr ⟨N, retained, write, found, owner, key, value, allowed, nonempty, preserved⟩

/-- A root entered with a nonempty active implementation ends with a nonempty
active implementation. Changed targets use the actual retained guard and code
transport, rather than installation of every future implementation at entry. -/
theorem ConfiguredHistoryTraceIn.settledRoot_implSlot_nonempty_of_f2prime
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {R : Exec.Frame} (member : R ∈ history.settledRoots)
    (proxy : R.pre.getCode P = Proxy.code)
    (active : (R.pre.getCode ((R.pre.getStor P).get implSlot).toAdr).toList ≠ [])
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    (classified : ∀ N ∈ Exec.retainedNodes R.run, N.sevm.currentTarget = P →
      (N.sevm.code = Proxy.code ∧ N.sevm.codeAddress = some P) ∨
        UsdcImplCode N.sevm.code)
    (apart : KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    (R.post.getCode ((R.post.getStor P).get implSlot).toAdr).toList ≠ [] := by
  rcases ConfiguredHistoryTraceIn.settledRoot_implSlot_origin_code_of_f2prime history
      capabilities bal member proxy governance classified apart with unchanged |
      ⟨N, _, write, _, _, _, value, _, nonempty, preserved⟩
  · rw [unchanged]
    have kept : R.post.getCode ((R.pre.getStor P).get implSlot).toAdr =
        R.pre.getCode ((R.pre.getStor P).get implSlot).toAdr := by
      have code := Exec.preserves_getCode R.run _ active
      unfold Exec.Frame.post Execution.committedPost
      split
      next outEq _ =>
        simpa only [outEq, Execution.getCode] using code
      next outEq _ =>
        have committed := R.committed
        simp only [outEq, Execution.commits, Bool.false_eq_true] at committed
    rw [kept]
    exact active
  · rw [← value, preserved]
    exact nonempty

/-- Original F2′ and the proxy guard select the exact upgrade positions at
which runtime installation evidence is needed. The coupled induction derives
classification; it is not supplied as a hypothesis. Creation earlier in this
root is allowed for both the implementation and its V2.2 library. -/
theorem ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_from_installations
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {W : List UsdcDeployedEntry} {R : Exec.Frame}
    (member : R ∈ history.settledRoots)
    (proxy : R.pre.getCode P = Proxy.code)
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (slot : ∃ e ∈ W, ((R.pre.getStor P).get implSlot).toAdr = e.adr ∧
      e.RuntimeReady R.pre)
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    (installations : ∀ N ∈ Exec.retainedNodes R.run,
      N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
      N.sevm.codeAddress = some P → ∀ write : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? N = some write → write.key = implSlot →
      write.value.toAdr ∈ F2prime.upgradeTargets →
      (N.devm.getCode write.value.toAdr).toList ≠ [] →
      ∃ e ∈ W, write.value.toAdr = e.adr ∧ e.RuntimeReady N.devm)
    (apart : KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    ∀ N ∈ Exec.retainedNodes R.run,
      (∃ e ∈ W, ((N.devm.getStor P).get implSlot).toAdr = e.adr ∧ e.RuntimeReady N.devm) ∧
      (N.sevm.currentTarget = P →
        (N.sevm.code = Proxy.code ∧ N.sevm.codeAddress = some P) ∨
          ∃ e ∈ W, N.sevm.code = e.code ∧
            (e.code = Impl.code → N.devm.getCode usdcLib = Lib.code)) := by
  have context := ConfiguredHistoryTraceIn.retained_proxyWorld_context_from_installations
    history capabilities bal (R := Exec.Frame.rootDeriv R)
    (history.mem_rawFrames_of_mem_settledRoots R member) R.committed
    (history.settledRoots_rootOwnCode R member) proxy impls lib slot
    (by
      intro N retained target code address write found key
      have own := address (history.settledRoots_rootOwnEntry R member)
      have allowed := ConfiguredHistoryTraceIn.retained_proxyUpgrade_target_of_f2prime_with_code
        history capabilities bal governance member retained target code own found key
      exact installations N retained target code own write found key allowed.1 allowed.2)
    (by
      intro N retained target e he code write found
      exact apart N retained target (by rw [code]; exact impls e he) write found)
  intro N retained
  refine ⟨(context N retained).1, ?_⟩
  intro target
  rcases (context N retained).2 target with ⟨code, address⟩ | entry
  · exact .inl ⟨code, address (history.settledRoots_rootOwnEntry R member)⟩
  · exact .inr entry

/-- Discharge the endpoint provenance classifier with the dynamic retained
induction. Only initial selected-code readiness and actual upgrade-position
runtime evidence are supplied, not installation of all entries at root entry.
Historical installation evidence itself remains a separate producer duty. -/
theorem ConfiguredHistoryTraceIn.settledRoot_dynamic_implSlot_origin_code_of_f2prime
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {P : Adr} {W : List UsdcDeployedEntry} {R : Exec.Frame}
    (member : R ∈ history.settledRoots)
    (proxy : R.pre.getCode P = Proxy.code)
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (slot : ∃ e ∈ W, ((R.pre.getStor P).get implSlot).toAdr = e.adr ∧
      e.RuntimeReady R.pre)
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    (installations : ∀ N ∈ Exec.retainedNodes R.run,
      N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
      N.sevm.codeAddress = some P → ∀ write : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? N = some write → write.key = implSlot →
      write.value.toAdr ∈ F2prime.upgradeTargets →
      (N.devm.getCode write.value.toAdr).toList ≠ [] →
      ∃ e ∈ W, write.value.toAdr = e.adr ∧ e.RuntimeReady N.devm)
    (apart : KnownImplSlotApart P (Exec.retainedNodes R.run)) :
    (R.post.getStor P).get implSlot = (R.pre.getStor P).get implSlot ∨
      ∃ N ∈ Exec.retainedNodes R.run, ∃ write : Exec.StorageWrite,
        Exec.Deriv.successfulSstore? N = some write ∧ write.owner = P ∧
        write.key = implSlot ∧ write.value = (R.post.getStor P).get implSlot ∧
        write.value.toAdr ∈ F2prime.upgradeTargets ∧
        (N.devm.getCode write.value.toAdr).toList ≠ [] ∧
        R.post.getCode write.value.toAdr = N.devm.getCode write.value.toAdr := by
  have context := ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_from_installations
    history capabilities bal member proxy impls lib slot governance installations apart
  apply ConfiguredHistoryTraceIn.settledRoot_implSlot_origin_code_of_f2prime history
    capabilities bal member proxy governance ?_ apart
  intro N retained target
  rcases (context N retained).2 target with own | ⟨e, he, code, _⟩
  · exact .inl own
  · exact .inr (code ▸ impls e he)

end Blanc.Lift.Usdc
