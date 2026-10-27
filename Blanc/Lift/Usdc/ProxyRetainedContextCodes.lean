import Blanc.ExecutionRetainedNodeOrigin
import Blanc.ExecutionInRootOwnCode
import Blanc.Lift.Usdc.ProxyCommittedUpgradeLog
import Blanc.Lift.Usdc.GovernanceHistory

/-! Coupled USDC context and implementation-pointer induction within one retained root. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Coupled implementation-pointer and code-family induction on the actual
retained chronology of one committing root. Every available entry is installed
at this root's entry; installation at earlier history boundaries is a separate
producer duty. Only retained proxy writes are constrained. Discarded subtrees
need neither governance restrictions nor code-family classification. -/
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
  have proxyFam : UsdcContextCode Proxy.code := .inl rfl
  have nonempty : (R.devm.getCode P).toList ≠ [] := by
    rw [proxy]
    exact proxyFam.ne_nil
  have rootHsg := (history.rawFrame_entryFacts capabilities R member).2.2.1
  have installedP (N : Exec.Deriv) (retained : N ∈ Exec.retainedNodes R.exc) :=
    Exec.rawNodes_getCode R.exc proxy proxyFam.ne_nil N
      ((Exec.retainedNodes_sublist_rawNodes R.exc).subset retained)
  have installedE (e : UsdcDeployedEntry) (he : e ∈ W)
      (N : Exec.Deriv) (retained : N ∈ Exec.retainedNodes R.exc) :=
    Exec.rawNodes_getCode R.exc (installed e he) (impls e he).context.ne_nil N
      ((Exec.retainedNodes_sublist_rawNodes R.exc).subset retained)
  have all : ∀ before N after, Exec.retainedNodes R.exc = before ++ N :: after →
      (∃ e ∈ W, ((N.devm.getStor P).get implSlot).toAdr = e.adr) ∧
      (N.sevm.currentTarget = P →
        (N.sevm.code = Proxy.code ∧
          (RootOwnEntry R → N.sevm.codeAddress = some P)) ∨ ∃ e ∈ W, N.sevm.code = e.code) := by
    refine List.forall_split_of_positional fun before N after split earlier => ?_
    have retained : N ∈ Exec.retainedNodes R.exc := by
      rw [split]
      exact List.mem_append_right _ List.mem_cons_self
    have previous (m : Exec.Deriv) (hm : m ∈ before) :
        (∃ e ∈ W, ((m.devm.getStor P).get implSlot).toAdr = e.adr) ∧
        (m.sevm.currentTarget = P →
          (m.sevm.code = Proxy.code ∧
          (RootOwnEntry R → m.sevm.codeAddress = some P)) ∨ ∃ e ∈ W, m.sevm.code = e.code) := by
      obtain ⟨b₁, b₂, equal⟩ := List.append_of_mem hm
      exact earlier b₁ m b₂ equal
    have priorRetained (m : Exec.Deriv) (hm : m ∈ before) :
        m ∈ Exec.retainedNodes R.exc := by
      rw [split]
      exact List.mem_append_left _ hm
    have cell : ∃ e ∈ W, ((N.devm.getStor P).get implSlot).toAdr = e.adr := by
      rcases Exec.retainedNodes_cellProv_noStateGas R.exc committed implSlot
          rootHsg nonempty split with equal | ⟨b₁, b₂, m, write, equal, found, own, key, value⟩
      · rw [equal]
        exact slot
      · have hm : m ∈ before := by
          rw [equal]
          exact List.mem_append_right _ List.mem_cons_self
        have target : m.sevm.currentTarget = P :=
          (successfulSstore?_node_owner found).2.symm.trans own
        rcases (previous m hm).2 target with ⟨proxyCode, address⟩ | ⟨e, he, code⟩
        · rw [← value]
          exact upgrades m (priorRetained m hm) target proxyCode address write found key
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
      exact (previous m hm).2 target
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
          rcases (previous m hm).2 same with ⟨code, _⟩ | ⟨e, he, code⟩
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
          obtain ⟨e, he, address⟩ := (previous m hm).1
          have addr : w.toAdr = e.adr := by
            rw [proxyDel.2 g w rest stack]
            change (m.devm.getStorVal frame.sevm.currentTarget implSlot).toAdr = e.adr
            rw [frameTarget]
            exact address
          have actual : m.devm.getCode w.toAdr = e.code := by
            rw [addr]
            exact installedE e he m mRetained
          refine .inr ⟨e, he, ?_⟩
          rw [childCode, Xinst.step_delegatecall_spawn_code spawn stack
            (by rw [actual]; exact (impls e he).context.not_delegation), actual]
        · obtain ⟨e, he, code⟩ : ∃ e ∈ W, m.sevm.code = e.code := by
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
            exact installedE l hl m mRetained
          refine .inr ⟨l, hl, ?_⟩
          rw [childCode, Xinst.step_delegatecall_spawn_code spawn stack
            (by rw [actual]; exact (impls l hl).context.not_delegation), actual]
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

end Blanc.Lift.Usdc
