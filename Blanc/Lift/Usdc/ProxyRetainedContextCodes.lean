import Blanc.ExecutionRetainedNodeOrigin
import Blanc.ExecutionInRootOwnCode
import Blanc.Lift.Usdc.ProxyCommittedUpgradeLog

/-! Coupled Proxy/V1 context and implementation-slot exclusion within one retained root. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

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
  have proxyFam : UsdcContextCode Proxy.code := .inl rfl
  have implFam : UsdcContextCode ImplV1.code := .inr (.inl rfl)
  have nonempty : (R.devm.getCode P).toList ≠ [] := by
    rw [proxy]
    exact proxyFam.ne_nil
  have rootHsg := (history.rawFrame_entryFacts capabilities R member).2.2.1
  have installedP (N : Exec.Deriv) (retained : N ∈ Exec.retainedNodes R.exc) :=
    Exec.rawNodes_getCode R.exc proxy proxyFam.ne_nil N
      ((Exec.retainedNodes_sublist_rawNodes R.exc).subset retained)
  have installedI (N : Exec.Deriv) (retained : N ∈ Exec.retainedNodes R.exc) :=
    Exec.rawNodes_getCode R.exc impl implFam.ne_nil N
      ((Exec.retainedNodes_sublist_rawNodes R.exc).subset retained)
  have all : ∀ before N after, Exec.retainedNodes R.exc = before ++ N :: after →
      (N.devm.getStor P).get implSlot = (R.devm.getStor P).get implSlot ∧
      (N.sevm.currentTarget = P → N.sevm.code = Proxy.code ∨ N.sevm.code = ImplV1.code) ∧
      ∀ write : Exec.StorageWrite, Exec.Deriv.successfulSstore? N = some write →
        write.owner = P → write.key ≠ implSlot := by
    refine List.forall_split_of_positional fun before N after split earlier => ?_
    have retained : N ∈ Exec.retainedNodes R.exc := by
      rw [split]
      exact List.mem_append_right _ List.mem_cons_self
    have previous (m : Exec.Deriv) (hm : m ∈ before) :
        (m.devm.getStor P).get implSlot = (R.devm.getStor P).get implSlot ∧
        (m.sevm.currentTarget = P → m.sevm.code = Proxy.code ∨ m.sevm.code = ImplV1.code) ∧
        ∀ write : Exec.StorageWrite, Exec.Deriv.successfulSstore? m = some write →
          write.owner = P → write.key ≠ implSlot := by
      obtain ⟨b₁, b₂, equal⟩ := List.append_of_mem hm
      exact earlier b₁ m b₂ equal
    have cell : (N.devm.getStor P).get implSlot = (R.devm.getStor P).get implSlot := by
      have prov := Exec.retainedNodes_cellProv_noStateGas R.exc committed implSlot
        rootHsg nonempty split
      rcases prov with equal | ⟨b₁, b₂, m, write, equal, found, own, key, _⟩
      · exact equal
      · have hm : m ∈ before := by
          rw [equal]
          exact List.mem_append_right _ List.mem_cons_self
        exact ((previous m hm).2.2 write found own key).elim
    have codes : N.sevm.currentTarget = P →
        N.sevm.code = Proxy.code ∨ N.sevm.code = ImplV1.code := by
      intro target
      rcases Exec.retainedNodes_split_origin R.exc committed split with
        ⟨_, root⟩ | ⟨m, hm, same⟩ | ⟨m, hm, spawned⟩
      · change N = R at root
        subst N
        have notDelegation : ¬ isValidDelegation (R.devm.getCode P) := by
          rw [proxy]
          exact proxyFam.not_delegation
        exact .inl ((rootOwn P target nonempty notDelegation).trans proxy)
      · rw [← same] at target ⊢
        exact (previous m hm).2.1 target
      · have mRetained : m ∈ Exec.retainedNodes R.exc := by
          rw [split]
          exact List.mem_append_left _ hm
        have proxyCode := installedP m mRetained
        have implCode := installedI m mRetained
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
          have kind : x = .call ∨ x = .staticcall ∨
              (x = .delegatecall ∧ ∀ (g w : B256) (rest : List B256),
                m.devm.stack = g :: w :: rest → w = m.devm.getStorVal P implSlot) := by
            rcases (previous m hm).2.1 same with proxyParent | implParent
            · rw [env] at proxyParent
              rcases usdc_exec_kind facts.1 facts.2.2.1 (bal facts.2.1) chain
                (.inl proxyParent) decoded with call | staticcall | ⟨del, proxyDel | implDel⟩
              · exact .inl call
              · exact .inr (.inl staticcall)
              · refine .inr (.inr ⟨del, ?_⟩)
                intro g w rest stack
                rw [← frameTarget]
                exact proxyDel.2 g w rest stack
              · exact (proxy_ne_impl (proxyParent.symm.trans implDel.1)).elim
            · rw [env] at implParent
              have direct := call_or_staticcall_of_parentPrefix_noStateGas
                ImplV1.cert_check ImplV1.cert_callOnly (F := Exec.Frame.rootDeriv frame)
                facts.1 implParent facts.2.2.1 chain decoded
              exact direct.elim Or.inl (fun h => .inr (.inl h))
          rcases kind with call | staticcall | ⟨rfl, operand⟩
          · exact .inl (by
              rw [childCode, Xinst.step_directCall_spawn_code (.inl call) spawn
                (by rw [← childTarget, target, proxyCode]; exact proxyFam.not_delegation),
                ← childTarget, target, proxyCode])
          · exact .inl (by
              rw [childCode, Xinst.step_directCall_spawn_code (.inr staticcall) spawn
                (by rw [← childTarget, target, proxyCode]; exact proxyFam.not_delegation),
                ← childTarget, target, proxyCode])
          · obtain ⟨g, w, rest, stack⟩ := Xinst.step_delegatecall_spawn_stack spawn
            have address : w.toAdr = I := by
              rw [operand g w rest stack]
              change ((m.devm.getStor P).get implSlot).toAdr = I
              rw [(previous m hm).1]
              exact slot
            have actual : m.devm.getCode w.toAdr = ImplV1.code := by
              rw [address]
              exact implCode
            exact .inr (by
              rw [childCode, Xinst.step_delegatecall_spawn_code spawn stack
                (by rw [actual]; exact implFam.not_delegation), actual])
        · have own := (Evm.step_spawn_child step enter).2.2
            (by rw [childSevm, target]; exact same)
            (by rw [childSevm, target, proxyCode]; exact proxyFam.ne_empty)
            (by rw [childSevm, target, proxyCode]; exact proxyFam.not_delegation)
          rw [childSevm, target] at own
          exact .inl (own.trans proxyCode)
    refine ⟨cell, codes, ?_⟩
    intro write found own key
    have target : N.sevm.currentTarget = P :=
      (successfulSstore?_node_owner found).2.symm.trans own
    rcases codes target with proxyCode | implCode
    · exact noUpgraded
        (ConfiguredHistoryTraceIn.retained_implSstore_emitsUpgraded_of_proxyCode history
          capabilities bal member committed retained found own key proxyCode)
    · exact v1Apart N retained target implCode write found key
  intro N retained
  obtain ⟨before, after, split⟩ := List.append_of_mem retained
  exact all before N after split

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

end Blanc.Lift.Usdc
