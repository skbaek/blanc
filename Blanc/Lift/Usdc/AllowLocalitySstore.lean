import Blanc.Lift.Usdc.AllowLocalityHistory
import Blanc.Lift.WriteSiteReachHistory
import Blanc.ExecutionTraceRootFrame

/-!
# Allowance locality at the attributed history `SSTORE`

`allow_class_of_wsObs` is `allow_locality` at one `SSTORE` step: an `SSTORE` meeting a root
site of a checked site list, at a tracked allowance row of the Pair, is non-increasing or in an
allowed frame (`SProg.RunP.point` applied to `allow_locality`).

The `ConfiguredHistoryTraceIn.retainedSstore_implV*_allowClass` theorems apply it, through the
prefix soundness of the write-site checker (`exists_retainedSstore_frame_wsObs`), to the last
retained `SSTORE` that `exists_retainedSstore_frame_sstoreCursor` attributes to a committed raw
frame: when that frame runs implementation V1, V2, V2_1 or V2_2 and its root sites satisfy the
frame-local `RowSep`, a write at a tracked Pair allowance row has a value no greater than the
row's word at the write's node, or its frame is one of the exceptions of the matching
`implV*_allowLocality_rawFrame` law (the selector-observed reading: V1 caller or initializer;
V2 and V2_1 caller, initializer, or the native owner answer `OldUsdcNativePairAnswer`; V2_2
caller, initializer, or calldata word 4 for its owner selectors).  The V2 and V2_1 forms take
the same `bal` and address-1 `nodeleg` premises as their `_rawFrame` laws.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

/-- **The allowance law at one `SSTORE`.** -/
theorem allow_class_of_wsObs {t : SelTable} {pair : Adr} {Tr : Adr → Prop} {sites : List Site}
    {ε : Env} (hsel : t.selT.known = true) (hok : sites.all (allowSiteOk t) = true)
    (sep : RowSep 10 pair.toB256 (AllowKey Tr) sites ε) {sevm : Sevm} {d : Devm}
    (obs : WsObs sites ε sevm d (.reg .sstore)) {x v : B256} {rest : List B256}
    (stack : d.stack = x :: v :: rest) (tracked : ∃ g, Tr g ∧ allowSlot pair g = x) :
    AllowedFrame t pair ε ∨ v.toNat ≤ (d.getStorVal sevm.currentTarget x).toNat :=
  (SProg.RunP.point (P := WsStep sites ε fun _ _ _ _ => True) (d' := d)
    (fun r => allow_locality hsel hok sep r) ⟨trivial, obs⟩).2 rfl x v rest stack tracked


section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {pair : Adr} {Tr : Adr → Prop}

/-- **V1 at the attributed write.** -/
theorem ConfiguredHistoryTraceIn.retainedSstore_implV1_allowClass
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) {owner : Adr} {key : B256}
    (hcode : (R.devm.getCode owner).toList ≠ [])
    (changed : (Devm.getStor R.devm owner).get key ≠
      (Devm.getStor (Execution.committedPost R.exn committed) owner).get key) :
    ∃ (write : Exec.SuccessfulSstoreOccurrence R) (frame : Exec.Frame),
      write.Retained ∧ write.storageOwner = owner ∧ write.key = key ∧
      write.value = (Devm.getStor (Execution.committedPost R.exn committed) owner).get key ∧
      write.IsLastRetained ∧
      frame ∈ Exec.committedFrames R.exc ∧
      Blanc.Exec.Frame.rootDeriv frame ∈ history.rawFrames ∧
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv frame) write.occurrence.node ∧
      frame.sevm.currentTarget = owner ∧
      (frame.sevm.code = ImplV1.code →
        RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV1Ws.implWsAnn)
          (WriteSite.Env.root frame.sevm) →
        (∃ g, Tr g ∧ allowSlot pair g = key) →
        ((selV1T.eval (WriteSite.Env.root frame.sevm) ∈ selV1.callers ∧
            frame.sevm.caller = pair) ∨
          selV1T.eval (WriteSite.Env.root frame.sevm) ∈ selV1.inits) ∨
        write.value.toNat ≤ (write.occurrence.node.devm.getStorVal owner key).toNat) := by
  obtain ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, ⟨rest, stack⟩, obs⟩ :=
    history.exists_retainedSstore_frame_wsObs capabilities member committed hcode changed
  refine ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, fun code sep tracked => ?_⟩
  rw [← keyEq] at tracked ⊢
  rw [← target]
  rcases allow_class_of_wsObs (by decide) implV1_allowSitesOk sep
      (obs ImplV1.cert_check implV1_wsCert code) stack tracked with allowed | nonInc
  · rcases allowed with ⟨caller, callerEq⟩ | ⟨owner, -⟩ | initializer
    · exact Or.inl (Or.inl ⟨caller, by
        simpa only [WriteSite.Env.root, toAdr_toB256] using callerEq⟩)
    · exact (List.not_mem_nil owner).elim
    · exact Or.inl (Or.inr initializer)
  · exact Or.inr nonInc

/-- **V2 at the attributed write.** -/
theorem ConfiguredHistoryTraceIn.retainedSstore_implV2_allowClass
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) {owner : Adr} {key : B256}
    (hcode : (R.devm.getCode owner).toList ≠ [])
    (changed : (Devm.getStor R.devm owner).get key ≠
      (Devm.getStor (Execution.committedPost R.exn committed) owner).get key) :
    ∃ (write : Exec.SuccessfulSstoreOccurrence R) (frame : Exec.Frame),
      write.Retained ∧ write.storageOwner = owner ∧ write.key = key ∧
      write.value = (Devm.getStor (Execution.committedPost R.exn committed) owner).get key ∧
      write.IsLastRetained ∧
      frame ∈ Exec.committedFrames R.exc ∧
      Blanc.Exec.Frame.rootDeriv frame ∈ history.rawFrames ∧
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv frame) write.occurrence.node ∧
      frame.sevm.currentTarget = owner ∧
      (frame.sevm.code = ImplV2.code →
        getDelegatedCodeAddress (frame.pre.getCode 1) = none →
        RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2Ws.implWsAnn)
          (WriteSite.Env.root frame.sevm) →
        (∃ g, Tr g ∧ allowSlot pair g = key) →
        ((Sevm.selector frame.sevm ∈ selV2.callers ∧ frame.sevm.caller = pair) ∨
          Sevm.selector frame.sevm ∈ selV2.inits ∨
          OldUsdcNativePairAnswer (Blanc.Exec.Frame.rootDeriv frame) pair) ∨
        write.value.toNat ≤ (write.occurrence.node.devm.getStorVal owner key).toNat) := by
  obtain ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, ⟨rest, stack⟩, obs⟩ :=
    history.exists_retainedSstore_frame_wsObs capabilities member committed hcode changed
  refine ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, fun code nodeleg sep tracked => ?_⟩
  obtain ⟨pc, inF, hsg, ⟨fresh, empty⟩, -⟩ :=
    history.rawFrame_entryFacts capabilities _ frameRaw
  obtain ⟨post, success⟩ := frame.exists_ok
  rw [← keyEq] at tracked ⊢
  rw [← target]
  rcases allow_class_of_wsObs (by decide) implV2_allowSitesOk sep
      (obs ImplV2.cert_check implV2_wsCert code) stack tracked with allowed | nonInc
  · rcases allowedFrame_selV2T rfl allowed with caller | initializer | ⟨owner, ownerEq⟩
    · exact Or.inl (Or.inl caller)
    · exact Or.inl (Or.inr (Or.inl initializer))
    · exact Or.inl (Or.inr (Or.inr (old_owner_pair_native (F := Blanc.Exec.Frame.rootDeriv frame)
        pc fresh empty (Or.inl ⟨code, owner⟩) nodeleg success ⟨hsg, bal inF⟩ ownerEq)))
  · exact Or.inr nonInc

/-- **V2_1 at the attributed write.** -/
theorem ConfiguredHistoryTraceIn.retainedSstore_implV2_1_allowClass
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) {owner : Adr} {key : B256}
    (hcode : (R.devm.getCode owner).toList ≠ [])
    (changed : (Devm.getStor R.devm owner).get key ≠
      (Devm.getStor (Execution.committedPost R.exn committed) owner).get key) :
    ∃ (write : Exec.SuccessfulSstoreOccurrence R) (frame : Exec.Frame),
      write.Retained ∧ write.storageOwner = owner ∧ write.key = key ∧
      write.value = (Devm.getStor (Execution.committedPost R.exn committed) owner).get key ∧
      write.IsLastRetained ∧
      frame ∈ Exec.committedFrames R.exc ∧
      Blanc.Exec.Frame.rootDeriv frame ∈ history.rawFrames ∧
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv frame) write.occurrence.node ∧
      frame.sevm.currentTarget = owner ∧
      (frame.sevm.code = ImplV2_1.code →
        getDelegatedCodeAddress (frame.pre.getCode 1) = none →
        RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplV2_1Ws.implWsAnn)
          (WriteSite.Env.root frame.sevm) →
        (∃ g, Tr g ∧ allowSlot pair g = key) →
        ((Sevm.selector frame.sevm ∈ selV2_1.callers ∧ frame.sevm.caller = pair) ∨
          Sevm.selector frame.sevm ∈ selV2_1.inits ∨
          OldUsdcNativePairAnswer (Blanc.Exec.Frame.rootDeriv frame) pair) ∨
        write.value.toNat ≤ (write.occurrence.node.devm.getStorVal owner key).toNat) := by
  obtain ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, ⟨rest, stack⟩, obs⟩ :=
    history.exists_retainedSstore_frame_wsObs capabilities member committed hcode changed
  refine ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, fun code nodeleg sep tracked => ?_⟩
  obtain ⟨pc, inF, hsg, ⟨fresh, empty⟩, -⟩ :=
    history.rawFrame_entryFacts capabilities _ frameRaw
  obtain ⟨post, success⟩ := frame.exists_ok
  rw [← keyEq] at tracked ⊢
  rw [← target]
  rcases allow_class_of_wsObs (by decide) implV2_1_allowSitesOk sep
      (obs ImplV2_1.cert_check implV2_1_wsCert code) stack tracked with allowed | nonInc
  · rcases allowedFrame_selV2T rfl allowed with caller | initializer | ⟨owner, ownerEq⟩
    · exact Or.inl (Or.inl caller)
    · exact Or.inl (Or.inr (Or.inl initializer))
    · exact Or.inl (Or.inr (Or.inr (old_owner_pair_native (F := Blanc.Exec.Frame.rootDeriv frame)
        pc fresh empty (Or.inr ⟨code, owner⟩) nodeleg success ⟨hsg, bal inF⟩ ownerEq)))
  · exact Or.inr nonInc

/-- **V2_2 at the attributed write.** -/
theorem ConfiguredHistoryTraceIn.retainedSstore_implV2_2_allowClass
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames)
    (committed : Execution.commits R.exn = true) {owner : Adr} {key : B256}
    (hcode : (R.devm.getCode owner).toList ≠ [])
    (changed : (Devm.getStor R.devm owner).get key ≠
      (Devm.getStor (Execution.committedPost R.exn committed) owner).get key) :
    ∃ (write : Exec.SuccessfulSstoreOccurrence R) (frame : Exec.Frame),
      write.Retained ∧ write.storageOwner = owner ∧ write.key = key ∧
      write.value = (Devm.getStor (Execution.committedPost R.exn committed) owner).get key ∧
      write.IsLastRetained ∧
      frame ∈ Exec.committedFrames R.exc ∧
      Blanc.Exec.Frame.rootDeriv frame ∈ history.rawFrames ∧
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv frame) write.occurrence.node ∧
      frame.sevm.currentTarget = owner ∧
      (frame.sevm.code = Impl.code →
        RowSep 10 pair.toB256 (AllowKey Tr) (wsRoot ImplWs.implWsAnn)
          (WriteSite.Env.root frame.sevm) →
        (∃ g, Tr g ∧ allowSlot pair g = key) →
        ((Sevm.selector frame.sevm ∈ selV2_2.callers ∧ frame.sevm.caller = pair) ∨
          Sevm.selector frame.sevm ∈ selV2_2.inits ∨
          (Sevm.selector frame.sevm ∈ selV2_2.owners ∧
            (Sevm.dataWord frame.sevm 4).toAdr = pair)) ∨
        write.value.toNat ≤ (write.occurrence.node.devm.getStorVal owner key).toNat) := by
  obtain ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, ⟨rest, stack⟩, obs⟩ :=
    history.exists_retainedSstore_frame_wsObs capabilities member committed hcode changed
  refine ⟨write, frame, retained, ownerEq, keyEq, valueEq, last, frameMem, frameRaw, chain,
    target, fun code sep tracked => ?_⟩
  rw [← keyEq] at tracked ⊢
  rw [← target]
  rcases allow_class_of_wsObs (by decide) implV2_2_allowSitesOk sep
      (obs Impl.cert_check impl_wsCert code) stack tracked with allowed | nonInc
  · exact Or.inl (allowedFrame_selV2T rfl allowed)
  · exact Or.inr nonInc

end History

end Blanc.Lift.Usdc
