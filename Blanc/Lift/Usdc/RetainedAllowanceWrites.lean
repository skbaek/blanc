import Blanc.Lift.Usdc.AllowanceRawHistory
import Blanc.Lift.Usdc.InitRowsHistory
import Blanc.Lift.Usdc.RetainedOldRecovery
import Blanc.ExecutionMidHistoryInForest
import Blanc.Lift.Usdc.ProxyRetainedNoDel
import Blanc.ExecutionRetainedCellZero

/-! Actual globally retained allowance writers and their remaining V2_2 owner case. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P pair : Adr} {Tr : Adr → Prop}

private theorem retainedRowWrite_nonInc_or_v2_2_owner_of_frames
    {frames roots : List Exec.Frame}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    (framesEq : frames = rootFrames roots)
    (frameSubset : frames ⊆ history.settledFrames)
    (noCaller : ∀ (G : Exec.Frame), G ∈ frames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery history P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    {R : Exec.Frame} (root : R ∈ roots)
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key)
    (writeClass : ∃ raw ∈ history.rawFrames, Exec.Deriv.ParentPrefix raw m ∧
      raw.sevm.currentTarget = P ∧ (UsdcAllowException pair raw ∨
        w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat)) :
    ∃ G : Exec.Frame, G ∈ frames ∧ G ∈ Exec.committedFrames R.run ∧
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m ∧ G.sevm.currentTarget = P ∧
      (w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat ∨
        (G.sevm.code = Impl.code ∧ Sevm.selector G.sevm ∈ selV2_2.owners ∧
          (Sevm.dataWord G.sevm 4).toAdr = pair)) := by
  obtain ⟨G, committed, chain⟩ :=
    (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run m).mp retained
  have member : G ∈ frames := by
    rw [framesEq]
    exact List.mem_flatMap.mpr ⟨R, root, committed⟩
  have fullMember := frameSubset member
  have rawMember := history.mem_rawFrames_of_mem_settledFrames G fullMember
  have nodeTarget : m.sevm.currentTarget = P :=
    (successfulSstore?_node_owner found).2.symm.trans owner
  have target : G.sevm.currentTarget = P :=
    (congrArg Sevm.currentTarget (Exec.Deriv.ParentPrefix.sevm_eq chain)).symm.trans nodeTarget
  obtain ⟨raw, rawMem, rawChain, rawTarget, classified⟩ :=
    writeClass
  have same : raw.sevm = (Exec.Frame.rootDeriv G).sevm :=
    (Exec.Deriv.ParentPrefix.sevm_eq rawChain).symm.trans
      (Exec.Deriv.ParentPrefix.sevm_eq chain)
  refine ⟨G, member, committed, chain, target, ?_⟩
  rcases classified with exception | nonInc
  · have actual : UsdcAllowException pair (Exec.Frame.rootDeriv G) := by
      unfold UsdcAllowException at exception ⊢
      rw [same] at exception
      exact exception
    rcases usdcAllowException_split actual with pairException | initializer
    · have canonical (t : SelTable) (h : PairAllowedFrame t pair (Env.root G.sevm)) :
          (t.selT.eval (Env.root G.sevm) ∈ t.callers ∧ G.sevm.caller = pair) ∨
            (t.selT.eval (Env.root G.sevm) ∈ t.owners ∧
              (Sevm.dataWord G.sevm 4).toAdr = pair) := by
        simpa only [PairAllowedFrame, Env.root, Term.eval, toAdr_toB256, Sevm.dataWord] using h
      have rejectCaller (sel : Sevm.selector G.sevm ∈
          [0x095ea7b3, 0x39509351, 0xa457c2d7]) (caller : G.sevm.caller = pair) : False :=
        noCaller G member target m w chain found sel caller
      have rejectOwner
          (version : (G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
            (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners))
          (named : (Sevm.dataWord G.sevm 4).toAdr = pair) : False :=
        ConfiguredHistoryTraceIn.retained_old_owner_not_pair_effective history capabilities bal
          excluded fullMember target version (oldReady G fullMember target version named) named
      rcases pairException with ⟨code, allowed⟩ | ⟨code, allowed⟩ |
          ⟨code, allowed⟩ | ⟨code, allowed⟩
      · have allowed := canonical selV1 allowed
        simp only [selV1, selV1T_root, List.mem_cons, List.not_mem_nil, or_false,
          false_and, or_false] at allowed
        exact (rejectCaller (by rw [allowed.1]; exact List.mem_cons_self) allowed.2).elim
      · have allowed := canonical selV2 allowed
        simp only [selV2, selV2T_root_selWord, selWord_eq_selector] at allowed
        rcases allowed with caller | named
        · exact (rejectCaller caller.1 caller.2).elim
        · exact (rejectOwner (.inl ⟨code, named.1⟩) named.2).elim
      · have allowed := canonical selV2_1 allowed
        simp only [selV2_1, selV2T_root_selWord, selWord_eq_selector] at allowed
        rcases allowed with caller | named
        · exact (rejectCaller caller.1 caller.2).elim
        · exact (rejectOwner (.inr ⟨code, named.1⟩) named.2).elim
      · have allowed := canonical selV2_2 allowed
        simp only [selV2_2, selV2T_root_selWord, selWord_eq_selector] at allowed
        rcases allowed with caller | named
        · exact (rejectCaller caller.1 caller.2).elim
        · exact .inr ⟨code, named.1, named.2⟩
    · exact .inl (ConfiguredHistoryTraceIn.initRowWritesNonInc history capabilities initApart
        _ rawMember target initializer m chain w found tracked)
  · exact .inl nonInc

/-- A globally retained tracked-row write is non-increasing, or its same globally
retained parent is a V2_2 owner exception. Caller and old-owner readiness inputs
are local producer obligations; no exclusion is applied to a discarded frame. -/
theorem ConfiguredHistoryTraceIn.usdc_retainedRowWrite_nonInc_or_v2_2_owner_of_rawClass
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    (rawClass : UsdcRawRowWriteClass P pair Tr history.rawFrames history.rawNodes)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    (noCaller : ∀ (G : Exec.Frame), G ∈ history.settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery history P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    {R : Exec.Frame} (root : R ∈ history.settledRoots)
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    ∃ G : Exec.Frame, G ∈ history.settledFrames ∧ G ∈ Exec.committedFrames R.run ∧
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m ∧ G.sevm.currentTarget = P ∧
      (w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat ∨
        (G.sevm.code = Impl.code ∧ Sevm.selector G.sevm ∈ selV2_2.owners ∧
          (Sevm.dataWord G.sevm 4).toAdr = pair)) := by
  have rawRoot := history.mem_rawFrames_of_mem_settledRoots R root
  have rawNode := history.rawNodes_of_mem_rawFrames _ rawRoot m
    ((Exec.retainedNodes_sublist_rawNodes R.run).subset retained)
  exact retainedRowWrite_nonInc_or_v2_2_owner_of_frames history capabilities bal
    initApart history.settledFrames_eq (fun _ member => member)
    noCaller excluded oldReady root retained found owner tracked
    (rawClass rawNode found owner tracked)

/-- A globally retained tracked-row write is non-increasing, or its same globally
retained parent is a V2_2 owner exception. Caller and old-owner readiness inputs
are local producer obligations; no exclusion is applied to a discarded frame. -/
theorem ConfiguredHistoryTraceIn.usdc_retainedRowWrite_nonInc_or_v2_2_owner
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    (codes : UsdcNodeCodes P history.rawNodes)
    (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
    (rowSep : UsdcRowSep P pair Tr history.rawFrames)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    (noCaller : ∀ (G : Exec.Frame), G ∈ history.settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery history P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    {R : Exec.Frame} (root : R ∈ history.settledRoots)
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    ∃ G : Exec.Frame, G ∈ history.settledFrames ∧ G ∈ Exec.committedFrames R.run ∧
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m ∧ G.sevm.currentTarget = P ∧
      (w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat ∨
        (G.sevm.code = Impl.code ∧ Sevm.selector G.sevm ∈ selV2_2.owners ∧
          (Sevm.dataWord G.sevm 4).toAdr = pair)) := by
  exact ConfiguredHistoryTraceIn.usdc_retainedRowWrite_nonInc_or_v2_2_owner_of_rawClass history capabilities bal
    (ConfiguredHistoryTraceIn.usdc_rawRowWrite history capabilities codes proxyApart rowSep)
    initApart noCaller excluded oldReady root retained found owner tracked

/-- The separate retained V2_2 owner producer closes the only residual case.
This is one actual-write result, not a retained storage or endpoint fold. -/
theorem ConfiguredHistoryTraceIn.usdc_retainedRowWrite_nonInc
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    (codes : UsdcNodeCodes P history.rawNodes)
    (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
    (rowSep : UsdcRowSep P pair Tr history.rawFrames)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    (noCaller : ∀ (G : Exec.Frame), G ∈ history.settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery history P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    (v2_2Owner : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      G.sevm.code = Impl.code → Sevm.selector G.sevm ∈ selV2_2.owners →
      (Sevm.dataWord G.sevm 4).toAdr ≠ pair)
    {R : Exec.Frame} (root : R ∈ history.settledRoots)
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    ∃ G : Exec.Frame, G ∈ history.settledFrames ∧ G ∈ Exec.committedFrames R.run ∧
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m ∧ G.sevm.currentTarget = P ∧
      w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat := by
  obtain ⟨G, member, committed, chain, target, nonInc | residual⟩ :=
    ConfiguredHistoryTraceIn.usdc_retainedRowWrite_nonInc_or_v2_2_owner history capabilities bal
      codes proxyApart rowSep initApart noCaller excluded oldReady root retained found owner tracked
  · exact ⟨G, member, committed, chain, target, nonInc⟩
  · exact (v2_2Owner G member target residual.1 residual.2.1 residual.2.2).elim


/-- One retained write needs classification only at its own node. All native
queries and initializer separation still belong to the original history. -/
theorem ConfiguredHistoryTraceIn.usdc_retainedRowWrite_nonInc_of_retainedCode_of_rootCallers
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
    (rowSep : UsdcModernRowSep P pair Tr history.rawFrames)
    (v1Class : V1RawWriteClass P pair Tr history.rawFrames)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    {R : Exec.Frame}
    (noCaller : ∀ (G : Exec.Frame), G ∈ Exec.committedFrames R.run →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery history P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    (v2_2Owner : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      G.sevm.code = Impl.code → Sevm.selector G.sevm ∈ selV2_2.owners →
      (Sevm.dataWord G.sevm 4).toAdr ≠ pair)
    (root : R ∈ history.settledRoots)
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    (code : UsdcContextCode m.sevm.code)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    ∃ G : Exec.Frame, G ∈ history.settledFrames ∧ G ∈ Exec.committedFrames R.run ∧
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m ∧ G.sevm.currentTarget = P ∧
      w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat := by
  have rawRoot := history.mem_rawFrames_of_mem_settledRoots R root
  have rawNode := history.rawNodes_of_mem_rawFrames _ rawRoot m
    ((Exec.retainedNodes_sublist_rawNodes R.run).subset retained)
  have classified := ConfiguredHistoryTraceIn.usdc_rawRowWrite_of_nodeCode history
    capabilities proxyApart rowSep v1Class rawNode code found owner tracked
  have subset : Exec.committedFrames R.run ⊆ history.settledFrames := by
    intro G member
    rw [history.settledFrames_eq]
    exact List.mem_flatMap.mpr ⟨R, root, member⟩
  have framesEq : Exec.committedFrames R.run = rootFrames [R] := by
    simp only [rootFrames, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  obtain ⟨G, member, committed, chain, target, nonInc | residual⟩ :=
    retainedRowWrite_nonInc_or_v2_2_owner_of_frames history capabilities bal initApart
      framesEq subset noCaller excluded oldReady
      List.mem_cons_self retained found owner tracked classified
  · exact ⟨G, subset member, committed, chain, target, nonInc⟩
  · exact (v2_2Owner G (subset member) target residual.1 residual.2.1 residual.2.2).elim


/-- Compatibility with caller evidence over the full original settled history. -/
theorem ConfiguredHistoryTraceIn.usdc_retainedRowWrite_nonInc_of_retainedCode
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
    (rowSep : UsdcModernRowSep P pair Tr history.rawFrames)
    (v1Class : V1RawWriteClass P pair Tr history.rawFrames)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    (noCaller : ∀ (G : Exec.Frame), G ∈ history.settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery history P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    (v2_2Owner : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      G.sevm.code = Impl.code → Sevm.selector G.sevm ∈ selV2_2.owners →
      (Sevm.dataWord G.sevm 4).toAdr ≠ pair)
    {R : Exec.Frame} (root : R ∈ history.settledRoots)
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    (code : UsdcContextCode m.sevm.code)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    ∃ G : Exec.Frame, G ∈ history.settledFrames ∧ G ∈ Exec.committedFrames R.run ∧
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m ∧ G.sevm.currentTarget = P ∧
      w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat := by
  apply ConfiguredHistoryTraceIn.usdc_retainedRowWrite_nonInc_of_retainedCode_of_rootCallers
    history capabilities bal proxyApart rowSep v1Class initApart ?_ excluded oldReady
    v2_2Owner root retained code found owner tracked
  intro G member
  apply noCaller G
  rw [history.settledFrames_eq]
  exact List.mem_flatMap.mpr ⟨R, root, member⟩

/-- A retained write under an actual post-cut mid root is non-increasing or has the
same mid retained V2_2 owner exception. Raw facts, independent native-query exclusion and
explicit old-owner routing remain on the original full history. -/
theorem MidHistoryTraceIn.usdc_retainedRowWrite_nonInc_or_v2_2_owner_of_rawClass
    {pre completed : BlockChain} {i : Nat}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn F cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    (rawClass : UsdcRawRowWriteClass P pair Tr
      ((prior.step block).append later).rawFrames ((prior.step block).append later).rawNodes)
    (initApart : InitRowsApart P pair Tr ((prior.step block).append later).rawFrames)
    (noCaller : ∀ (G : Exec.Frame),
      G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery ((prior.step block).append later) P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ ((prior.step block).append later).settledFrames →
      G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    {R : Exec.Frame} (root : R ∈ ((MidHistoryTraceIn.tail block cut).append later).settledRoots)
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    ∃ G : Exec.Frame, G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames ∧
      G ∈ Exec.committedFrames R.run ∧
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m ∧ G.sevm.currentTarget = P ∧
      (w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat ∨
        (G.sevm.code = Impl.code ∧ Sevm.selector G.sevm ∈ selV2_2.owners ∧
          (Sevm.dataWord G.sevm 4).toAdr = pair)) := by
  let full := (prior.step block).append later
  let mid := (MidHistoryTraceIn.tail block cut).append later
  obtain ⟨G, committed, chain⟩ :=
    (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run m).mp retained
  have member : G ∈ mid.settledFrames := by
    rw [mid.settledFrames_eq]
    exact List.mem_flatMap.mpr ⟨R, root, committed⟩
  have fullMember := MidHistoryTraceIn.settledFrames_subset_full prior block cut later member
  have rawNode := (full.mem_rawNodes_iff_rawFrame_parentPrefix m).mpr
    ⟨_, full.mem_rawFrames_of_mem_settledFrames G fullMember, chain⟩
  exact retainedRowWrite_nonInc_or_v2_2_owner_of_frames full capabilities bal
    initApart mid.settledFrames_eq
    (MidHistoryTraceIn.settledFrames_subset_full prior block cut later)
    noCaller excluded oldReady root retained found owner tracked
    (rawClass rawNode found owner tracked)

/-- A retained write under an actual post-cut mid root is non-increasing or has the
same mid retained V2_2 owner exception. Raw facts, independent native-query exclusion and
explicit old-owner routing remain on the original full history. -/
theorem MidHistoryTraceIn.usdc_retainedRowWrite_nonInc_or_v2_2_owner
    {pre completed : BlockChain} {i : Nat}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn F cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    (codes : UsdcNodeCodes P ((prior.step block).append later).rawNodes)
    (proxyApart : ProxyRowsApart P pair Tr ((prior.step block).append later).rawNodes)
    (rowSep : UsdcRowSep P pair Tr ((prior.step block).append later).rawFrames)
    (initApart : InitRowsApart P pair Tr ((prior.step block).append later).rawFrames)
    (noCaller : ∀ (G : Exec.Frame),
      G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery ((prior.step block).append later) P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ ((prior.step block).append later).settledFrames →
      G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    {R : Exec.Frame} (root : R ∈ ((MidHistoryTraceIn.tail block cut).append later).settledRoots)
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    ∃ G : Exec.Frame, G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames ∧
      G ∈ Exec.committedFrames R.run ∧
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m ∧ G.sevm.currentTarget = P ∧
      (w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat ∨
        (G.sevm.code = Impl.code ∧ Sevm.selector G.sevm ∈ selV2_2.owners ∧
          (Sevm.dataWord G.sevm 4).toAdr = pair)) := by
  exact MidHistoryTraceIn.usdc_retainedRowWrite_nonInc_or_v2_2_owner_of_rawClass prior block cut later
    capabilities bal
    (ConfiguredHistoryTraceIn.usdc_rawRowWrite ((prior.step block).append later) capabilities
      codes proxyApart rowSep) initApart noCaller excluded oldReady root retained found owner tracked

section Dynamic

variable
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
    (rowSep : UsdcModernRowSep P pair Tr history.rawFrames)
    (v1Class : V1RawWriteClass P pair Tr history.rawFrames)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    (noCaller : ∀ (G : Exec.Frame), G ∈ history.settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery history P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    (v2_2Owner : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      G.sevm.code = Impl.code → Sevm.selector G.sevm ∈ selV2_2.owners →
      (Sevm.dataWord G.sevm 4).toAdr ≠ pair)
    {W : List UsdcDeployedEntry} {R : Exec.Frame}
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
    (apart : KnownImplSlotApart P (Exec.retainedNodes R.run))

include history capabilities bal proxyApart rowSep v1Class initApart noCaller excluded
  oldReady v2_2Owner member proxy impls lib slot governance installations apart

omit noCaller in
/-- Allowance non-increase from retained F2′ governance and runtime installations
at actual upgrade positions. No raw-node code family or raw upgrade check is an
input; caller, native-query, routing and row-separation obligations are unchanged. -/
theorem ConfiguredHistoryTraceIn.settledRoot_allowanceWrite_nonInc_from_installations_of_rootCallers
    (noRootCaller : ∀ (G : Exec.Frame), G ∈ Exec.committedFrames R.run →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat := by
  have context := ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_from_installations
    history capabilities (fun {_} hf => bal _ hf) member proxy impls lib slot governance
    installations apart
  have target : m.sevm.currentTarget = P :=
    (successfulSstore?_node_owner found).2.symm.trans owner
  have code : UsdcContextCode m.sevm.code := by
    rcases (context m retained).2 target with ⟨code, _⟩ | ⟨e, he, code, _⟩
    · exact .inl code
    · rw [code]
      exact (impls e he).context
  obtain ⟨G, _, _, _, _, bound⟩ :=
    ConfiguredHistoryTraceIn.usdc_retainedRowWrite_nonInc_of_retainedCode_of_rootCallers history
      capabilities bal proxyApart rowSep v1Class initApart noRootCaller excluded oldReady v2_2Owner
      member retained code found owner tracked
  exact bound

/-- Compatibility with caller evidence over the full original settled history. -/
theorem ConfiguredHistoryTraceIn.settledRoot_allowanceWrite_nonInc_from_installations
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run)
    {w : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? m = some w)
    (owner : w.owner = P) (tracked : ∃ g, Tr g ∧ allowSlot pair g = w.key) :
    w.value.toNat ≤ ((m.devm.getStor P).get w.key).toNat := by
  apply ConfiguredHistoryTraceIn.settledRoot_allowanceWrite_nonInc_from_installations_of_rootCallers
    history capabilities bal proxyApart rowSep v1Class initApart excluded oldReady
    v2_2Owner member proxy impls lib slot governance installations apart ?_ retained found owner tracked
  intro G committed
  apply noCaller G
  rw [history.settledFrames_eq]
  exact List.mem_flatMap.mpr ⟨R, member, committed⟩

omit noCaller in
/-- A zero allowance row remains zero across the actual settled root, using the
retained dynamic upgrade proof and the shared cell invariant. Transaction sweeps
and history composition are separate from this execution-root endpoint. -/
theorem ConfiguredHistoryTraceIn.settledRoot_allowance_zero_from_installations_of_rootCallers
    (noRootCaller : ∀ (G : Exec.Frame), G ∈ Exec.committedFrames R.run →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
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
  have bound := ConfiguredHistoryTraceIn.settledRoot_allowanceWrite_nonInc_from_installations_of_rootCallers
    history capabilities bal proxyApart rowSep v1Class initApart excluded oldReady
    v2_2Owner member proxy impls lib slot governance installations apart noRootCaller retained found owner
    ⟨g, tracked, key.symm⟩
  simpa only [key] using bound

/-- Compatibility with caller evidence over the full original settled history. -/
theorem ConfiguredHistoryTraceIn.settledRoot_allowance_zero_from_installations
    {g : Adr} (tracked : Tr g)
    (zero : (R.pre.getStor P).get (allowSlot pair g) = 0) :
    (R.post.getStor P).get (allowSlot pair g) = 0 := by
  apply ConfiguredHistoryTraceIn.settledRoot_allowance_zero_from_installations_of_rootCallers
    history capabilities bal proxyApart rowSep v1Class initApart excluded oldReady
    v2_2Owner member proxy impls lib slot governance installations apart ?_ tracked zero
  intro G committed
  apply noCaller G
  rw [history.settledFrames_eq]
  exact List.mem_flatMap.mpr ⟨R, member, committed⟩

end Dynamic

/-- Complete transaction settlement preserves all tracked zero allowance rows.
Root readiness is derived from the transaction's actual entry state. Retained
terminal safety excludes deletion, so fee settlement and touched-account sweep
need no supplied deletion oracle or created-account exclusion. The selected
implementation address remains in W; runtime readiness at the final state is
not asserted by this projection. -/
theorem ConfiguredHistoryTraceIn.transaction_allowance_zero_from_installations_of_transactionCallers
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
    (rowSep : UsdcModernRowSep P pair Tr history.rawFrames)
    (v1Class : V1RawWriteClass P pair Tr history.rawFrames)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery history P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    (v2_2Owner : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      G.sevm.code = Impl.code → Sevm.selector G.sevm ∈ selV2_2.owners →
      (Sevm.dataWord G.sevm 4).toAdr ≠ pair)
    {W : List UsdcDeployedEntry}
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (noCaller : ∀ (G : Exec.Frame), G ∈ trace.settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
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
      ∃ e ∈ W, write.value.toAdr = e.adr ∧ e.RuntimeReady N.devm)
    (apart : ∀ R ∈ trace.settledRoots, KnownImplSlotApart P (Exec.retainedNodes R.run))
    (zero : ∀ g, Tr g → (benv.state.getStor P).get (allowSlot pair g) = 0) :
    P ∉ trace.messageOut.accountsToDelete ∧ state.getCode P = Proxy.code ∧
      (∃ e ∈ W, ((state.getStor P).get implSlot).toAdr = e.adr) ∧
      ∀ g, Tr g → (state.getStor P).get (allowSlot pair g) = 0 := by
  have proxyFamily : UsdcContextCode Proxy.code := .inl rfl
  have libraryFamily : UsdcContextCode Lib.code := .inr (.inr (.inr (.inr (.inr rfl))))
  have ready (R : Exec.Frame) (member : R ∈ trace.settledRoots) :
      R.pre.getCode P = Proxy.code ∧
        ∃ e ∈ W, ((R.pre.getStor P).get implSlot).toAdr = e.adr ∧
          e.RuntimeReady R.pre := by
    obtain ⟨e, he, address, runtime, library⟩ := slot
    obtain ⟨rootProxy, rootSlot⟩ := trace.settledRoots_entry_code_cell
      proxy proxyFamily.ne_nil proxyFamily.not_delegation implSlot R member
    refine ⟨rootProxy, e, he, ?_, ?_, ?_⟩
    · rw [rootSlot]; exact address
    · exact (trace.settledRoots_entry_code_cell runtime (impls e he).context.ne_nil
        (impls e he).context.not_delegation 0 R member).1
    · intro implementation
      exact (trace.settledRoots_entry_code_cell (library implementation) libraryFamily.ne_nil
        libraryFamily.not_delegation 0 R member).1
  have context (R : Exec.Frame) (member : R ∈ trace.settledRoots) :=
    ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_from_installations history
      capabilities (fun {_} hf => bal _ hf) (rootsIn R member) (ready R member).1 impls lib
      (ready R member).2 governance (installations R member) (apart R member)
  have notDeleted := trace.not_deleted_of_retained_terminals hsg (a := P) (by
    intro R member
    apply ConfiguredHistoryTraceIn.settledRoot_usdcContext_terminal_safe history capabilities
      (rootsIn R member)
    intro N retained target
    rcases (context R member N retained).2 target with ⟨code, _⟩ | ⟨e, he, code, _⟩
    · exact .inl code
    · rw [code]; exact (impls e he).context)
  have pointer := trace.cell_property_of_settledRoots implSlot hsg proxy proxyFamily.ne_nil
    proxyFamily.not_delegation notDeleted (fun word => ∃ e ∈ W, word.toAdr = e.adr)
    (by
      intro R member _
      obtain ⟨_, e, he, address, _⟩ :=
        ConfiguredHistoryTraceIn.settledRoot_dynamic_runtimeReady_of_f2prime history capabilities
          (fun {_} hf => bal _ hf) (rootsIn R member) (ready R member).1 impls lib
          (ready R member).2 governance (installations R member) (apart R member)
      exact ⟨e, he, address⟩)
    (by obtain ⟨e, he, address, _⟩ := slot; exact ⟨e, he, address⟩)
  refine ⟨notDeleted, pointer.2, pointer.1, ?_⟩
  intro g tracked
  exact (trace.cell_property_of_settledRoots (allowSlot pair g) hsg proxy proxyFamily.ne_nil
    proxyFamily.not_delegation notDeleted (fun word => word = 0)
    (by
      intro R member rootZero
      exact ConfiguredHistoryTraceIn.settledRoot_allowance_zero_from_installations_of_rootCallers history
        capabilities bal proxyApart rowSep v1Class initApart excluded oldReady v2_2Owner
        (rootsIn R member) (ready R member).1 impls lib (ready R member).2 governance
        (installations R member) (apart R member)
        (fun G committed => noCaller G (by
          rw [trace.settledFrames_eq]
          exact List.mem_flatMap.mpr ⟨R, member, committed⟩)) tracked rootZero)
    (zero g tracked)).1

/-- Compatibility with caller evidence over the full original settled history. -/
theorem ConfiguredHistoryTraceIn.transaction_allowance_zero_from_installations
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (bal : ∀ f, F f → f.ruleSet.bal = none)
    (proxyApart : ProxyRowsApart P pair Tr history.rawNodes)
    (rowSep : UsdcModernRowSep P pair Tr history.rawFrames)
    (v1Class : V1RawWriteClass P pair Tr history.rawFrames)
    (initApart : InitRowsApart P pair Tr history.rawFrames)
    (noCaller : ∀ (G : Exec.Frame), G ∈ history.settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
      Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
      Exec.Deriv.successfulSstore? m = some w →
      Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery history P pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    (v2_2Owner : ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      G.sevm.code = Impl.code → Sevm.selector G.sevm ∈ selV2_2.owners →
      (Sevm.dataWord G.sevm 4).toAdr ≠ pair)
    {W : List UsdcDeployedEntry}
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (governance : UsdcGovernanceF2primeOn P history.settledFrames)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
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
      ∃ e ∈ W, write.value.toAdr = e.adr ∧ e.RuntimeReady N.devm)
    (apart : ∀ R ∈ trace.settledRoots, KnownImplSlotApart P (Exec.retainedNodes R.run))
    (zero : ∀ g, Tr g → (benv.state.getStor P).get (allowSlot pair g) = 0) :
    P ∉ trace.messageOut.accountsToDelete ∧ state.getCode P = Proxy.code ∧
      (∃ e ∈ W, ((state.getStor P).get implSlot).toAdr = e.adr) ∧
      ∀ g, Tr g → (state.getStor P).get (allowSlot pair g) = 0 := by
  apply ConfiguredHistoryTraceIn.transaction_allowance_zero_from_installations_of_transactionCallers
    history capabilities bal proxyApart rowSep v1Class initApart excluded oldReady v2_2Owner
    impls lib governance trace rootsIn ?_ hsg proxy slot installations apart zero
  intro G member
  rw [trace.settledFrames_eq] at member
  obtain ⟨R, root, committed⟩ := List.mem_flatMap.mp member
  apply noCaller G
  rw [history.settledFrames_eq]
  exact List.mem_flatMap.mpr ⟨R, rootsIn R root, committed⟩

end History

end Blanc.Lift.Usdc
