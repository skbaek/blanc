import Blanc.Lift.Usdc.AllowanceRawHistory
import Blanc.Lift.Usdc.InitRowsHistory
import Blanc.Lift.Usdc.RetainedOldRecovery

/-! Actual globally retained allowance writers and their remaining V2_2 owner case. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.ExecutionTrace

section History

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {P pair : Adr} {Tr : Adr → Prop}

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
  obtain ⟨G, committed, chain⟩ :=
    (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run m).mp retained
  have member : G ∈ history.settledFrames := by
    rw [history.settledFrames_eq]
    exact List.mem_flatMap.mpr ⟨R, root, committed⟩
  have rawMember := history.mem_rawFrames_of_mem_settledFrames G member
  have nodeMember : m ∈ history.rawNodes :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix m).mpr ⟨_, rawMember, chain⟩
  have nodeTarget : m.sevm.currentTarget = P :=
    (successfulSstore?_node_owner found).2.symm.trans owner
  have target : G.sevm.currentTarget = P :=
    (congrArg Sevm.currentTarget (Exec.Deriv.ParentPrefix.sevm_eq chain)).symm.trans nodeTarget
  obtain ⟨raw, rawMem, rawChain, rawTarget, classified⟩ :=
    ConfiguredHistoryTraceIn.usdc_rawRowWrite history capabilities codes proxyApart rowSep
      nodeMember found owner tracked
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
          excluded member target version (oldReady G member target version named) named
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

end History

end Blanc.Lift.Usdc
