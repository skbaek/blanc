import Blanc.Weth10AllowanceAccounting
import Blanc.Weth10SelectorFacts

/-!
Per-selector arms of the allowance-region transport.

Each arm discharges the `CompiledFrameAllowanceHandler` obligation for one
dispatched selector of an authentic committed WETH10 frame: the compiled
body is childless, so the frame's attribution stream is its own counted
record alone, and replaying that singleton ledger over the entry storage is
exactly the selector's functional effect on the tagged allowance region.

This module establishes the template on the first two arms — the `approve`
store and the `allowance` view — and records the key-agreement bridge from
the runtime's hashed calldata image to the attribution event's projected
key.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## Key agreement -/

/-- The tagged key `approve` actually stores at is the projected key of its
own attribution event: the raw caller word as owner and the raw first
argument word as spender.  The two sides hash the same byte image because
`Sevm.argWord` decodes exactly the 32 calldata bytes the runtime copies. -/
theorem approveRuntimeKey_eq_projected (e : Sevm) :
    approveRuntimeKey e =
      projectedAllowanceKey e.caller.toB256 (Sevm.argWord e 0) := by
  have hlen : (e.data.sliceD 4 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  have harg : Sevm.argWord e 0 = Bytes.toB256 (e.data.sliceD 4 32 0) := by
    unfold Sevm.argWord Sevm.dataWord
    rw [show ((32 * (0 : B256)) + 4).toNat = 4 from by decide]
  unfold approveRuntimeKey projectedAllowanceKey
  rw [harg, Bytes.toBytes_toB256_of_length hlen]

/-! ## Local copies of the compiled body lines

`Weth10HolderFlowExecAccounting` keeps its per-selector line decompositions
private, so this module re-declares the two it needs, byte for byte. -/

private def returnTrueLine : Line :=
  [pushB256 1] ++ mstoreAt 0 ++ pushList [32, 0]

private def approveLine : Line := approvePrefix ++ returnTrueLine

private def allowanceLine : Line :=
  argCopy 0 0 2 ++ allowanceKeyFromMemory ++ [sload] ++
  mstoreAt 0 ++ pushList [32, 0]

/-! ## The `approve` arm -/

/-- The ordinary `approve` body is a childless line ending in `RETURN`, so
an authentic committed frame contributes no proper-descendant counted
records; the counted mirror of
`Exec.Frame.descendantFlowActions_eq_nil_of_approve`. -/
theorem Exec.Frame.attributionInner_eq_nil_of_approve
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "approve" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (approveLine +++ Func.last .ret)) ∈ weth10Funcs dp := by
    rw [hselector]
    simp only [weth10Funcs, List.mem_cons]
    exact Or.inr (Or.inl (by rfl))
  have hchildless : ∀ n ∈ approveLine, NinstIsChildless n := by
    simp [approveLine, approvePrefix, returnTrueLine,
      argCopy, cdc, arg, cdl, allowanceKeyFromMemory, Blanc.logApprove,
      NinstIsChildless, Ninst.pushB256, mstoreAt, logWith, pushList]
  exact frame.attributionInner_eq_nil_of_nonpayableChildless
    context hnonempty hmem hchildless

/-- `approve` transports the allowance region: the attribution stream is
the frame's own record alone, and its event stores the raw value word at
the projected caller/spender key. -/
theorem Exec.Frame.allowanceRegionEffect_of_approve
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "approve" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hinner : Exec.attributionInner dp ca frame.run = [] :=
    frame.attributionInner_eq_nil_of_approve context hselector hnonempty
  have hsel : Sevm.selector frame.sevm = approveSelector := hselector
  have hnotlast : ownRecordLast frame.sevm = false := by
    simp [ownRecordLast, isFlashInvocation, isPermitInvocation, hsel,
      approveSelector_ne_flashLoanSelector, approveSelector_ne_permitSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      [CountedFrame.ofFrame dp ca frame] := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe, hinner,
      Exec.frameContribution_eq_cons dp ca frame []
        context.invocation hnotlast]
  rw [hstream]
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error _ => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst hpc
      have heffect := approve_exec_effect dp context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2 hselector
        hnonempty
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hset : Devm.getStor post ca =
          (Devm.getStor pre ca).set (approveRuntimeKey e)
            (Sevm.argWord e 1) := by
        rw [← htarget]
        exact heffect.2.1
      have hne0 : e.data.length.toB256 ≠ 0 := hnonempty
      have hselE : Sevm.selector e = approveSelector := hselector
      have hown : (CountedFrame.ofFrame dp ca
          (⟨0, e, pre, .ok post, run, committed⟩ : Exec.Frame)).allowance =
          some { owner := e.caller.toB256
                 spender := Sevm.argWord e 0
                 caller := e.caller
                 depth := e.depth
                 visit := .approveStore (Sevm.argWord e 1) } := by
        show frameAllowanceEvent e pre post =
          some { owner := e.caller.toB256
                 spender := Sevm.argWord e 0
                 caller := e.caller
                 depth := e.depth
                 visit := .approveStore (Sevm.argWord e 1) }
        simp [frameAllowanceEvent, hne0, hselE]
      have hcode : Devm.getCode pre ca = Devm.getCode post ca :=
        (congrFun heffect.2.2.2.2.2 ca).symm
      refine ⟨fun key _ => ?_, hcode⟩
      show (Devm.getStor post ca).get key =
        applyAllowanceLedger (Devm.getStor pre ca)
          [CountedFrame.ofFrame dp ca ⟨0, e, pre, .ok post, run, committed⟩]
          key
      rw [applyAllowanceLedger_singleton, hown]
      simp only [AllowanceEvent.key, AllowanceVisit.written?]
      rw [hset]
      by_cases hkey :
          projectedAllowanceKey e.caller.toB256 (Sevm.argWord e 0) = key
      · rw [if_pos hkey, ← hkey, ← approveRuntimeKey_eq_projected]
        exact Stor.get_set_self _ _ _
      · rw [if_neg hkey]
        apply Stor.get_set_ne
        rw [approveRuntimeKey_eq_projected]
        exact hkey

/-! ## The `allowance` view arm -/

/-- The `allowance` view body is a childless line ending in `RETURN`, so an
authentic committed frame contributes no proper-descendant counted
records. -/
theorem Exec.Frame.attributionInner_eq_nil_of_allowance
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "allowance" [.address, .address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (allowanceLine +++ Func.last .ret)) ∈ weth10Funcs dp := by
    rw [hselector]
    have hshape : nonpayable (allowanceLine +++ Func.last .ret) =
        nonpayable allowance := rfl
    rw [hshape]
    simp [weth10Funcs]
  have hchildless : ∀ n ∈ allowanceLine, NinstIsChildless n := by
    simp [allowanceLine, argCopy, cdc, allowanceKeyFromMemory,
      NinstIsChildless, Ninst.pushB256, mstoreAt, pushList]
  exact frame.attributionInner_eq_nil_of_nonpayableChildless
    context hnonempty hmem hchildless

/-- The `allowance` view transports the allowance region: the attribution
stream is the frame's own record alone, its event writes nothing, and the
committed storage is the entry storage. -/
theorem Exec.Frame.allowanceRegionEffect_of_allowance
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "allowance" [.address, .address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hinner : Exec.attributionInner dp ca frame.run = [] :=
    frame.attributionInner_eq_nil_of_allowance context hselector hnonempty
  have hsel : Sevm.selector frame.sevm = allowanceSelector := hselector
  have hnotlast : ownRecordLast frame.sevm = false := by
    simp [ownRecordLast, isFlashInvocation, isPermitInvocation, hsel,
      allowanceSelector_ne_flashLoanSelector,
      allowanceSelector_ne_permitSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      [CountedFrame.ofFrame dp ca frame] := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe, hinner,
      Exec.frameContribution_eq_cons dp ca frame []
        context.invocation hnotlast]
  rw [hstream]
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error _ => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst hpc
      have heffect := allowance_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2 hselector
        hnonempty
      have hstor : Devm.getStor post = Devm.getStor pre := heffect.2.2.1
      have hcode : Devm.getCode pre ca = Devm.getCode post ca :=
        (congrFun heffect.2.2.2.2 ca).symm
      have hne0 : e.data.length.toB256 ≠ 0 := hnonempty
      have hselE : Sevm.selector e = allowanceSelector := hselector
      have hown : (CountedFrame.ofFrame dp ca
          (⟨0, e, pre, .ok post, run, committed⟩ : Exec.Frame)).allowance =
          some { owner := Sevm.argWord e 0
                 spender := Sevm.argWord e 1
                 caller := e.caller
                 depth := e.depth
                 visit := .viewRead ((Devm.getStor pre e.currentTarget).get
                   (projectedAllowanceKey (Sevm.argWord e 0)
                     (Sevm.argWord e 1))) } := by
        show frameAllowanceEvent e pre post =
          some { owner := Sevm.argWord e 0
                 spender := Sevm.argWord e 1
                 caller := e.caller
                 depth := e.depth
                 visit := .viewRead ((Devm.getStor pre e.currentTarget).get
                   (projectedAllowanceKey (Sevm.argWord e 0)
                     (Sevm.argWord e 1))) }
        simp [frameAllowanceEvent, hne0, hselE,
          allowanceSelector_ne_approveSelector,
          allowanceSelector_ne_approveAndCallSelector,
          allowanceSelector_ne_permitSelector,
          allowanceSelector_ne_transferFromSelector,
          allowanceSelector_ne_withdrawFromSelector,
          allowanceSelector_ne_flashLoanSelector]
      refine ⟨fun key _ => ?_, hcode⟩
      show (Devm.getStor post ca).get key =
        applyAllowanceLedger (Devm.getStor pre ca)
          [CountedFrame.ofFrame dp ca ⟨0, e, pre, .ok post, run, committed⟩]
          key
      rw [applyAllowanceLedger_singleton, hown]
      simp only [AllowanceVisit.written?, ite_self]
      rw [congrFun hstor ca]

/-! ## Read-sound variants

Both selectors here contribute exactly one counted record, and that record's
allowance event is computed from the frame's entry storage, so
`AllowanceRegionEffectSound.of_singletonArm` upgrades the existing transport
outright. -/

/-- `approve` transports the allowance region read-soundly: its ledger is
the frame's own record alone, and an `approveStore` visit records the entry
word at the approved key. -/
theorem Exec.Frame.allowanceRegionEffectSound_of_approve
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "approve" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffectSound ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) :=
  .of_singletonArm context
    (frame.allowanceRegionEffect_of_approve context hselector hnonempty)
    (frame.attributionInner_eq_nil_of_approve context hselector hnonempty)
    (ownRecordLast_eq_false_of_selector hselector
      approveSelector_ne_flashLoanSelector approveSelector_ne_permitSelector)

/-- `allowance` transports the allowance region read-soundly: its ledger is
the frame's own record alone, and a `viewRead` visit is by construction the
entry word at the queried key. -/
theorem Exec.Frame.allowanceRegionEffectSound_of_allowance
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "allowance" [.address, .address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffectSound ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) :=
  .of_singletonArm context
    (frame.allowanceRegionEffect_of_allowance context hselector hnonempty)
    (frame.attributionInner_eq_nil_of_allowance context hselector hnonempty)
    (ownRecordLast_eq_false_of_selector hselector
      allowanceSelector_ne_flashLoanSelector
      allowanceSelector_ne_permitSelector)

end Weth10

end Blanc

