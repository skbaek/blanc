import Blanc.Weth10AllowanceArms

/-!
Per-selector arms of the allowance-region transport: the childless views.

Every selector below reads state but writes nothing and records no
allowance event, so its transported effect is the identity on the tagged
allowance region: the compiled body is childless, the frame's attribution
stream is its own counted record alone, that record's allowance event is
`none`, and replaying the singleton ledger over the entry storage returns
the entry value at every key.  The committed storage equals the entry
storage by the selector's `PublicReadResult` observation.

Ten views are straight childless lines ending in `RETURN` and reuse
`attributionInner_eq_nil_of_nonpayableChildless` directly.  The remaining
three (`DOMAIN_SEPARATOR`, `maxFlashLoan`, `flashFee`) branch after a
childless selection line; a local branch-agnostic counted select walks
whichever arm actually ran, and `flashFee`'s error arm is refuted outright
because its callee is the fixed `flashTokenError` reverter.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## Local copies of the compiled body lines

`Weth10HolderFlowExecAccounting` keeps its per-selector line decompositions
private, so this module re-declares the ones it needs, byte for byte. -/

private def returnWordLine (w : B256) : Line :=
  [pushB256 w] ++ mstoreAt 0 ++ pushList [32, 0]

private def nameLine : Line :=
  [pushB256 (Blanc.String.toBytes "Wrapped Ether v10").toB256,
    pushB256 120, shl] ++
  pushList [17, 32] ++ mstoreAt 0 ++ mstoreAt 1 ++ mstoreAt 2 ++
  pushList [96, 0]

private def symbolLine : Line :=
  [pushB256 (Blanc.String.toBytes "WETH10").toB256,
    pushB256 208, shl] ++
  pushList [6, 32] ++ mstoreAt 0 ++ mstoreAt 1 ++ mstoreAt 2 ++
  pushList [96, 0]

private def totalSupplyLine : Line :=
  [selfbalance] ++ pushFlashMintedSlot ++ [sload, add] ++
  mstoreAt 0 ++ pushList [32, 0]

private def balanceOfLine : Line :=
  arg 0 ++ [sload] ++ mstoreAt 0 ++ pushList [32, 0]

private def noncesLine : Line :=
  arg 0 ++ tagNonceKey ++ [sload] ++ mstoreAt 0 ++ pushList [32, 0]

private def flashMintedLine : Line :=
  pushFlashMintedSlot ++ [sload] ++ mstoreAt 0 ++ pushList [32, 0]

private def deploymentChainIdLine (dp : DeployParams) : Line :=
  [pushDeployWord dp.deploymentChainId] ++
  mstoreAt 0 ++ pushList [32, 0]

private def domainSelectLine (dp : DeployParams) : Line :=
  [chainid, dup 0, pushDeployWord dp.deploymentChainId, eq]

private def domainCachedLine (dp : DeployParams) : Line :=
  [pop, pushDeployWord dp.cachedDomainSeparator] ++
  mstoreAt 0 ++ pushList [32, 0]

private def domainFreshLine : Line :=
  calculateDomainSeparator ++ mstoreAt 0 ++ pushList [32, 0]

private def maxFlashLoanSelectLine : Line := arg 0 ++ [address, eq]

private def maxFlashLoanAvailableLine : Line :=
  pushFlashMintedSlot ++
  [sload, pushB256 (Nat.toB256 maxFlashMinted), sub] ++
  mstoreAt 0 ++ pushList [32, 0]

private def flashFeeSelectLine : Line :=
  arg 0 ++ [address, eq, iszero]

/-! ## Branch-agnostic counted select

`Weth10AttributionChronology` mirrors the compiled walk only for known
branch flags; the branchy views need whichever arm actually ran, exactly as
`Exec.Frame.CompiledCursor.selectBranchWithActions` provides on the
action-labelled walk. -/

/-! ## Shared transport for storage-invariant views -/

/-- Shared transport tail for every childless view whose committed storage
is the entry storage: the attribution stream collapses to the frame's own
record, that record's allowance event is `none`, and replaying the
singleton ledger is the identity on every key. -/
private theorem Exec.Frame.allowanceRegionEffect_of_storageInvariantView
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {sig : B256}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = sig)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hinner : Exec.attributionInner dp ca frame.run = [])
    (hneApprove : sig ≠ approveSelector)
    (hneApproveCall : sig ≠ approveAndCallSelector)
    (hnePermit : sig ≠ permitSelector)
    (hneTransferFrom : sig ≠ transferFromSelector)
    (hneWithdrawFrom : sig ≠ withdrawFromSelector)
    (hneFlash : sig ≠ flashLoanSelector)
    (hneAllowance : sig ≠ allowanceSelector)
    (hstor : Devm.getStor frame.post = Devm.getStor frame.pre)
    (hcode : Devm.getCode frame.pre ca = Devm.getCode frame.post ca) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hselector, hneFlash]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hstream : Exec.attributionStream dp ca frame.run =
      [CountedFrame.ofFrame dp ca frame] := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe, hinner,
      Exec.frameContribution_eq_cons dp ca frame []
        context.invocation hnotflash]
  rw [hstream]
  have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post = none
    simp [frameAllowanceEvent, hnonempty, hselector, hneApprove,
      hneApproveCall, hnePermit, hneTransferFrom, hneWithdrawFrom,
      hneFlash, hneAllowance]
  refine ⟨fun key _ => ?_, hcode⟩
  rw [applyAllowanceLedger_singleton, hown, congrFun hstor ca]

/-! ## The `name` view arm -/

/-- The `name` view body is a childless line ending in `RETURN`, so an
authentic committed frame contributes no proper-descendant counted
records. -/
theorem Exec.Frame.attributionInner_eq_nil_of_name
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "name" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (nameLine +++ Func.last .ret)) ∈ weth10Funcs dp := by
    rw [hselector]
    have hshape : nonpayable (nameLine +++ Func.last .ret) =
        nonpayable name := rfl
    rw [hshape]
    simp [weth10Funcs]
  have hchildless : ∀ n ∈ nameLine, NinstIsChildless n := by
    simp [nameLine, NinstIsChildless, Ninst.pushB256, pushList, mstoreAt]
  exact frame.attributionInner_eq_nil_of_nonpayableChildless
    context hnonempty hmem hchildless

/-- The `name` view transports the allowance region: the attribution stream
is the frame's own record alone, its event is `none`, and the committed
storage is the entry storage. -/
theorem Exec.Frame.allowanceRegionEffect_of_name
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "name" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := name_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_name context hselector hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

/-! ## The `symbol` view arm -/

/-- The `symbol` view body is a childless line ending in `RETURN`, so an
authentic committed frame contributes no proper-descendant counted
records. -/
theorem Exec.Frame.attributionInner_eq_nil_of_symbol
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "symbol" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (symbolLine +++ Func.last .ret)) ∈ weth10Funcs dp := by
    rw [hselector]
    have hshape : nonpayable (symbolLine +++ Func.last .ret) =
        nonpayable symbol := rfl
    rw [hshape]
    simp [weth10Funcs]
  have hchildless : ∀ n ∈ symbolLine, NinstIsChildless n := by
    simp [symbolLine, NinstIsChildless, Ninst.pushB256, pushList, mstoreAt]
  exact frame.attributionInner_eq_nil_of_nonpayableChildless
    context hnonempty hmem hchildless

/-- The `symbol` view transports the allowance region. -/
theorem Exec.Frame.allowanceRegionEffect_of_symbol
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "symbol" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := symbol_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_symbol context hselector hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

/-! ## The `decimals` view arm -/

/-- The `decimals` view body is a childless line ending in `RETURN`, so an
authentic committed frame contributes no proper-descendant counted
records. -/
theorem Exec.Frame.attributionInner_eq_nil_of_decimals
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "decimals" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (returnWordLine 0x12 +++ Func.last .ret)) ∈
        weth10Funcs dp := by
    rw [hselector]
    have hshape : nonpayable (returnWordLine 0x12 +++ Func.last .ret) =
        nonpayable decimals := rfl
    rw [hshape]
    simp [weth10Funcs]
  have hchildless : ∀ n ∈ returnWordLine 0x12, NinstIsChildless n := by
    simp [returnWordLine, NinstIsChildless, Ninst.pushB256, mstoreAt,
      pushList]
  exact frame.attributionInner_eq_nil_of_nonpayableChildless
    context hnonempty hmem hchildless

/-- The `decimals` view transports the allowance region. -/
theorem Exec.Frame.allowanceRegionEffect_of_decimals
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "decimals" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := decimals_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_decimals context hselector hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

/-! ## The `PERMIT_TYPEHASH` view arm -/

/-- The `PERMIT_TYPEHASH` view body is a childless line ending in `RETURN`,
so an authentic committed frame contributes no proper-descendant counted
records. -/
theorem Exec.Frame.attributionInner_eq_nil_of_permitTypehash
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "PERMIT_TYPEHASH" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (returnWordLine PERMIT_TYPEHASH +++ Func.last .ret)) ∈
        weth10Funcs dp := by
    rw [hselector]
    have hshape :
        nonpayable (returnWordLine PERMIT_TYPEHASH +++ Func.last .ret) =
          nonpayable permitTypehash := rfl
    rw [hshape]
    simp [weth10Funcs]
  have hchildless : ∀ n ∈ returnWordLine PERMIT_TYPEHASH,
      NinstIsChildless n := by
    simp [returnWordLine, NinstIsChildless, Ninst.pushB256, mstoreAt,
      pushList]
  exact frame.attributionInner_eq_nil_of_nonpayableChildless
    context hnonempty hmem hchildless

/-- The `PERMIT_TYPEHASH` view transports the allowance region. -/
theorem Exec.Frame.allowanceRegionEffect_of_permitTypehash
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "PERMIT_TYPEHASH" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := permitTypehash_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_permitTypehash context hselector
      hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

/-! ## The `CALLBACK_SUCCESS` view arm -/

/-- The `CALLBACK_SUCCESS` view body is a childless line ending in
`RETURN`, so an authentic committed frame contributes no proper-descendant
counted records. -/
theorem Exec.Frame.attributionInner_eq_nil_of_callbackSuccess
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "CALLBACK_SUCCESS" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (returnWordLine CALLBACK_SUCCESS +++ Func.last .ret)) ∈
        weth10Funcs dp := by
    rw [hselector]
    have hshape :
        nonpayable (returnWordLine CALLBACK_SUCCESS +++ Func.last .ret) =
          nonpayable callbackSuccess := rfl
    rw [hshape]
    simp [weth10Funcs]
  have hchildless : ∀ n ∈ returnWordLine CALLBACK_SUCCESS,
      NinstIsChildless n := by
    simp [returnWordLine, NinstIsChildless, Ninst.pushB256, mstoreAt,
      pushList]
  exact frame.attributionInner_eq_nil_of_nonpayableChildless
    context hnonempty hmem hchildless

/-- The `CALLBACK_SUCCESS` view transports the allowance region. -/
theorem Exec.Frame.allowanceRegionEffect_of_callbackSuccess
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "CALLBACK_SUCCESS" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := callbackSuccess_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_callbackSuccess context hselector
      hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

/-! ## The `totalSupply` view arm -/

/-- The `totalSupply` view body is a childless line ending in `RETURN`, so
an authentic committed frame contributes no proper-descendant counted
records. -/
theorem Exec.Frame.attributionInner_eq_nil_of_totalSupply
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "totalSupply" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (totalSupplyLine +++ Func.last .ret)) ∈ weth10Funcs dp := by
    rw [hselector]
    have hshape : nonpayable (totalSupplyLine +++ Func.last .ret) =
        nonpayable totalSupply := rfl
    rw [hshape]
    simp [weth10Funcs]
  have hchildless : ∀ n ∈ totalSupplyLine, NinstIsChildless n := by
    simp [totalSupplyLine, pushFlashMintedSlot, NinstIsChildless,
      Ninst.pushB256, mstoreAt, pushList]
  exact frame.attributionInner_eq_nil_of_nonpayableChildless
    context hnonempty hmem hchildless

/-- The `totalSupply` view transports the allowance region. -/
theorem Exec.Frame.allowanceRegionEffect_of_totalSupply
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "totalSupply" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := totalSupply_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_totalSupply context hselector
      hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

/-! ## The `balanceOf` view arm -/

/-- The `balanceOf` view body is a childless line ending in `RETURN`, so an
authentic committed frame contributes no proper-descendant counted
records. -/
theorem Exec.Frame.attributionInner_eq_nil_of_balanceOf
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "balanceOf" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (balanceOfLine +++ Func.last .ret)) ∈ weth10Funcs dp := by
    rw [hselector]
    have hshape : nonpayable (balanceOfLine +++ Func.last .ret) =
        nonpayable balanceOfEndpoint := rfl
    rw [hshape]
    simp [weth10Funcs]
  have hchildless : ∀ n ∈ balanceOfLine, NinstIsChildless n := by
    simp [balanceOfLine, arg, cdl, NinstIsChildless, Ninst.pushB256,
      mstoreAt, pushList]
  exact frame.attributionInner_eq_nil_of_nonpayableChildless
    context hnonempty hmem hchildless

/-- The `balanceOf` view transports the allowance region. -/
theorem Exec.Frame.allowanceRegionEffect_of_balanceOf
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "balanceOf" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := balanceOf_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_balanceOf context hselector
      hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

/-! ## The `nonces` view arm -/

/-- The `nonces` view body is a childless line ending in `RETURN`, so an
authentic committed frame contributes no proper-descendant counted
records. -/
theorem Exec.Frame.attributionInner_eq_nil_of_nonces
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "nonces" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (noncesLine +++ Func.last .ret)) ∈ weth10Funcs dp := by
    rw [hselector]
    have hshape : nonpayable (noncesLine +++ Func.last .ret) =
        nonpayable nonces := rfl
    rw [hshape]
    simp [weth10Funcs]
  have hchildless : ∀ n ∈ noncesLine, NinstIsChildless n := by
    simp [noncesLine, arg, cdl, tagNonceKey, NinstIsChildless,
      Ninst.pushB256, mstoreAt, pushList]
  exact frame.attributionInner_eq_nil_of_nonpayableChildless
    context hnonempty hmem hchildless

/-- The `nonces` view transports the allowance region. -/
theorem Exec.Frame.allowanceRegionEffect_of_nonces
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "nonces" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := nonces_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_nonces context hselector hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

/-! ## The `flashMinted` view arm -/

/-- The `flashMinted` view body is a childless line ending in `RETURN`, so
an authentic committed frame contributes no proper-descendant counted
records. -/
theorem Exec.Frame.attributionInner_eq_nil_of_flashMinted
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "flashMinted" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (flashMintedLine +++ Func.last .ret)) ∈ weth10Funcs dp := by
    rw [hselector]
    have hshape : nonpayable (flashMintedLine +++ Func.last .ret) =
        nonpayable flashMinted := rfl
    rw [hshape]
    simp [weth10Funcs]
  have hchildless : ∀ n ∈ flashMintedLine, NinstIsChildless n := by
    simp [flashMintedLine, pushFlashMintedSlot, NinstIsChildless,
      Ninst.pushB256, mstoreAt, pushList]
  exact frame.attributionInner_eq_nil_of_nonpayableChildless
    context hnonempty hmem hchildless

/-- The `flashMinted` view transports the allowance region. -/
theorem Exec.Frame.allowanceRegionEffect_of_flashMinted
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = selector "flashMinted" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := flashMinted_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_flashMinted context hselector
      hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

/-! ## The `deploymentChainId` view arm -/

/-- The `deploymentChainId` view body is a childless line ending in
`RETURN`, so an authentic committed frame contributes no proper-descendant
counted records. -/
theorem Exec.Frame.attributionInner_eq_nil_of_deploymentChainId
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "deploymentChainId" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (deploymentChainIdLine dp +++ Func.last .ret)) ∈
        weth10Funcs dp := by
    rw [hselector]
    have hshape :
        nonpayable (deploymentChainIdLine dp +++ Func.last .ret) =
          nonpayable (deploymentChainId dp) := rfl
    rw [hshape]
    simp [weth10Funcs]
  have hchildless : ∀ n ∈ deploymentChainIdLine dp, NinstIsChildless n := by
    simp [deploymentChainIdLine, pushDeployWord, NinstIsChildless,
      Ninst.pushB256, mstoreAt, pushList]
  exact frame.attributionInner_eq_nil_of_nonpayableChildless
    context hnonempty hmem hchildless

/-- The `deploymentChainId` view transports the allowance region. -/
theorem Exec.Frame.allowanceRegionEffect_of_deploymentChainId
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "deploymentChainId" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := deploymentChainId_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_deploymentChainId context hselector
      hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

/-! ## The `DOMAIN_SEPARATOR` view arm -/

/-- Both executable arms of `DOMAIN_SEPARATOR` are childless, so an
authentic committed frame contributes no proper-descendant counted records;
the counted mirror of
`Exec.Frame.descendantFlowActions_eq_nil_of_domainSeparator`. -/
theorem Exec.Frame.attributionInner_eq_nil_of_domainSeparator
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "DOMAIN_SEPARATOR" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (domainSelectLine dp +++
        Func.branch (domainFreshLine +++ Func.last .ret)
          (domainCachedLine dp +++ Func.last .ret))) ∈ weth10Funcs dp := by
    rw [hselector]
    have hshape : nonpayable (domainSelectLine dp +++
        Func.branch (domainFreshLine +++ Func.last .ret)
          (domainCachedLine dp +++ Func.last .ret)) =
        nonpayable (domainSeparator dp) := rfl
    rw [hshape]
    simp [weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCounted context hnonempty hmem with
    ⟨wrapperCursor⟩
  rcases wrapperCursor.enterNonpayable with ⟨bodyCursor⟩
  rcases bodyCursor.peelChildlessLine
      (by simp [domainSelectLine, pushDeployWord, NinstIsChildless]) with
    ⟨branchCursor, -⟩
  rcases branchCursor.selectBranchSplit with
    ⟨⟨freshCursor⟩⟩ | ⟨⟨cachedCursor⟩⟩
  · rcases freshCursor.peelChildlessLine
        (by simp [domainFreshLine, calculateDomainSeparator,
          NinstIsChildless, Ninst.pushB256, mstoreAt, pushList]) with
      ⟨lastCursor, -⟩
    exact lastCursor.finishAttributionInner
  · rcases cachedCursor.peelChildlessLine
        (by simp [domainCachedLine, pushDeployWord, NinstIsChildless,
          Ninst.pushB256, mstoreAt, pushList]) with
      ⟨lastCursor, -⟩
    exact lastCursor.finishAttributionInner

/-- The `DOMAIN_SEPARATOR` view transports the allowance region. -/
theorem Exec.Frame.allowanceRegionEffect_of_domainSeparator
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "DOMAIN_SEPARATOR" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := domainSeparator_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_domainSeparator context hselector
      hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

/-! ## The `maxFlashLoan` view arm -/

/-- Both successful `maxFlashLoan` result arms are childless, so an
authentic committed frame contributes no proper-descendant counted records;
the counted mirror of
`Exec.Frame.descendantFlowActions_eq_nil_of_maxFlashLoan`. -/
theorem Exec.Frame.attributionInner_eq_nil_of_maxFlashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "maxFlashLoan" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (maxFlashLoanSelectLine +++
        Func.branch (returnWordLine 0 +++ Func.last .ret)
          (maxFlashLoanAvailableLine +++ Func.last .ret))) ∈
        weth10Funcs dp := by
    rw [hselector]
    have hshape : nonpayable (maxFlashLoanSelectLine +++
        Func.branch (returnWordLine 0 +++ Func.last .ret)
          (maxFlashLoanAvailableLine +++ Func.last .ret)) =
        nonpayable maxFlashLoan := rfl
    rw [hshape]
    simp [weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCounted context hnonempty hmem with
    ⟨wrapperCursor⟩
  rcases wrapperCursor.enterNonpayable with ⟨bodyCursor⟩
  rcases bodyCursor.peelChildlessLine
      (by simp [maxFlashLoanSelectLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨branchCursor, -⟩
  rcases branchCursor.selectBranchSplit with
    ⟨⟨zeroCursor⟩⟩ | ⟨⟨availCursor⟩⟩
  · rcases zeroCursor.peelChildlessLine
        (by simp [returnWordLine, NinstIsChildless, Ninst.pushB256,
          mstoreAt, pushList]) with
      ⟨lastCursor, -⟩
    exact lastCursor.finishAttributionInner
  · rcases availCursor.peelChildlessLine
        (by simp [maxFlashLoanAvailableLine, pushFlashMintedSlot,
          NinstIsChildless, Ninst.pushB256, mstoreAt, pushList]) with
      ⟨lastCursor, -⟩
    exact lastCursor.finishAttributionInner

/-- The `maxFlashLoan` view transports the allowance region. -/
theorem Exec.Frame.allowanceRegionEffect_of_maxFlashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "maxFlashLoan" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := maxFlashLoan_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_maxFlashLoan context hselector
      hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

/-! ## The `flashFee` view arm -/

/-- The successful `flashFee` arm is childless and the other source arm
enters the fixed `flashTokenError` reverter, so an authentic committed
frame contributes no proper-descendant counted records; the counted mirror
of `Exec.Frame.descendantFlowActions_eq_nil_of_flashFee`. -/
theorem Exec.Frame.attributionInner_eq_nil_of_flashFee
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "flashFee" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (flashFeeSelectLine +++
        Func.branch (returnWordLine 0 +++ Func.last .ret)
          (Func.call flashTokenErrorSlot))) ∈ weth10Funcs dp := by
    rw [hselector]
    have hshape : nonpayable (flashFeeSelectLine +++
        Func.branch (returnWordLine 0 +++ Func.last .ret)
          (Func.call flashTokenErrorSlot)) =
        nonpayable flashFee := rfl
    rw [hshape]
    simp [weth10Funcs]
  rcases frame.compiledSelectorBodyCursorCounted context hnonempty hmem with
    ⟨wrapperCursor⟩
  rcases wrapperCursor.enterNonpayable with ⟨bodyCursor⟩
  rcases bodyCursor.peelChildlessLine
      (by simp [flashFeeSelectLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨branchCursor, -⟩
  rcases branchCursor.selectBranchSplit with
    ⟨⟨successCursor⟩⟩ | ⟨⟨errorCursor⟩⟩
  · rcases successCursor.peelChildlessLine
        (by simp [returnWordLine, NinstIsChildless, Ninst.pushB256,
          mstoreAt, pushList]) with
      ⟨lastCursor, -⟩
    exact lastCursor.finishAttributionInner
  · exfalso
    cases errorCursor.run with
    | call hget _hroom _hburn hbody =>
        rw [show ((weth10 dp).main :: weth10Aux)[flashTokenErrorSlot]? =
            some flashTokenError from rfl] at hget
        injection hget with hf
        subst hf
        exact Func.not_run_revWith (Func.Run.of_runCompiled hbody)

/-- The `flashFee` view transports the allowance region. -/
theorem Exec.Frame.allowanceRegionEffect_of_flashFee
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "flashFee" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  obtain ⟨hstor, hcode⟩ :
      Devm.getStor frame.post = Devm.getStor frame.pre ∧
        Devm.getCode frame.pre ca = Devm.getCode frame.post ca := by
    rcases frame with ⟨pc, e, pre, out, run, committed⟩
    cases out with
    | error _ => simp [Execution.commits] at committed
    | ok post =>
        have hpc : pc = 0 := context.root.1
        subst hpc
        have heffect := flashFee_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hselector
          hnonempty
        exact ⟨heffect.2.2.1, (congrFun heffect.2.2.2.2 ca).symm⟩
  exact frame.allowanceRegionEffect_of_storageInvariantView context
    hselector hnonempty
    (frame.attributionInner_eq_nil_of_flashFee context hselector
      hnonempty)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hstor hcode

end Weth10

end Blanc

