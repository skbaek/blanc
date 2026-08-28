import Blanc.Weth10AllowanceArmsSpend

/-!
The direct-redemption arms of the allowance-region transport.

`withdraw`, `withdrawTo`, and the zero-recipient `transfer` all debit the
caller's balance, emit, and then perform one external value `CALL` whose
recipient may reenter WETH10.  Unlike every earlier arm, the frame's
attribution stream is therefore *not* its own record alone: the committed
send child contributes its own counted stream between the frame's record
and the frame's end.  This module walks the original retained execution at
the counted-cursor altitude up to the `CALL`, crosses the spawn edge while
identifying its counted label with the retained child's attribution
stream, transports the allowance region across the child through the
`ForallDeeperAt` recursion hypothesis, and closes the trailing guard as a
childless suffix.  All three selectors miss every allowance branch of
`frameAllowanceEvent`, so the frame's own record replays transparently.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace Weth10

/-! ## Allowance transport across one retained child message

The counted mirror of
`ProcessMessageTrace.storageSegmentDelta_of_forallDeeperAt`: a retained
call-message trace transports the allowance region by exactly its
retained child's attribution stream, consuming `lift_core`'s strong-depth
hypothesis at the `Exec.CoreAllowanceSound` instantiation. -/

theorem ProcessMessageTrace.allowanceRegionDelta_of_forallDeeperAt
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {msg : Msg} {post parent : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hparent : parent.state = msg.benv.state)
    (hdepth : msg.depth < depth)
    (hcode : some (parent.getCode ca).toList =
      Prog.compile (weth10 dp))
    (htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp))
    (htargetDirect : msg.currentTarget = ca →
      msg.codeAddress = some ca)
    (hdeeper : ForallDeeperAt depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca parent post
      (trace.retained.attributionStream dp ca) := by
  rcases trace with ⟨slot, retained, hprocess⟩
  cases retained with
  | none =>
      have hstorage : Devm.getStor parent ca = Devm.getStor post ca := by
        rcases ProcessMessage.none_ok_state_cases hprocess with
          hrollback | ⟨benv, htransfer, hpost⟩
        · exact congrArg (fun state : State => state.getStor ca)
            (hparent.trans hrollback.symm)
        · change msg.benvAfterTransfer = .ok benv at htransfer
          exact (congrArg (fun state : State => state.getStor ca)
              hparent).trans <|
            (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
              (congrArg (fun state : State => state.getStor ca) hpost).symm
      have hcodeEq : parent.getCode ca = post.getCode ca := by
        rcases ProcessMessage.none_ok_state_cases hprocess with
          hrollback | ⟨benv, htransfer, hpost⟩
        · exact congrArg (fun state : State => state.getCode ca)
            (hparent.trans hrollback.symm)
        · change msg.benvAfterTransfer = .ok benv at htransfer
          exact (congrArg (fun state : State => state.getCode ca)
              hparent).trans <|
            (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
              (congrArg (fun state : State => state.getCode ca) hpost).symm
      exact AllowanceRegionEffect.of_getStorCode_eq hstorage hcodeEq
  | @some pc sevm pre out run =>
      have henter : (Frame.ofCall msg).enter =
          .run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hprocess).1
      rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hevm⟩
      simp only [Frame.ofCall] at htransfer hevm
      have hpreState : pre.state = benv.state := by
        have component := congrArg (fun evm : Evm => evm.dyna.state) hevm
        change pre.state = (initEvm (msg.withBenv benv)).dyna.state
        exact component
      have hsevm : sevm = initSevm (msg.withBenv benv) :=
        congrArg (fun evm : Evm => evm.sta) hevm
      have hpc : pc = 0 := by
        simpa [initEvm] using congrArg (fun evm : Evm => evm.pc) hevm
      have hmemory : pre.memory = Mem.empty := by
        have component := congrArg (fun evm : Evm => evm.dyna.memory) hevm
        change pre.memory = (initEvm (msg.withBenv benv)).dyna.memory
        simpa [initEvm, initDevm, Msg.withBenv] using component
      have hentryStorage : Devm.getStor parent ca =
          Devm.getStor pre ca := by
        exact (congrArg (fun state : State => state.getStor ca)
            hparent).trans <|
          (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
            (congrArg (fun state : State => state.getStor ca)
              hpreState).symm
      have hentryCodeEq : parent.getCode ca = pre.getCode ca := by
        exact (congrArg (fun state : State => state.getCode ca)
            hparent).trans <|
          (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
            (congrArg (fun state : State => state.getCode ca)
              hpreState).symm
      have hentryCode : some (pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        calc
          some (pre.getCode ca).toList =
              some (benv.state.getCode ca).toList := by
            change some (pre.state.getCode ca).toList = _
            rw [hpreState]
          _ = some (msg.benv.state.getCode ca).toList := by
            rw [benvAfterTransfer_ok_getCode htransfer ca]
          _ = some (parent.getCode ca).toList := by
            change some (msg.benv.state.getCode ca).toList =
              some (parent.state.getCode ca).toList
            rw [hparent]
          _ = _ := hcode
      have hat : Prog.At (weth10 dp) ca pc sevm pre := by
        refine ⟨hentryCode, ?_⟩
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        refine ⟨?_, hpc⟩
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using htargetCode hmsgTarget
      have hdirect : sevm.currentTarget = ca →
          sevm.codeAddress = some ca := by
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using htargetDirect hmsgTarget
      by_cases hcommit : Execution.commits out = true
      · cases out with
        | error error => simp [Execution.commits] at hcommit
        | ok raw =>
            have hchildDepth : sevm.depth < depth := by
              rw [hsevm]
              simpa [initSevm, Msg.withBenv] using hdepth
            have hcore := hdeeper pc sevm pre (.ok raw) run
              hchildDepth hat
            have childEffect := hcore run hcommit hat
              (fun htarget => ⟨⟨hpc, hmemory⟩, hdirect htarget⟩)
            have hpostState : post.state = raw.state :=
              ProcessMessage.ok_state_eq_committedPost hprocess hcommit
            have hpostStorage : Devm.getStor raw ca =
                Devm.getStor post ca :=
              congrArg (fun state : State => state.getStor ca)
                hpostState.symm
            have hpostCode : raw.getCode ca = post.getCode ca :=
              congrArg (fun state : State => state.getCode ca)
                hpostState.symm
            exact (by
              simpa only [List.nil_append, List.append_nil,
                RetainedXlot.attributionStream] using
                (AllowanceRegionEffect.of_getStorCode_eq
                    hentryStorage hentryCodeEq).append
                  (childEffect.append
                    (AllowanceRegionEffect.of_getStorCode_eq
                      hpostStorage hpostCode)))
      · have hactions : Exec.attributionStream dp ca run = [] :=
          Exec.attributionStream_eq_nil_of_not_commits run hcommit
        have hpostState : post.state = msg.benv.state :=
          ProcessMessage.ok_state_eq_of_not_commits hprocess hcommit
        have hstorage : Devm.getStor parent ca = Devm.getStor post ca :=
          congrArg (fun state : State => state.getStor ca)
            (hparent.trans hpostState.symm)
        have hcodeEq : parent.getCode ca = post.getCode ca :=
          congrArg (fun state : State => state.getCode ca)
            (hparent.trans hpostState.symm)
        have hstream : RetainedXlot.attributionStream dp ca
            (RetainedXlot.some run) = [] := by
          simpa only [RetainedXlot.attributionStream] using hactions
        rw [hstream]
        exact AllowanceRegionEffect.of_getStorCode_eq hstorage hcodeEq

/-! ## Closing the post-call guard suffix

After the external value `CALL` resumes with a success word, the
remaining body is the `ISZERO` test, the send-error reverter branch, and
a childless terminal continuation.  Packaged over the continuation
derivation as its own retained frame, the suffix contributes no counted
records and no storage writes. -/

theorem Exec.tailGuard_attributionInner_storage
    {dp : DeployParams} {ca : Adr}
    {fsevm : Sevm} {pcT : Nat} {midD final : Devm}
    {table : List (Nat × Func)}
    {successLine : Line} {successLast : Linst}
    {errSlot : Nat} {_errReason : String} {rest : Stack}
    (next : Exec pcT fsevm midD (.ok final))
    (fcommitted : Execution.commits (.ok final) = true)
    (htail : Func.RunCompiled ((weth10 dp).main :: weth10Aux) fsevm midD
      (Ninst.iszero :::
        ((.call errSlot) <?> (successLine +++ Func.last successLast)))
      final)
    (hsub : subcode fsevm.code.toList pcT
      (Func.compile table pcT
        (Ninst.iszero :::
          ((.call errSlot) <?> (successLine +++ Func.last successLast)))))
    (hbound : noPushBefore fsevm.code pcT 32 = true)
    (hstackOne : midD.stack = (1 : B256) :: rest)
    (hsuccessChildless : ∀ n ∈ successLine, NinstIsChildless n)
    (hsuccessStor : Func.Inv Devm.getStor Devm.getStor
      (successLine +++ Func.last successLast)) :
    Exec.attributionInner dp ca next = [] ∧
    Devm.getStor midD = Devm.getStor final := by
  let tailCursor :
      Blanc.Weth10.Exec.Frame.CountedCursor
        (frame := ⟨pcT, fsevm, midD, .ok final, next, fcommitted⟩) dp ca
        ((weth10 dp).main :: weth10Aux) table
        (Ninst.iszero :::
          ((.call errSlot) <?> (successLine +++ Func.last successLast)))
        final :=
    ⟨pcT, midD, next, ⟨[], Exec.Deriv.ParentPrefixActions.refl _⟩,
      Exec.Deriv.ParentPrefixCounted.refl _, htail, hsub, hbound⟩
  rcases tailCursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨branchCursor, hiszeroRun⟩
  have hp0 : [(1 : B256)] <<+ midD.stack := by
    rw [hstackOne]
    exact pref_append [(1 : B256)] rest
  have hpIso : ((1 : B256) =? 0) :: [] <<+ branchCursor.pre.stack :=
    prefix_of_iszero hiszeroRun hp0
  have hne10 : (1 : B256) ≠ 0 := fun h => B256.zero_ne_one h.symm
  rw [show ((1 : B256) =? 0) = 0 from by simp [B256.eqCheck, hne10]]
    at hpIso
  rcases branchCursor.selectBranchZeroSilent hpIso with
    ⟨successCursor, _hsuccStack, hbranchSilent⟩
  rcases successCursor.peelChildlessLine hsuccessChildless with
    ⟨lastCursor, _hsuccessRun⟩
  have hinnerNil : Exec.attributionInner dp ca next = [] :=
    lastCursor.finishAttributionInner
  have hstorIso : midD.state = branchCursor.pre.state :=
    Ninst.Hinv.inv (f := Devm.state) hiszeroRun
  have hstorSuccess : Devm.getStor successCursor.pre =
      Devm.getStor final :=
    Func.of_inv Devm.getStor Devm.getStor hsuccessStor
      (Func.Run.of_runCompiled successCursor.run)
  refine ⟨hinnerNil, ?_⟩
  calc Devm.getStor midD
      = Devm.getStor branchCursor.pre :=
        funext (getStor_eq_of_state_eq hstorIso)
    _ = Devm.getStor successCursor.pre :=
        funext (getStor_eq_of_state_eq hbranchSilent.state)
    _ = Devm.getStor final := hstorSuccess

/-! ## The success continuation's own allowance closer

The redemption walk is also run with a *child-calling* success continuation —
the zero-recipient `transferAndCall` runs the ERC-677 callback behind the
redemption send — so the continuation cannot be closed as a childless suffix.
It is instead closed by the caller, at the continuation re-rooted as its own
frame.  A `CountedCursor` is data and cannot be quantified existentially
inside a `Prop`, so the closer receives the raw counted data — program
counter, entry machine, retained derivation, compiled run and code-slice
witnesses — and rebuilds its own cursor.  The three side conditions are the
memory frame and installed-code witness a child-calling continuation needs;
a childless continuation ignores them. -/

/-- What a redemption walk demands of its success continuation: whatever the
continuation's own proper-descendant counted stream turns out to be,
replaying it over the continuation's entry storage reproduces the frame's
committed post state on every tagged allowance key. -/
def SuccessAllowanceCloser (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) (img : Bytes) (success : Func) : Prop :=
  ∀ (entryPc : Nat) (entry : Devm)
    (continuation : Exec entryPc frame.sevm entry frame.out),
    Func.RunCompiled ((weth10 dp).main :: weth10Aux) frame.sevm entry
      success frame.post →
    subcode frame.sevm.code.toList entryPc
      (Func.compile (table 0 ((weth10 dp).main :: weth10Aux)) entryPc
        success) →
    noPushBefore frame.sevm.code entryPc 32 = true →
    Mem.Wf entry.memory →
    Mem.Reads entry.memory img →
    some (entry.getCode ca).toList = Prog.compile (weth10 dp) →
    ∀ key, InRegion .allowance key →
      (Devm.getStor frame.post ca).get key =
        applyAllowanceLedger (Devm.getStor entry ca)
          (Exec.attributionInner dp ca continuation) key

/-- A childless success continuation ending in a terminal instruction closes
the walk from its storage invariance alone: it retains no counted record, so
the replayed ledger is empty. -/
theorem successAllowanceCloser_of_childless
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {img : Bytes}
    {successLine : Line} {successLast : Linst}
    (hchildless : ∀ n ∈ successLine, NinstIsChildless n)
    (hstor : Func.Inv Devm.getStor Devm.getStor
      (successLine +++ Func.last successLast)) :
    SuccessAllowanceCloser dp ca frame img
      (successLine +++ Func.last successLast) := by
  intro entryPc entry continuation hrun hsub hbound _hwf _hreads _hcode
    key _hkey
  let suffixCursor :
      Blanc.Weth10.Exec.Frame.CountedCursor
        (frame := ⟨entryPc, frame.sevm, entry, frame.out, continuation,
          frame.committed⟩) dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (successLine +++ Func.last successLast) frame.post :=
    ⟨entryPc, entry, continuation,
      ⟨[], Exec.Deriv.ParentPrefixActions.refl _⟩,
      Exec.Deriv.ParentPrefixCounted.refl _, hrun, hsub, hbound⟩
  rcases suffixCursor.peelChildlessLine hchildless with ⟨lastCursor, -⟩
  have hnil : Exec.attributionInner dp ca continuation = [] :=
    lastCursor.finishAttributionInner
  have hstorEq : Devm.getStor entry = Devm.getStor frame.post :=
    Func.of_inv Devm.getStor Devm.getStor hstor
      (Func.Run.of_runCompiled hrun)
  rw [hnil, applyAllowanceLedger_nil, ← congrFun hstorEq ca]

/-- The generalized closer for the redemption success guard: the post-`CALL`
`ISZERO` test and the send-error branch are childless scaffolding that
neither retains a counted record nor moves storage, so the whole guard
suffix's allowance effect is the success continuation's own. -/
theorem Exec.tailGuardAllowanceStorage
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {pcT : Nat} {midD : Devm} {success : Func}
    {errSlot : Nat} {rest : Stack} {img : Bytes}
    (next : Exec pcT frame.sevm midD frame.out)
    (htail : Func.RunCompiled ((weth10 dp).main :: weth10Aux) frame.sevm midD
      (Ninst.iszero ::: ((.call errSlot) <?> success)) frame.post)
    (hsub : subcode frame.sevm.code.toList pcT
      (Func.compile (table 0 ((weth10 dp).main :: weth10Aux)) pcT
        (Ninst.iszero ::: ((.call errSlot) <?> success))))
    (hbound : noPushBefore frame.sevm.code pcT 32 = true)
    (hstackOne : midD.stack = (1 : B256) :: rest)
    (hwf : Mem.Wf midD.memory)
    (hreads : Mem.Reads midD.memory img)
    (hcode : some (midD.getCode ca).toList = Prog.compile (weth10 dp))
    (hcloser : SuccessAllowanceCloser dp ca frame img success) :
    ∀ key, InRegion .allowance key →
      (Devm.getStor frame.post ca).get key =
        applyAllowanceLedger (Devm.getStor midD ca)
          (Exec.attributionInner dp ca next) key := by
  let tailCursor :
      Blanc.Weth10.Exec.Frame.CountedCursor
        (frame := ⟨pcT, frame.sevm, midD, frame.out, next,
          frame.committed⟩) dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (Ninst.iszero ::: ((.call errSlot) <?> success)) frame.post :=
    ⟨pcT, midD, next, ⟨[], Exec.Deriv.ParentPrefixActions.refl _⟩,
      Exec.Deriv.ParentPrefixCounted.refl _, htail, hsub, hbound⟩
  rcases tailCursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨branchCursor, hiszeroRun⟩
  have hp0 : [(1 : B256)] <<+ midD.stack := by
    rw [hstackOne]
    exact pref_append [(1 : B256)] rest
  have hpIso : ((1 : B256) =? 0) :: [] <<+ branchCursor.pre.stack :=
    prefix_of_iszero hiszeroRun hp0
  have hne10 : (1 : B256) ≠ 0 := fun h => B256.zero_ne_one h.symm
  rw [show ((1 : B256) =? 0) = 0 from by simp [B256.eqCheck, hne10]]
    at hpIso
  rcases branchCursor.selectBranchZeroSilent hpIso with
    ⟨successCursor, _hsuccStack, hbranchSilent⟩
  have hstate : midD.state = successCursor.pre.state :=
    (Ninst.Hinv.inv (f := Devm.state) hiszeroRun).trans hbranchSilent.state
  have hmemory : midD.memory = successCursor.pre.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) hiszeroRun).trans hbranchSilent.memory
  have hclosed := hcloser successCursor.pc successCursor.pre
    successCursor.current successCursor.run successCursor.codeSlice
    successCursor.codeBoundary (by rw [← hmemory]; exact hwf)
    (by rw [← hmemory]; exact hreads)
    (by rw [← getCode_eq_of_state_eq hstate ca]; exact hcode)
  have hsplit := successCursor.countedPrefix.descendantCounted_eq
  change Exec.attributionInner dp ca next =
    [] ++ Exec.attributionInner dp ca successCursor.current at hsplit
  intro key hkey
  rw [hsplit, List.nil_append,
    applyAllowanceLedger_congr
      (congrArg (fun s : Stor => s.get key)
        (getStor_eq_of_state_eq hstate ca))]
  exact hclosed key hkey

/-! ## Local copies of the compiled redemption body

`Weth10HolderFlowCompiled` keeps its redemption-body decomposition private,
so this module re-declares the pieces the three redemption selectors share,
byte for byte. -/

private def redeemCheckLine (amountArg : B256) : Line :=
  loadCallerBalanceAmount amountArg ++ balanceTooSmall

private def redeemEventTail (amountArg : B256) : Line :=
  arg amountArg ++ [pushB256 0] ++ emitTransfer ++ [swap 0, pop]

def redeemSendToCallerPrefix : Line :=
  pushList [0, 0, 0, 0] ++ [swap 3, caller, gas]

def redeemSendToArgPrefix (k : B256) : Line :=
  pushList [0, 0, 0, 0] ++ [swap 3] ++ arg k ++ [gas]

/-- The shared caller-owned redemption body: balance guard, debit, burn
event, send-operand prefix, external value `CALL`, success guard. -/
def redeemBody (amountArg : B256) (sendPrefix : Line)
    (success : Func) : Func :=
  redeemCheckLine amountArg +++
  ((.call burnBalanceErrorSlot) <?>
    (debitLoadedBalance +++
      caller ::: redeemEventTail amountArg +++
      sendPrefix +++
      Ninst.call ::: Ninst.iszero :::
      ((.call ethTransferErrorSlot) <?> success)))

private theorem withdraw_eq_redeemBody :
    withdraw = redeemBody 0 redeemSendToCallerPrefix (Func.last .stop) := rfl

private theorem withdrawTo_eq_redeemBody :
    withdrawTo = redeemBody 1 (redeemSendToArgPrefix 0) (Func.last .stop) :=
  rfl

private theorem transferZeroThen_eq_redeemBody (success : Func) :
    transferZeroThen success =
      redeemBody 1 redeemSendToCallerPrefix success := rfl

/-- The caller-send operand walk shared by the redemption selectors. -/
theorem redeemSendToCallerPrefix_effect
    {e : Sevm} {pre callPre : Devm} {value : B256} {tail : Stack}
    (hstack : value :: tail <<+ pre.stack)
    (run : Line.Run e pre redeemSendToCallerPrefix callPre) :
    ValueCallOperandPrefix e pre callPre value e.caller.toB256 tail := by
  unfold redeemSendToCallerPrefix pushList at run
  simp only [List.map] at run
  rcases Line.of_run_cons run with ⟨s₁, hpush₁, run₁⟩
  have hp₁ : (0 : B256) :: value :: tail <<+ s₁.stack :=
    prefix_of_push (of_run_pushB256 hpush₁) hstack
  rcases Line.of_run_cons run₁ with ⟨s₂, hpush₂, run₂⟩
  have hp₂ : (0 : B256) :: 0 :: value :: tail <<+ s₂.stack :=
    prefix_of_push (of_run_pushB256 hpush₂) hp₁
  rcases Line.of_run_cons run₂ with ⟨s₃, hpush₃, run₃⟩
  have hp₃ : (0 : B256) :: 0 :: 0 :: value :: tail <<+ s₃.stack :=
    prefix_of_push (of_run_pushB256 hpush₃) hp₂
  rcases Line.of_run_cons run₃ with ⟨s₄, hpush₄, run₄⟩
  have hp₄ : (0 : B256) :: 0 :: 0 :: 0 :: value :: tail <<+ s₄.stack :=
    prefix_of_push (of_run_pushB256 hpush₄) hp₃
  rcases Line.of_run_cons run₄ with ⟨s₅, hswap, run₅⟩
  have hswapCore : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: value :: tail)
      (value :: 0 :: 0 :: 0 :: 0 :: tail) :=
    Stack.swapCore_succ (Stack.swapCore_succ
      (Stack.swapCore_succ Stack.swapCore_zero))
  have hp₅ : value :: 0 :: 0 :: 0 :: 0 :: tail <<+ s₅.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp₄
  rcases Line.of_run_cons run₅ with ⟨s₆, hcaller, run₆⟩
  have hp₆ : e.caller.toB256 :: value :: 0 :: 0 :: 0 :: 0 :: tail <<+
      s₆.stack := prefix_of_push (of_run_caller hcaller) hp₅
  rcases Line.of_run_cons run₆ with ⟨last, hgas, hnil⟩
  cases hnil
  rcases of_run_gas hgas with ⟨gasWord, hpushGas⟩
  exact ⟨⟨gasWord, prefix_of_push hpushGas hp₆⟩,
    Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run,
    Line.of_inv Devm.getCode (by line_inv) run,
    Line.of_inv Devm.memory (by line_inv) run,
    Line.of_inv Devm.logs (by line_inv) run,
    Line.of_inv Devm.output (by line_inv) run⟩

/-- The argument-send operand walk shared by the redemption selectors. -/
theorem redeemSendToArgPrefix_effect (k : B256)
    {e : Sevm} {pre callPre : Devm} {value : B256} {tail : Stack}
    (hstack : value :: tail <<+ pre.stack)
    (run : Line.Run e pre (redeemSendToArgPrefix k) callPre) :
    ValueCallOperandPrefix e pre callPre value (Sevm.argWord e k) tail := by
  unfold redeemSendToArgPrefix pushList at run
  simp only [List.map] at run
  rcases Line.of_run_cons run with ⟨s₁, hpush₁, run₁⟩
  have hp₁ : (0 : B256) :: value :: tail <<+ s₁.stack :=
    prefix_of_push (of_run_pushB256 hpush₁) hstack
  rcases Line.of_run_cons run₁ with ⟨s₂, hpush₂, run₂⟩
  have hp₂ : (0 : B256) :: 0 :: value :: tail <<+ s₂.stack :=
    prefix_of_push (of_run_pushB256 hpush₂) hp₁
  rcases Line.of_run_cons run₂ with ⟨s₃, hpush₃, run₃⟩
  have hp₃ : (0 : B256) :: 0 :: 0 :: value :: tail <<+ s₃.stack :=
    prefix_of_push (of_run_pushB256 hpush₃) hp₂
  rcases Line.of_run_cons run₃ with ⟨s₄, hpush₄, run₄⟩
  have hp₄ : (0 : B256) :: 0 :: 0 :: 0 :: value :: tail <<+ s₄.stack :=
    prefix_of_push (of_run_pushB256 hpush₄) hp₃
  rcases Line.of_run_cons run₄ with ⟨s₅, hswap, run₅⟩
  have hswapCore : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: value :: tail)
      (value :: 0 :: 0 :: 0 :: 0 :: tail) :=
    Stack.swapCore_succ (Stack.swapCore_succ
      (Stack.swapCore_succ Stack.swapCore_zero))
  have hp₅ : value :: 0 :: 0 :: 0 :: 0 :: tail <<+ s₅.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp₄
  rcases of_run_append (arg k) run₅ with ⟨s₆, harg, run₆⟩
  have hp₆ : Sevm.argWord e k :: value :: 0 :: 0 :: 0 :: 0 :: tail <<+
      s₆.stack := prefix_of_arg hp₅ harg
  rcases Line.of_run_cons run₆ with ⟨last, hgas, hnil⟩
  cases hnil
  rcases of_run_gas hgas with ⟨gasWord, hpushGas⟩
  exact ⟨⟨gasWord, prefix_of_push hpushGas hp₆⟩,
    Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run,
    Line.of_inv Devm.getCode (by line_inv) run,
    Line.of_inv Devm.memory (by line_inv) run,
    Line.of_inv Devm.logs (by line_inv) run,
    Line.of_inv Devm.output (by line_inv) run⟩

/-! ## Identifying the counted label of a source `CALL` -/

/-! ## The shared caller-owned redemption walk

The redemption selectors differ only in their amount argument, their
send-operand prefix, and their success continuation.  This walk crosses the
shared body once: the guarded debit writes a single address-shaped balance
key, the external value `CALL` is identified with a retained child message
whose allowance-region delta is supplied by the recursion hypothesis, and
the trailing success guard is handed to the caller's continuation closer.
The continuation is an arbitrary `Func`: `withdraw`, `withdrawTo` and the
zero-recipient `transfer` end in a childless terminal suffix, while the
zero-recipient `transferAndCall` runs the ERC-677 callback there. -/

theorem Exec.Frame.CountedCursor.redeemAllowanceRegionStorage
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {amountArg target : B256} {sendPrefix : Line}
    {success : Func} {img : Bytes}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (redeemBody amountArg sendPrefix success) frame.post)
    (htarget : frame.sevm.currentTarget = ca)
    (hstack : [] <<+ cursor.pre.stack)
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img)
    (hcursorCode : some (cursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hsendChildless : ∀ n ∈ sendPrefix, NinstIsChildless n)
    (hsend : ∀ {sendPre callPre : Devm} {value : B256} {tail : Stack},
      value :: tail <<+ sendPre.stack →
      Line.Run frame.sevm sendPre sendPrefix callPre →
      ValueCallOperandPrefix frame.sevm sendPre callPre value target tail)
    (hcloser : SuccessAllowanceCloser dp ca frame
      (Bytes.writeAt img 0 (Sevm.argWord frame.sevm amountArg).toBytes)
      success)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    ∀ key, InRegion .allowance key →
      (Devm.getStor frame.post ca).get key =
        applyAllowanceLedger (Devm.getStor cursor.pre ca)
          (Exec.attributionInner dp ca frame.run) key := by
  rcases frame with ⟨fpc, e, fpre, fout, frun, fcommitted⟩
  cases fout with
  | error err => simp [Execution.commits] at fcommitted
  | ok fpost =>
      intro key hkey
      have htargetE : e.currentTarget = ca := htarget
      have hkeyNe : e.caller.toB256 ≠ key :=
        (allowanceRegion_ne_validAdr hkey ⟨e.caller, rfl⟩).symm
      -- the guarded balance check
      unfold redeemBody at cursor
      rcases cursor.peelChildlessLine (line := redeemCheckLine amountArg)
          (by simp [redeemCheckLine, loadCallerBalanceAmount,
            balanceTooSmall, arg, cdl, NinstIsChildless,
            Ninst.pushB256]) with
        ⟨branchCursor, hcheck⟩
      unfold redeemCheckLine at hcheck
      rcases of_run_append (loadCallerBalanceAmount amountArg) hcheck with
        ⟨afterLoad, hload, hguard⟩
      rcases prefix_of_loadCallerBalanceAmount hstack hload with
        ⟨balance, _hbalance, hloadStack⟩
      have hguardStack : (balance <? Sevm.argWord e amountArg) :: balance ::
          Sevm.argWord e amountArg :: e.caller.toB256 :: [] <<+
            branchCursor.pre.stack :=
        prefix_of_balanceTooSmall hloadStack hguard
      rcases branchCursor.selectBranchLeftWithBurn
          (not_run_call_revWith (burnBalanceError_lookup dp)) with
        ⟨successCursor, hbalancePopBy⟩
      have hbalancePop := Devm.PopBurn.of_popBurnBy hbalancePopBy
      have hpopStack := hbalancePop.stack
      simp only [Stack.Pop, Split, List.nil_append,
        List.cons_append] at hpopStack
      rw [hpopStack] at hguardStack
      have hflag : (balance <? Sevm.argWord e amountArg) = 0 :=
        pref_head_unique hguardStack (pref_append [0] successCursor.pre.stack)
      rw [hflag] at hguardStack
      have hsuccessStack : balance :: Sevm.argWord e amountArg ::
          e.caller.toB256 :: [] <<+ successCursor.pre.stack :=
        cons_pref_cons_inv hguardStack
      have hcheckStor : Devm.getStor cursor.pre =
          Devm.getStor successCursor.pre :=
        (Line.of_inv Devm.getStor (by line_inv) hload).trans
          ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
            (PopBurn.Inv.inv hbalancePop))
      have hcheckCode : Devm.getCode cursor.pre =
          Devm.getCode successCursor.pre :=
        (Line.of_inv Devm.getCode (by line_inv) hload).trans
          ((Line.of_inv Devm.getCode (by line_inv) hguard).trans
            (funext (getCode_eq_of_state_eq hbalancePop.state)))
      have hcheckMem : cursor.pre.memory = successCursor.pre.memory :=
        (Line.of_inv Devm.memory (by line_inv) hload).trans
          ((Line.of_inv Devm.memory (by line_inv) hguard).trans
            hbalancePop.memory)
      -- the caller-key debit
      rcases successCursor.peelChildlessLine (line := debitLoadedBalance)
          (by simp [debitLoadedBalance, NinstIsChildless]) with
        ⟨afterDebitCursor, hdebit⟩
      have hdebitCode : Devm.getCode successCursor.pre =
          Devm.getCode afterDebitCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) hdebit
      have hdebitMem : successCursor.pre.memory =
          afterDebitCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) hdebit
      unfold debitLoadedBalance at hdebit
      rcases Line.of_run_cons hdebit with ⟨d1, hsub, hdebit1⟩
      have hpD1 : (balance - Sevm.argWord e amountArg) ::
          e.caller.toB256 :: [] <<+ d1.stack :=
        prefix_of_sub hsub hsuccessStack
      rcases Line.of_run_cons hdebit1 with ⟨d2, hswap, hdebit2⟩
      have hswapCoreD : Stack.Swap (0 : Fin 16).val
          [balance - Sevm.argWord e amountArg, e.caller.toB256]
          [e.caller.toB256, balance - Sevm.argWord e amountArg] :=
        Stack.swapCore_zero
      have hpD2 : e.caller.toB256 ::
          (balance - Sevm.argWord e amountArg) :: [] <<+ d2.stack :=
        Stack.prefix_of_swap hswapCoreD (of_run_swap hswap) hpD1
      rcases Line.of_run_cons hdebit2 with ⟨d3, hstore, hnilD⟩
      cases hnilD
      have hsetDebit : Devm.getStor afterDebitCursor.pre e.currentTarget =
          (Devm.getStor d2 e.currentTarget).set e.caller.toB256
            (balance - Sevm.argWord e amountArg) :=
        sstore_getStor_set hstore hpD2
      have hdebitStorPre : Devm.getStor successCursor.pre =
          Devm.getStor d2 :=
        (Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hsub Line.Run.nil)).trans
          (Line.of_inv Devm.getStor (by line_inv)
            (Line.Run.cons hswap Line.Run.nil))
      -- the burn event and the send operands
      rcases afterDebitCursor.peelChildlessLine
          (line := caller :: redeemEventTail amountArg)
          (by simp [redeemEventTail, arg, cdl, emitTransfer,
            Blanc.transferFromLog, mstoreAt, logWith, NinstIsChildless,
            Ninst.pushB256]) with
        ⟨sendCursor, heventRun⟩
      rcases Line.of_run_cons heventRun with ⟨eventPre, hcallerRun, htailRun⟩
      have hcallerStor : Devm.getStor afterDebitCursor.pre =
          Devm.getStor eventPre :=
        Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hcallerRun Line.Run.nil)
      have hcallerCode : Devm.getCode afterDebitCursor.pre =
          Devm.getCode eventPre :=
        Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hcallerRun Line.Run.nil)
      have hcallerMem : afterDebitCursor.pre.memory = eventPre.memory :=
        Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons hcallerRun Line.Run.nil)
      have hownerStack : e.caller.toB256 :: [] <<+ eventPre.stack :=
        prefix_of_push (of_run_caller hcallerRun) nil_pref
      have hwfEvent : Mem.Wf eventPre.memory := by
        rw [← hcallerMem, ← hdebitMem, ← hcheckMem]
        exact hwf
      have hreadsEvent : Mem.Reads eventPre.memory img := by
        rw [← hcallerMem, ← hdebitMem, ← hcheckMem]
        exact hreads
      obtain ⟨hsendStack, _heventLogs, heventStor, _heventBal, heventCode,
          _heventOutput, hwfSend, hreadsSend⟩ :=
        burnEventTail_effect_frame hownerStack hwfEvent hreadsEvent
          (by simpa only [redeemEventTail] using htailRun)
      rcases sendCursor.peelChildlessLine (line := sendPrefix)
          hsendChildless with
        ⟨callCursor, hsendRun⟩
      have sendEvidence := hsend hsendStack hsendRun
      have hwfCall : Mem.Wf callCursor.pre.memory := by
        rw [← sendEvidence.memory]
        exact hwfSend
      have hreadsCall : Mem.Reads callCursor.pre.memory
          (Bytes.writeAt img 0 (Sevm.argWord e amountArg).toBytes) := by
        rw [← sendEvidence.memory]
        exact hreadsSend
      have hcallStor : Devm.getStor afterDebitCursor.pre =
          Devm.getStor callCursor.pre :=
        hcallerStor.trans (heventStor.symm.trans sendEvidence.storage)
      have hcallCode : Devm.getCode cursor.pre =
          Devm.getCode callCursor.pre :=
        hcheckCode.trans (hdebitCode.trans
          (hcallerCode.trans (heventCode.symm.trans sendEvidence.code)))
      have hpreCall : (Devm.getStor callCursor.pre e.currentTarget).get key =
          (Devm.getStor cursor.pre e.currentTarget).get key := by
        rw [← congrFun hcallStor e.currentTarget, hsetDebit,
          Stor.get_set_ne _ hkeyNe _,
          ← congrFun hdebitStorPre e.currentTarget,
          ← congrFun hcheckStor e.currentTarget]
      have hpreCallCa : (Devm.getStor callCursor.pre ca).get key =
          (Devm.getStor cursor.pre ca).get key := by
        rw [htargetE] at hpreCall
        exact hpreCall
      have hcallCodeAt : some (callCursor.pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        rw [← congrFun hcallCode ca]
        exact hcursorCode
      -- cross the external value CALL
      have hcallRun := callCursor.run
      cases hcallRun with
      | next hcompiled htailCompiled =>
          rename_i midD
          have hat : Ninst.At e.code callCursor.pc Ninst.call :=
            ninstAt_of_subcode_next callCursor.codeSlice
          obtain ⟨nextBoundary, nextSub⟩ :=
            Func.noPushBefore_next callCursor.codeSlice
              callCursor.codeBoundary
          rcases callCursor.parentPrefix with ⟨actionsBefore, hbefore⟩
          rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_next
              (frame := ⟨fpc, e, fpre, .ok fpost, frun, fcommitted⟩)
              callCursor.current hbefore hat hcompiled with
            ⟨xl, continuation, selected, occurrence, hedge, _hnextPrefix⟩
          rcases hedge.exists_counted with ⟨counted, hcountedEdge⟩
          rcases occurrence with
            ⟨_opc, _ocurrent, _ocont, _obefore, _oselected, _oprefix, _oat,
              ofilled, ostep, _oprec, _oedge⟩
          have hstepAt : Ninst.StepRun callCursor.pc e callCursor.pre
              Ninst.call xl (.ok midD) :=
            Ninst.stepRun_pc_irrel (pc' := callCursor.pc)
              (by simp [Ninst.pcFree]) ostep
          -- the trailing guard excludes the reverter arm
          have htailPlain : Func.Run ((weth10 dp).main :: weth10Aux) e midD
              (Ninst.iszero ::: ((.call ethTransferErrorSlot) <?> success))
              fpost :=
            Func.Run.of_runCompiled htailCompiled
          rcases of_run_next htailPlain with
            ⟨afterIszero, hiszeroRun, hbranchPlain⟩
          rcases of_run_branch_call_revWith (ethTransferError_lookup dp)
              hbranchPlain with
            ⟨afterGuard, hguardPop, _hsuccessRun⟩
          rcases sendEvidence.stack with ⟨gasWord, hcallStack⟩
          have hcall : Ninst.Run e callCursor.pre Ninst.call midD :=
            Ninst.Run.of_runCompiled hcompiled
          rcases of_run_call_val_with_depth_frame hcallStack hcall with
              hfailed | hsuccess
          · exfalso
            have htest := prefix_of_iszero hiszeroRun hfailed.1
            have hguardStack' := hguardPop.stack
            simp only [Stack.Pop, Split, List.nil_append,
              List.cons_append] at hguardStack'
            rw [hguardStack'] at htest
            have hzero : ((0 : B256) =? 0) = 0 :=
              pref_head_unique htest (pref_append [(0 : B256)] afterGuard.stack)
            rw [show ((0 : B256) =? 0) = 1 from by
              simp [B256.eqCheck]] at hzero
            exact B256.zero_ne_one hzero.symm
          · rcases hsuccess with
              ⟨callParent, child, xlRaw, hasDelegation, resolvedCallee, code,
                availableGas, rawPc, hrawStep, hdepthPos, _hcallStackEq,
                hparentState, hparentMemory, _hparentLogs, _hparentOutput,
                hdelegation, hrawFilled, hprocess, hclean, _hresume,
                hmidState, _hreturnData, hmidMemory, hmidStack⟩
            have halign := Ninst.StepRun.unique_exec_of_filled ofilled
              hrawFilled hstepAt hrawStep
            cases halign.1
            obtain ⟨retained⟩ := exists_retainedXlot_of_filled ofilled
            have hcommits : retained.RawCommits := by
              cases retained with
              | none => trivial
              | some retainedRun =>
                  exact Frame.raw_commits_of_settlementCommits
                    (ProcessMessage.settlementCommits_of_some_ok_clean
                      hprocess hclean)
            have hparent : callCursor.pre.state =
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  resolvedCallee true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).benv.state := by
              simpa only [callMsg] using hparentState.symm
            have hmsgDepth :
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  resolvedCallee true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).depth <
                  e.depth := by
              dsimp only [callMsg]
              omega
            have hdelegation' :
                (getDelegatedCodeAddress
                      (callCursor.pre.getCode target.toAdr) = none ∧
                    code = callCursor.pre.getCode target.toAdr ∧
                    hasDelegation = false) ∨
                (∃ delegatedTarget,
                  getDelegatedCodeAddress
                      (callCursor.pre.getCode target.toAdr) =
                    some delegatedTarget ∧
                  code = callCursor.pre.getCode delegatedTarget ∧
                  hasDelegation = true) := by
              rcases hdelegation with ⟨hnone, _, hcode, hdel⟩ |
                ⟨delegatedTarget, hsome, _, hcode, hdel⟩
              · exact Or.inl ⟨hnone, hcode, hdel⟩
              · exact Or.inr ⟨delegatedTarget, hsome, hcode, hdel⟩
            have hresolved : target.toAdr = ca → resolvedCallee = ca := by
              intro htargetCa
              have hnone : getDelegatedCodeAddress
                  (callCursor.pre.getCode target.toAdr) = none := by
                rw [htargetCa]
                dsimp only [getDelegatedCodeAddress]
                rw [if_neg (not_delegation_of_compile hcallCodeAt)]
              rcases hdelegation with ⟨_, hna, _, _⟩ | ⟨_, hsome, _, _, _⟩
              · exact hna.trans htargetCa
              · simp [hnone] at hsome
            have htargetCode :
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  resolvedCallee true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).currentTarget =
                  ca →
                some code.toList = Prog.compile (weth10 dp) := by
              intro hct
              have htargetCa : target.toAdr = ca := by
                simpa only [callMsg] using hct
              exact callbackCode_eq_compiled_of_target_eq hcallCodeAt
                htargetCa hdelegation'
            have childEffect :=
              ProcessMessageTrace.allowanceRegionDelta_of_forallDeeperAt
                (dp := dp) (ca := ca) (depth := e.depth)
                (parent := callCursor.pre)
                ⟨_, retained, hprocess⟩ hparent hmsgDepth hcallCodeAt
                htargetCode
                (by
                  intro hct
                  have htargetCa : target.toAdr = ca := by
                    simpa only [callMsg] using hct
                  simp only [callMsg, htargetCa, hresolved htargetCa])
                hdeeper
            -- the zero-length return window leaves the memory frame intact
            have hmidMemory' : midD.memory = callParent.memory := by
              simpa only [show (0 : B256).toNat = 0 from rfl, List.take_zero,
                Mem.write] using hmidMemory
            have hwfMid : Mem.Wf midD.memory := by
              rw [hmidMemory', hparentMemory]
              exact Mem.Wf.extends _ hwfCall
            have hreadsMid : Mem.Reads midD.memory
                (Bytes.writeAt img 0 (Sevm.argWord e amountArg).toBytes) := by
              rw [hmidMemory', hparentMemory]
              exact Mem.Reads.extends _ hreadsCall
            have hcodeMid : some (midD.getCode ca).toList =
                Prog.compile (weth10 dp) := by
              rw [getCode_eq_of_state_eq hmidState ca, ← childEffect.codeEq]
              exact hcallCodeAt
            -- the trailing guard is closed by the success continuation
            have htailStorage :=
              Exec.tailGuardAllowanceStorage
                (frame := ⟨fpc, e, fpre, .ok fpost, frun, fcommitted⟩)
                (rest := callParent.stack)
                continuation htailCompiled nextSub nextBoundary
                hmidStack hwfMid hreadsMid hcodeMid hcloser
            -- the counted stream of the frame splits at the send child
            have hprefixSplit := callCursor.countedPrefix.descendantCounted_eq
            change Exec.attributionInner dp ca frun =
              [] ++ Exec.attributionInner dp ca callCursor.current
                at hprefixSplit
            have hedgeSplit := hcountedEdge.descendantCounted_eq
            change Exec.attributionInner dp ca callCursor.current =
              counted ++ Exec.attributionInner dp ca continuation
                at hedgeSplit
            have hcountedEq :=
              Exec.Deriv.ParentStepCounted.selected_eq_retained_of_call
                hat ofilled hstepAt retained hcountedEdge
            have hinnerEq : Exec.attributionInner dp ca frun =
                retained.attributionStream dp ca ++
                  Exec.attributionInner dp ca continuation := by
              rw [hprefixSplit, List.nil_append, hedgeSplit, hcountedEq]
            have hmid : (Devm.getStor midD ca).get key =
                applyAllowanceLedger (Devm.getStor cursor.pre ca)
                  (retained.attributionStream dp ca) key := by
              calc (Devm.getStor midD ca).get key
                  = (Devm.getStor child ca).get key :=
                    congrArg (fun state : State => (state.getStor ca).get key)
                      hmidState
                _ = applyAllowanceLedger (Devm.getStor callCursor.pre ca)
                      (retained.attributionStream dp ca) key :=
                    childEffect.storage key hkey
                _ = applyAllowanceLedger (Devm.getStor cursor.pre ca)
                      (retained.attributionStream dp ca) key :=
                    applyAllowanceLedger_congr hpreCallCa
            calc (Devm.getStor fpost ca).get key
                = applyAllowanceLedger (Devm.getStor midD ca)
                    (Exec.attributionInner dp ca continuation) key :=
                  htailStorage key hkey
              _ = applyAllowanceLedger (Devm.getStor cursor.pre ca)
                    (retained.attributionStream dp ca ++
                      Exec.attributionInner dp ca continuation) key :=
                  (applyAllowanceLedger_append _ _ _ _ key hmid).symm
              _ = applyAllowanceLedger (Devm.getStor cursor.pre ca)
                    (Exec.attributionInner dp ca frun) key := by
                  rw [hinnerEq]

/-- The redemption walk specialized to a childless terminal success
continuation, as `withdraw`, `withdrawTo` and the zero-recipient `transfer`
use it. -/
private theorem Exec.Frame.CountedCursor.redeemAllowanceStorage
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {amountArg target : B256} {sendPrefix successLine : Line}
    {successLast : Linst} {img : Bytes}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (redeemBody amountArg sendPrefix
        (successLine +++ Func.last successLast)) frame.post)
    (htarget : frame.sevm.currentTarget = ca)
    (hstack : [] <<+ cursor.pre.stack)
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img)
    (hcursorCode : some (cursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hsendChildless : ∀ n ∈ sendPrefix, NinstIsChildless n)
    (hsend : ∀ {sendPre callPre : Devm} {value : B256} {tail : Stack},
      value :: tail <<+ sendPre.stack →
      Line.Run frame.sevm sendPre sendPrefix callPre →
      ValueCallOperandPrefix frame.sevm sendPre callPre value target tail)
    (hsuccessChildless : ∀ n ∈ successLine, NinstIsChildless n)
    (hsuccessStor : Func.Inv Devm.getStor Devm.getStor
      (successLine +++ Func.last successLast))
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    ∀ key, InRegion .allowance key →
      (Devm.getStor frame.post ca).get key =
        applyAllowanceLedger (Devm.getStor cursor.pre ca)
          (Exec.attributionInner dp ca frame.run) key :=
  cursor.redeemAllowanceRegionStorage htarget hstack hwf hreads hcursorCode
    hsendChildless hsend
    (successAllowanceCloser_of_childless hsuccessChildless hsuccessStor)
    hdeeper

/-! ## The three public redemption arms -/

def redeemReturnTrueLine : Line :=
  [pushB256 1] ++ mstoreAt 0 ++ pushList [32, 0]

theorem returnTrue_eq_redeemReturnTrueLine :
    returnTrue = redeemReturnTrueLine +++ Func.last .ret := rfl

/-- `withdraw` transports the allowance region.  Its own record has no
allowance event, so the frame's record replays transparently; the caller-key
debit is address-shaped; and the committed send child's counted stream is
exactly the frame's proper-descendant stream, transported by the recursion
hypothesis. -/
theorem Exec.Frame.allowanceRegionEffect_of_withdraw
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable withdraw) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [withdrawSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorCountedSilent (frame := frame) context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemBody 0 redeemSendToCallerPrefix (Func.last .stop))
    frame.post at bodyCursor
  have hstorage := bodyCursor.redeemAllowanceStorage
    (successLine := []) (target := frame.sevm.caller.toB256)
    context.invocation.2.1 nil_pref
    (by rw [← hbodySilent.memory]; exact context.memory_wf)
    (by rw [← hbodySilent.memory]; exact context.memory_reads_empty)
    (by
      rw [← getCode_eq_of_state_eq hbodySilent.state ca]
      exact context.installed.1)
    (by simp [redeemSendToCallerPrefix, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToCallerPrefix_effect hp hrun)
    (by simp)
    (by func_inv)
    hdeeper
  have hnotlast : ownRecordLast frame.sevm = false := by
    simp [ownRecordLast, isFlashInvocation, isPermitInvocation, hselector,
      withdrawSelector_ne_flashLoanSelector,
      withdrawSelector_ne_permitSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post = none
    simp [frameAllowanceEvent, hnonempty, hselector,
      withdrawSelector_ne_approveSelector,
      withdrawSelector_ne_approveAndCallSelector,
      withdrawSelector_ne_permitSelector,
      withdrawSelector_ne_transferFromSelector,
      withdrawSelector_ne_withdrawFromSelector,
      withdrawSelector_ne_flashLoanSelector,
      withdrawSelector_ne_allowanceSelector]
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotlast]
  rw [hstream]
  refine ⟨fun key hkey => ?_,
    Exec.installedCodeEq_committed frame.run frame.committed
      context.installed⟩
  rw [applyAllowanceLedger_cons_none hown]
  rw [hstorage key hkey]
  exact applyAllowanceLedger_congr
    (congrArg (fun s : Stor => s.get key)
      (getStor_eq_of_state_eq hbodySilent.state ca).symm)

/-- `withdrawTo` transports the allowance region, exactly as `withdraw` does
with the recipient taken from the address argument. -/
theorem Exec.Frame.allowanceRegionEffect_of_withdrawTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable withdrawTo) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [withdrawToSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorCountedSilent (frame := frame) context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemBody 1 (redeemSendToArgPrefix 0) (Func.last .stop))
    frame.post at bodyCursor
  have hstorage := bodyCursor.redeemAllowanceStorage
    (successLine := []) (target := Sevm.argWord frame.sevm 0)
    context.invocation.2.1 nil_pref
    (by rw [← hbodySilent.memory]; exact context.memory_wf)
    (by rw [← hbodySilent.memory]; exact context.memory_reads_empty)
    (by
      rw [← getCode_eq_of_state_eq hbodySilent.state ca]
      exact context.installed.1)
    (by simp [redeemSendToArgPrefix, pushList, arg, cdl, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToArgPrefix_effect 0 hp hrun)
    (by simp)
    (by func_inv)
    hdeeper
  have hnotlast : ownRecordLast frame.sevm = false := by
    simp [ownRecordLast, isFlashInvocation, isPermitInvocation, hselector,
      withdrawToSelector_ne_flashLoanSelector,
      withdrawToSelector_ne_permitSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post = none
    simp [frameAllowanceEvent, hnonempty, hselector,
      withdrawToSelector_ne_approveSelector,
      withdrawToSelector_ne_approveAndCallSelector,
      withdrawToSelector_ne_permitSelector,
      withdrawToSelector_ne_transferFromSelector,
      withdrawToSelector_ne_withdrawFromSelector,
      withdrawToSelector_ne_flashLoanSelector,
      withdrawToSelector_ne_allowanceSelector]
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotlast]
  rw [hstream]
  refine ⟨fun key hkey => ?_,
    Exec.installedCodeEq_committed frame.run frame.committed
      context.installed⟩
  rw [applyAllowanceLedger_cons_none hown]
  rw [hstorage key hkey]
  exact applyAllowanceLedger_congr
    (congrArg (fun s : Stor => s.get key)
      (getStor_eq_of_state_eq hbodySilent.state ca).symm)

/-- The zero-recipient `transfer` branch is a redemption to the caller, and
transports the allowance region exactly as `withdraw` does. -/
theorem Exec.Frame.allowanceRegionEffect_of_transferZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hzero : Sevm.argWord frame.sevm 0 = 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable transfer) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [transferSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorCountedSilent (frame := frame) context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨transferCursor, hnonpayableSilent⟩
  change Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ((arg 0 ++ [iszero]) +++
      (transferZeroThen returnTrue <?> transferNonzeroThen returnTrue))
    frame.post at transferCursor
  rcases transferCursor.peelChildlessLine
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine⟩
  have htargetPrefix : [Sevm.argWord frame.sevm 0 =? 0] <<+
      targetBranchCursor.pre.stack := by
    rcases of_run_append (arg 0) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with ⟨afterZero, hzeroRun, hnil⟩
    cases hnil
    exact prefix_of_iszero hzeroRun (prefix_of_arg nil_pref harg)
  have htargetCheck : (Sevm.argWord frame.sevm 0 =? 0) = 1 := by
    simp [B256.eqCheck, hzero]
  rw [htargetCheck] at htargetPrefix
  rcases targetBranchCursor.selectBranchSuccSilent (flag := (1 : B256))
      (by decide) htargetPrefix with
    ⟨bodyCursor, _hbodyStack, hbranchSilent⟩
  have hlineStor : Devm.getStor transferCursor.pre =
      Devm.getStor targetBranchCursor.pre :=
    Line.of_inv Devm.getStor (by line_inv) htargetLine
  have hlineCode : Devm.getCode transferCursor.pre =
      Devm.getCode targetBranchCursor.pre :=
    Line.of_inv Devm.getCode (by line_inv) htargetLine
  have hlineMem : transferCursor.pre.memory = targetBranchCursor.pre.memory :=
    Line.of_inv Devm.memory (by line_inv) htargetLine
  have hbodyStor : Devm.getStor frame.pre ca =
      Devm.getStor bodyCursor.pre ca :=
    (getStor_eq_of_state_eq hentrySilent.state ca).trans
      ((getStor_eq_of_state_eq hnonpayableSilent.state ca).trans
        ((congrFun hlineStor ca).trans
          (getStor_eq_of_state_eq hbranchSilent.state ca)))
  have hbodyCode : Devm.getCode frame.pre ca =
      Devm.getCode bodyCursor.pre ca :=
    (getCode_eq_of_state_eq hentrySilent.state ca).trans
      ((getCode_eq_of_state_eq hnonpayableSilent.state ca).trans
        ((congrFun hlineCode ca).trans
          (getCode_eq_of_state_eq hbranchSilent.state ca)))
  have hbodyMem : frame.pre.memory = bodyCursor.pre.memory :=
    hentrySilent.memory.trans (hnonpayableSilent.memory.trans
      (hlineMem.trans hbranchSilent.memory))
  change Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemBody 1 redeemSendToCallerPrefix
      (redeemReturnTrueLine +++ Func.last .ret))
    frame.post at bodyCursor
  have hstorage := bodyCursor.redeemAllowanceStorage
    (target := frame.sevm.caller.toB256)
    context.invocation.2.1 nil_pref
    (by rw [← hbodyMem]; exact context.memory_wf)
    (by rw [← hbodyMem]; exact context.memory_reads_empty)
    (by
      rw [← hbodyCode]
      exact context.installed.1)
    (by simp [redeemSendToCallerPrefix, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToCallerPrefix_effect hp hrun)
    (by simp [redeemReturnTrueLine, mstoreAt, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by func_inv)
    hdeeper
  have hnotlast : ownRecordLast frame.sevm = false := by
    simp [ownRecordLast, isFlashInvocation, isPermitInvocation, hselector,
      transferSelector_ne_flashLoanSelector,
      transferSelector_ne_permitSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post = none
    simp [frameAllowanceEvent, hnonempty, hselector,
      transferSelector_ne_approveSelector,
      transferSelector_ne_approveAndCallSelector,
      transferSelector_ne_permitSelector,
      transferSelector_ne_transferFromSelector,
      transferSelector_ne_withdrawFromSelector,
      transferSelector_ne_flashLoanSelector,
      transferSelector_ne_allowanceSelector]
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotlast]
  rw [hstream]
  refine ⟨fun key hkey => ?_,
    Exec.installedCodeEq_committed frame.run frame.committed
      context.installed⟩
  rw [applyAllowanceLedger_cons_none hown]
  rw [hstorage key hkey]
  exact applyAllowanceLedger_congr
    (congrArg (fun s : Stor => s.get key) hbodyStor.symm)

/-! ## Read-sound transport across one retained child message

The same walk against the strengthened carrier: the retained child's stream
is entry-read sound against the child's entry storage, and the surrounding
message-entry and settlement segments record nothing, so composing them
re-bases it onto the parent's. -/

/-- Read-sound sibling of
`ProcessMessageTrace.allowanceRegionDelta_of_forallDeeperAt`. -/
theorem ProcessMessageTrace.allowanceRegionDeltaSound_of_forallDeeperAt
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {msg : Msg} {post parent : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hparent : parent.state = msg.benv.state)
    (hdepth : msg.depth < depth)
    (hcode : some (parent.getCode ca).toList =
      Prog.compile (weth10 dp))
    (htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp))
    (htargetDirect : msg.currentTarget = ca →
      msg.codeAddress = some ca)
    (hdeeper : ForallDeeperAt depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    AllowanceRegionEffectSound ca parent post
      (trace.retained.attributionStream dp ca) := by
  rcases trace with ⟨slot, retained, hprocess⟩
  cases retained with
  | none =>
      have hstorage : Devm.getStor parent ca = Devm.getStor post ca := by
        rcases ProcessMessage.none_ok_state_cases hprocess with
          hrollback | ⟨benv, htransfer, hpost⟩
        · exact congrArg (fun state : State => state.getStor ca)
            (hparent.trans hrollback.symm)
        · change msg.benvAfterTransfer = .ok benv at htransfer
          exact (congrArg (fun state : State => state.getStor ca)
              hparent).trans <|
            (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
              (congrArg (fun state : State => state.getStor ca) hpost).symm
      have hcodeEq : parent.getCode ca = post.getCode ca := by
        rcases ProcessMessage.none_ok_state_cases hprocess with
          hrollback | ⟨benv, htransfer, hpost⟩
        · exact congrArg (fun state : State => state.getCode ca)
            (hparent.trans hrollback.symm)
        · change msg.benvAfterTransfer = .ok benv at htransfer
          exact (congrArg (fun state : State => state.getCode ca)
              hparent).trans <|
            (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
              (congrArg (fun state : State => state.getCode ca) hpost).symm
      exact AllowanceRegionEffectSound.of_getStorCode_eq hstorage hcodeEq
  | @some pc sevm pre out run =>
      have henter : (Frame.ofCall msg).enter =
          .run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hprocess).1
      rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hevm⟩
      simp only [Frame.ofCall] at htransfer hevm
      have hpreState : pre.state = benv.state := by
        have component := congrArg (fun evm : Evm => evm.dyna.state) hevm
        change pre.state = (initEvm (msg.withBenv benv)).dyna.state
        exact component
      have hsevm : sevm = initSevm (msg.withBenv benv) :=
        congrArg (fun evm : Evm => evm.sta) hevm
      have hpc : pc = 0 := by
        simpa [initEvm] using congrArg (fun evm : Evm => evm.pc) hevm
      have hmemory : pre.memory = Mem.empty := by
        have component := congrArg (fun evm : Evm => evm.dyna.memory) hevm
        change pre.memory = (initEvm (msg.withBenv benv)).dyna.memory
        simpa [initEvm, initDevm, Msg.withBenv] using component
      have hentryStorage : Devm.getStor parent ca =
          Devm.getStor pre ca := by
        exact (congrArg (fun state : State => state.getStor ca)
            hparent).trans <|
          (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
            (congrArg (fun state : State => state.getStor ca)
              hpreState).symm
      have hentryCodeEq : parent.getCode ca = pre.getCode ca := by
        exact (congrArg (fun state : State => state.getCode ca)
            hparent).trans <|
          (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
            (congrArg (fun state : State => state.getCode ca)
              hpreState).symm
      have hentryCode : some (pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        calc
          some (pre.getCode ca).toList =
              some (benv.state.getCode ca).toList := by
            change some (pre.state.getCode ca).toList = _
            rw [hpreState]
          _ = some (msg.benv.state.getCode ca).toList := by
            rw [benvAfterTransfer_ok_getCode htransfer ca]
          _ = some (parent.getCode ca).toList := by
            change some (msg.benv.state.getCode ca).toList =
              some (parent.state.getCode ca).toList
            rw [hparent]
          _ = _ := hcode
      have hat : Prog.At (weth10 dp) ca pc sevm pre := by
        refine ⟨hentryCode, ?_⟩
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        refine ⟨?_, hpc⟩
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using htargetCode hmsgTarget
      have hdirect : sevm.currentTarget = ca →
          sevm.codeAddress = some ca := by
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using htargetDirect hmsgTarget
      by_cases hcommit : Execution.commits out = true
      · cases out with
        | error error => simp [Execution.commits] at hcommit
        | ok raw =>
            have hchildDepth : sevm.depth < depth := by
              rw [hsevm]
              simpa [initSevm, Msg.withBenv] using hdepth
            have hcore := hdeeper pc sevm pre (.ok raw) run
              hchildDepth hat
            have childEffect := hcore run hcommit hat
              (fun htarget => ⟨⟨hpc, hmemory⟩, hdirect htarget⟩)
            have hpostState : post.state = raw.state :=
              ProcessMessage.ok_state_eq_committedPost hprocess hcommit
            have hpostStorage : Devm.getStor raw ca =
                Devm.getStor post ca :=
              congrArg (fun state : State => state.getStor ca)
                hpostState.symm
            have hpostCode : raw.getCode ca = post.getCode ca :=
              congrArg (fun state : State => state.getCode ca)
                hpostState.symm
            exact (by
              simpa only [List.nil_append, List.append_nil,
                RetainedXlot.attributionStream] using
                (AllowanceRegionEffectSound.of_getStorCode_eq
                    hentryStorage hentryCodeEq).append
                  (childEffect.append
                    (AllowanceRegionEffectSound.of_getStorCode_eq
                      hpostStorage hpostCode)))
      · have hactions : Exec.attributionStream dp ca run = [] :=
          Exec.attributionStream_eq_nil_of_not_commits run hcommit
        have hpostState : post.state = msg.benv.state :=
          ProcessMessage.ok_state_eq_of_not_commits hprocess hcommit
        have hstorage : Devm.getStor parent ca = Devm.getStor post ca :=
          congrArg (fun state : State => state.getStor ca)
            (hparent.trans hpostState.symm)
        have hcodeEq : parent.getCode ca = post.getCode ca :=
          congrArg (fun state : State => state.getCode ca)
            (hparent.trans hpostState.symm)
        have hstream : RetainedXlot.attributionStream dp ca
            (RetainedXlot.some run) = [] := by
          simpa only [RetainedXlot.attributionStream] using hactions
        rw [hstream]
        exact AllowanceRegionEffectSound.of_getStorCode_eq hstorage hcodeEq

/-! ## Read-sound closers for the redemption guard suffix

The read-sound walk needs one thing the landed one does not: whatever the
success continuation retains must itself be entry-read sound against the
continuation's entry storage.  The two siblings below add exactly that
conjunct to `SuccessAllowanceCloser` and `Exec.tailGuardAllowanceStorage`,
so every existing consumer keeps discharging exactly the obligation it
already discharges. -/

/-- Read-sound sibling of `SuccessAllowanceCloser`: the continuation's own
counted stream replays onto the frame's committed post state *and* is
entry-read sound against the continuation's entry storage. -/
def SuccessAllowanceCloserSound (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) (img : Bytes) (success : Func) : Prop :=
  ∀ (entryPc : Nat) (entry : Devm)
    (continuation : Exec entryPc frame.sevm entry frame.out),
    Func.RunCompiled ((weth10 dp).main :: weth10Aux) frame.sevm entry
      success frame.post →
    subcode frame.sevm.code.toList entryPc
      (Func.compile (table 0 ((weth10 dp).main :: weth10Aux)) entryPc
        success) →
    noPushBefore frame.sevm.code entryPc 32 = true →
    Mem.Wf entry.memory →
    Mem.Reads entry.memory img →
    some (entry.getCode ca).toList = Prog.compile (weth10 dp) →
    (∀ key, InRegion .allowance key →
        (Devm.getStor frame.post ca).get key =
          applyAllowanceLedger (Devm.getStor entry ca)
            (Exec.attributionInner dp ca continuation) key) ∧
      AllowanceEntryReadSound (Devm.getStor entry ca)
        (Exec.attributionInner dp ca continuation)

/-- The read-sound closer discharges the landed one. -/
theorem SuccessAllowanceCloserSound.successAllowanceCloser
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {img : Bytes}
    {success : Func}
    (h : SuccessAllowanceCloserSound dp ca frame img success) :
    SuccessAllowanceCloser dp ca frame img success :=
  fun entryPc entry continuation hrun hsub hbound hwf hreads hcode =>
    (h entryPc entry continuation hrun hsub hbound hwf hreads hcode).1

/-- A childless success continuation retains no counted record, so its
segment is entry-read sound for free: the empty ledger admits no split. -/
theorem successAllowanceCloserSound_of_childless
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {img : Bytes}
    {successLine : Line} {successLast : Linst}
    (hchildless : ∀ n ∈ successLine, NinstIsChildless n)
    (hstor : Func.Inv Devm.getStor Devm.getStor
      (successLine +++ Func.last successLast)) :
    SuccessAllowanceCloserSound dp ca frame img
      (successLine +++ Func.last successLast) := by
  intro entryPc entry continuation hrun hsub hbound hwf hreads hcode
  refine ⟨successAllowanceCloser_of_childless hchildless hstor entryPc entry
    continuation hrun hsub hbound hwf hreads hcode, ?_⟩
  let suffixCursor :
      Blanc.Weth10.Exec.Frame.CountedCursor
        (frame := ⟨entryPc, frame.sevm, entry, frame.out, continuation,
          frame.committed⟩) dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (successLine +++ Func.last successLast) frame.post :=
    ⟨entryPc, entry, continuation,
      ⟨[], Exec.Deriv.ParentPrefixActions.refl _⟩,
      Exec.Deriv.ParentPrefixCounted.refl _, hrun, hsub, hbound⟩
  rcases suffixCursor.peelChildlessLine hchildless with ⟨lastCursor, -⟩
  have hnil : Exec.attributionInner dp ca continuation = [] :=
    lastCursor.finishAttributionInner
  rw [hnil]
  exact AllowanceEntryReadSound.nil _

/-- Read-sound sibling of `Exec.tailGuardAllowanceStorage`: the post-`CALL`
`ISZERO` test and the send-error branch neither retain a counted record nor
move storage, so both the replay and the entry-read soundness of the guard
suffix are the success continuation's own, re-based across a state-silent
step. -/
theorem Exec.tailGuardAllowanceSound
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {pcT : Nat} {midD : Devm} {success : Func}
    {errSlot : Nat} {rest : Stack} {img : Bytes}
    (next : Exec pcT frame.sevm midD frame.out)
    (htail : Func.RunCompiled ((weth10 dp).main :: weth10Aux) frame.sevm midD
      (Ninst.iszero ::: ((.call errSlot) <?> success)) frame.post)
    (hsub : subcode frame.sevm.code.toList pcT
      (Func.compile (table 0 ((weth10 dp).main :: weth10Aux)) pcT
        (Ninst.iszero ::: ((.call errSlot) <?> success))))
    (hbound : noPushBefore frame.sevm.code pcT 32 = true)
    (hstackOne : midD.stack = (1 : B256) :: rest)
    (hwf : Mem.Wf midD.memory)
    (hreads : Mem.Reads midD.memory img)
    (hcode : some (midD.getCode ca).toList = Prog.compile (weth10 dp))
    (hcloser : SuccessAllowanceCloserSound dp ca frame img success) :
    (∀ key, InRegion .allowance key →
        (Devm.getStor frame.post ca).get key =
          applyAllowanceLedger (Devm.getStor midD ca)
            (Exec.attributionInner dp ca next) key) ∧
      AllowanceEntryReadSound (Devm.getStor midD ca)
        (Exec.attributionInner dp ca next) := by
  let tailCursor :
      Blanc.Weth10.Exec.Frame.CountedCursor
        (frame := ⟨pcT, frame.sevm, midD, frame.out, next,
          frame.committed⟩) dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (Ninst.iszero ::: ((.call errSlot) <?> success)) frame.post :=
    ⟨pcT, midD, next, ⟨[], Exec.Deriv.ParentPrefixActions.refl _⟩,
      Exec.Deriv.ParentPrefixCounted.refl _, htail, hsub, hbound⟩
  rcases tailCursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨branchCursor, hiszeroRun⟩
  have hp0 : [(1 : B256)] <<+ midD.stack := by
    rw [hstackOne]
    exact pref_append [(1 : B256)] rest
  have hpIso : ((1 : B256) =? 0) :: [] <<+ branchCursor.pre.stack :=
    prefix_of_iszero hiszeroRun hp0
  have hne10 : (1 : B256) ≠ 0 := fun h => B256.zero_ne_one h.symm
  rw [show ((1 : B256) =? 0) = 0 from by simp [B256.eqCheck, hne10]]
    at hpIso
  rcases branchCursor.selectBranchZeroSilent hpIso with
    ⟨successCursor, _hsuccStack, hbranchSilent⟩
  have hstate : midD.state = successCursor.pre.state :=
    (Ninst.Hinv.inv (f := Devm.state) hiszeroRun).trans hbranchSilent.state
  have hmemory : midD.memory = successCursor.pre.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) hiszeroRun).trans hbranchSilent.memory
  obtain ⟨hclosedStorage, hclosedRead⟩ := hcloser successCursor.pc
    successCursor.pre successCursor.current successCursor.run
    successCursor.codeSlice successCursor.codeBoundary
    (by rw [← hmemory]; exact hwf)
    (by rw [← hmemory]; exact hreads)
    (by rw [← getCode_eq_of_state_eq hstate ca]; exact hcode)
  have hsplit := successCursor.countedPrefix.descendantCounted_eq
  change Exec.attributionInner dp ca next =
    [] ++ Exec.attributionInner dp ca successCursor.current at hsplit
  have hstorCa : Devm.getStor midD ca = Devm.getStor successCursor.pre ca :=
    getStor_eq_of_state_eq hstate ca
  refine ⟨fun key hkey => ?_, ?_⟩
  · rw [hsplit, List.nil_append,
      applyAllowanceLedger_congr
        (congrArg (fun s : Stor => s.get key) hstorCa)]
    exact hclosedStorage key hkey
  · rw [hsplit, List.nil_append, hstorCa]
    exact hclosedRead

/-! ## The read-sound redemption walk

The same walk as `Exec.Frame.CountedCursor.redeemAllowanceRegionStorage`,
against the strengthened carrier.  Two things differ.  The key is no longer
introduced up front: the send child's entry-read soundness has to be
re-based from the `CALL` cursor's storage onto the walk's entry storage, and
`AllowanceEntryReadSound.append` consumes that re-basing as a statement
about *every* tagged key rather than one at a time.  And the two segments
are then composed by `AllowanceEntryReadSound.append` rather than by
rewriting with `applyAllowanceLedger_append`. -/

/-- Read-sound sibling of
`Exec.Frame.CountedCursor.redeemAllowanceRegionStorage`. -/
theorem Exec.Frame.CountedCursor.redeemAllowanceRegionSound
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {amountArg target : B256} {sendPrefix : Line}
    {success : Func} {img : Bytes}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (redeemBody amountArg sendPrefix success) frame.post)
    (htarget : frame.sevm.currentTarget = ca)
    (hstack : [] <<+ cursor.pre.stack)
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img)
    (hcursorCode : some (cursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hsendChildless : ∀ n ∈ sendPrefix, NinstIsChildless n)
    (hsend : ∀ {sendPre callPre : Devm} {value : B256} {tail : Stack},
      value :: tail <<+ sendPre.stack →
      Line.Run frame.sevm sendPre sendPrefix callPre →
      ValueCallOperandPrefix frame.sevm sendPre callPre value target tail)
    (hcloser : SuccessAllowanceCloserSound dp ca frame
      (Bytes.writeAt img 0 (Sevm.argWord frame.sevm amountArg).toBytes)
      success)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    (∀ key, InRegion .allowance key →
        (Devm.getStor frame.post ca).get key =
          applyAllowanceLedger (Devm.getStor cursor.pre ca)
            (Exec.attributionInner dp ca frame.run) key) ∧
      AllowanceEntryReadSound (Devm.getStor cursor.pre ca)
        (Exec.attributionInner dp ca frame.run) := by
  rcases frame with ⟨fpc, e, fpre, fout, frun, fcommitted⟩
  cases fout with
  | error err => simp [Execution.commits] at fcommitted
  | ok fpost =>
      have htargetE : e.currentTarget = ca := htarget
      have hkeyNe : ∀ key, InRegion .allowance key → e.caller.toB256 ≠ key :=
        fun key hkey => (allowanceRegion_ne_validAdr hkey ⟨e.caller, rfl⟩).symm
      -- the guarded balance check
      unfold redeemBody at cursor
      rcases cursor.peelChildlessLine (line := redeemCheckLine amountArg)
          (by simp [redeemCheckLine, loadCallerBalanceAmount,
            balanceTooSmall, arg, cdl, NinstIsChildless,
            Ninst.pushB256]) with
        ⟨branchCursor, hcheck⟩
      unfold redeemCheckLine at hcheck
      rcases of_run_append (loadCallerBalanceAmount amountArg) hcheck with
        ⟨afterLoad, hload, hguard⟩
      rcases prefix_of_loadCallerBalanceAmount hstack hload with
        ⟨balance, _hbalance, hloadStack⟩
      have hguardStack : (balance <? Sevm.argWord e amountArg) :: balance ::
          Sevm.argWord e amountArg :: e.caller.toB256 :: [] <<+
            branchCursor.pre.stack :=
        prefix_of_balanceTooSmall hloadStack hguard
      rcases branchCursor.selectBranchLeftWithBurn
          (not_run_call_revWith (burnBalanceError_lookup dp)) with
        ⟨successCursor, hbalancePopBy⟩
      have hbalancePop := Devm.PopBurn.of_popBurnBy hbalancePopBy
      have hpopStack := hbalancePop.stack
      simp only [Stack.Pop, Split, List.nil_append,
        List.cons_append] at hpopStack
      rw [hpopStack] at hguardStack
      have hflag : (balance <? Sevm.argWord e amountArg) = 0 :=
        pref_head_unique hguardStack (pref_append [0] successCursor.pre.stack)
      rw [hflag] at hguardStack
      have hsuccessStack : balance :: Sevm.argWord e amountArg ::
          e.caller.toB256 :: [] <<+ successCursor.pre.stack :=
        cons_pref_cons_inv hguardStack
      have hcheckStor : Devm.getStor cursor.pre =
          Devm.getStor successCursor.pre :=
        (Line.of_inv Devm.getStor (by line_inv) hload).trans
          ((Line.of_inv Devm.getStor (by line_inv) hguard).trans
            (PopBurn.Inv.inv hbalancePop))
      have hcheckCode : Devm.getCode cursor.pre =
          Devm.getCode successCursor.pre :=
        (Line.of_inv Devm.getCode (by line_inv) hload).trans
          ((Line.of_inv Devm.getCode (by line_inv) hguard).trans
            (funext (getCode_eq_of_state_eq hbalancePop.state)))
      have hcheckMem : cursor.pre.memory = successCursor.pre.memory :=
        (Line.of_inv Devm.memory (by line_inv) hload).trans
          ((Line.of_inv Devm.memory (by line_inv) hguard).trans
            hbalancePop.memory)
      -- the caller-key debit
      rcases successCursor.peelChildlessLine (line := debitLoadedBalance)
          (by simp [debitLoadedBalance, NinstIsChildless]) with
        ⟨afterDebitCursor, hdebit⟩
      have hdebitCode : Devm.getCode successCursor.pre =
          Devm.getCode afterDebitCursor.pre :=
        Line.of_inv Devm.getCode (by line_inv) hdebit
      have hdebitMem : successCursor.pre.memory =
          afterDebitCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) hdebit
      unfold debitLoadedBalance at hdebit
      rcases Line.of_run_cons hdebit with ⟨d1, hsub, hdebit1⟩
      have hpD1 : (balance - Sevm.argWord e amountArg) ::
          e.caller.toB256 :: [] <<+ d1.stack :=
        prefix_of_sub hsub hsuccessStack
      rcases Line.of_run_cons hdebit1 with ⟨d2, hswap, hdebit2⟩
      have hswapCoreD : Stack.Swap (0 : Fin 16).val
          [balance - Sevm.argWord e amountArg, e.caller.toB256]
          [e.caller.toB256, balance - Sevm.argWord e amountArg] :=
        Stack.swapCore_zero
      have hpD2 : e.caller.toB256 ::
          (balance - Sevm.argWord e amountArg) :: [] <<+ d2.stack :=
        Stack.prefix_of_swap hswapCoreD (of_run_swap hswap) hpD1
      rcases Line.of_run_cons hdebit2 with ⟨d3, hstore, hnilD⟩
      cases hnilD
      have hsetDebit : Devm.getStor afterDebitCursor.pre e.currentTarget =
          (Devm.getStor d2 e.currentTarget).set e.caller.toB256
            (balance - Sevm.argWord e amountArg) :=
        sstore_getStor_set hstore hpD2
      have hdebitStorPre : Devm.getStor successCursor.pre =
          Devm.getStor d2 :=
        (Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hsub Line.Run.nil)).trans
          (Line.of_inv Devm.getStor (by line_inv)
            (Line.Run.cons hswap Line.Run.nil))
      -- the burn event and the send operands
      rcases afterDebitCursor.peelChildlessLine
          (line := caller :: redeemEventTail amountArg)
          (by simp [redeemEventTail, arg, cdl, emitTransfer,
            Blanc.transferFromLog, mstoreAt, logWith, NinstIsChildless,
            Ninst.pushB256]) with
        ⟨sendCursor, heventRun⟩
      rcases Line.of_run_cons heventRun with ⟨eventPre, hcallerRun, htailRun⟩
      have hcallerStor : Devm.getStor afterDebitCursor.pre =
          Devm.getStor eventPre :=
        Line.of_inv Devm.getStor (by line_inv)
          (Line.Run.cons hcallerRun Line.Run.nil)
      have hcallerCode : Devm.getCode afterDebitCursor.pre =
          Devm.getCode eventPre :=
        Line.of_inv Devm.getCode (by line_inv)
          (Line.Run.cons hcallerRun Line.Run.nil)
      have hcallerMem : afterDebitCursor.pre.memory = eventPre.memory :=
        Line.of_inv Devm.memory (by line_inv)
          (Line.Run.cons hcallerRun Line.Run.nil)
      have hownerStack : e.caller.toB256 :: [] <<+ eventPre.stack :=
        prefix_of_push (of_run_caller hcallerRun) nil_pref
      have hwfEvent : Mem.Wf eventPre.memory := by
        rw [← hcallerMem, ← hdebitMem, ← hcheckMem]
        exact hwf
      have hreadsEvent : Mem.Reads eventPre.memory img := by
        rw [← hcallerMem, ← hdebitMem, ← hcheckMem]
        exact hreads
      obtain ⟨hsendStack, _heventLogs, heventStor, _heventBal, heventCode,
          _heventOutput, hwfSend, hreadsSend⟩ :=
        burnEventTail_effect_frame hownerStack hwfEvent hreadsEvent
          (by simpa only [redeemEventTail] using htailRun)
      rcases sendCursor.peelChildlessLine (line := sendPrefix)
          hsendChildless with
        ⟨callCursor, hsendRun⟩
      have sendEvidence := hsend hsendStack hsendRun
      have hwfCall : Mem.Wf callCursor.pre.memory := by
        rw [← sendEvidence.memory]
        exact hwfSend
      have hreadsCall : Mem.Reads callCursor.pre.memory
          (Bytes.writeAt img 0 (Sevm.argWord e amountArg).toBytes) := by
        rw [← sendEvidence.memory]
        exact hreadsSend
      have hcallStor : Devm.getStor afterDebitCursor.pre =
          Devm.getStor callCursor.pre :=
        hcallerStor.trans (heventStor.symm.trans sendEvidence.storage)
      have hcallCode : Devm.getCode cursor.pre =
          Devm.getCode callCursor.pre :=
        hcheckCode.trans (hdebitCode.trans
          (hcallerCode.trans (heventCode.symm.trans sendEvidence.code)))
      have hpreCall : ∀ key, InRegion .allowance key →
          (Devm.getStor callCursor.pre e.currentTarget).get key =
            (Devm.getStor cursor.pre e.currentTarget).get key := by
        intro key hkey
        rw [← congrFun hcallStor e.currentTarget, hsetDebit,
          Stor.get_set_ne _ (hkeyNe key hkey) _,
          ← congrFun hdebitStorPre e.currentTarget,
          ← congrFun hcheckStor e.currentTarget]
      have hpreCallCa : ∀ key, InRegion .allowance key →
          (Devm.getStor callCursor.pre ca).get key =
            (Devm.getStor cursor.pre ca).get key := by
        rw [htargetE] at hpreCall
        exact hpreCall
      have hcallCodeAt : some (callCursor.pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        rw [← congrFun hcallCode ca]
        exact hcursorCode
      -- cross the external value CALL
      have hcallRun := callCursor.run
      cases hcallRun with
      | next hcompiled htailCompiled =>
          rename_i midD
          have hat : Ninst.At e.code callCursor.pc Ninst.call :=
            ninstAt_of_subcode_next callCursor.codeSlice
          obtain ⟨nextBoundary, nextSub⟩ :=
            Func.noPushBefore_next callCursor.codeSlice
              callCursor.codeBoundary
          rcases callCursor.parentPrefix with ⟨actionsBefore, hbefore⟩
          rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_next
              (frame := ⟨fpc, e, fpre, .ok fpost, frun, fcommitted⟩)
              callCursor.current hbefore hat hcompiled with
            ⟨xl, continuation, selected, occurrence, hedge, _hnextPrefix⟩
          rcases hedge.exists_counted with ⟨counted, hcountedEdge⟩
          rcases occurrence with
            ⟨_opc, _ocurrent, _ocont, _obefore, _oselected, _oprefix, _oat,
              ofilled, ostep, _oprec, _oedge⟩
          have hstepAt : Ninst.StepRun callCursor.pc e callCursor.pre
              Ninst.call xl (.ok midD) :=
            Ninst.stepRun_pc_irrel (pc' := callCursor.pc)
              (by simp [Ninst.pcFree]) ostep
          -- the trailing guard excludes the reverter arm
          have htailPlain : Func.Run ((weth10 dp).main :: weth10Aux) e midD
              (Ninst.iszero ::: ((.call ethTransferErrorSlot) <?> success))
              fpost :=
            Func.Run.of_runCompiled htailCompiled
          rcases of_run_next htailPlain with
            ⟨afterIszero, hiszeroRun, hbranchPlain⟩
          rcases of_run_branch_call_revWith (ethTransferError_lookup dp)
              hbranchPlain with
            ⟨afterGuard, hguardPop, _hsuccessRun⟩
          rcases sendEvidence.stack with ⟨gasWord, hcallStack⟩
          have hcall : Ninst.Run e callCursor.pre Ninst.call midD :=
            Ninst.Run.of_runCompiled hcompiled
          rcases of_run_call_val_with_depth_frame hcallStack hcall with
              hfailed | hsuccess
          · exfalso
            have htest := prefix_of_iszero hiszeroRun hfailed.1
            have hguardStack' := hguardPop.stack
            simp only [Stack.Pop, Split, List.nil_append,
              List.cons_append] at hguardStack'
            rw [hguardStack'] at htest
            have hzero : ((0 : B256) =? 0) = 0 :=
              pref_head_unique htest (pref_append [(0 : B256)] afterGuard.stack)
            rw [show ((0 : B256) =? 0) = 1 from by
              simp [B256.eqCheck]] at hzero
            exact B256.zero_ne_one hzero.symm
          · rcases hsuccess with
              ⟨callParent, child, xlRaw, hasDelegation, resolvedCallee, code,
                availableGas, rawPc, hrawStep, hdepthPos, _hcallStackEq,
                hparentState, hparentMemory, _hparentLogs, _hparentOutput,
                hdelegation, hrawFilled, hprocess, hclean, _hresume,
                hmidState, _hreturnData, hmidMemory, hmidStack⟩
            have halign := Ninst.StepRun.unique_exec_of_filled ofilled
              hrawFilled hstepAt hrawStep
            cases halign.1
            obtain ⟨retained⟩ := exists_retainedXlot_of_filled ofilled
            have hcommits : retained.RawCommits := by
              cases retained with
              | none => trivial
              | some retainedRun =>
                  exact Frame.raw_commits_of_settlementCommits
                    (ProcessMessage.settlementCommits_of_some_ok_clean
                      hprocess hclean)
            have hparent : callCursor.pre.state =
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  resolvedCallee true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).benv.state := by
              simpa only [callMsg] using hparentState.symm
            have hmsgDepth :
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  resolvedCallee true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).depth <
                  e.depth := by
              dsimp only [callMsg]
              omega
            have hdelegation' :
                (getDelegatedCodeAddress
                      (callCursor.pre.getCode target.toAdr) = none ∧
                    code = callCursor.pre.getCode target.toAdr ∧
                    hasDelegation = false) ∨
                (∃ delegatedTarget,
                  getDelegatedCodeAddress
                      (callCursor.pre.getCode target.toAdr) =
                    some delegatedTarget ∧
                  code = callCursor.pre.getCode delegatedTarget ∧
                  hasDelegation = true) := by
              rcases hdelegation with ⟨hnone, _, hcode, hdel⟩ |
                ⟨delegatedTarget, hsome, _, hcode, hdel⟩
              · exact Or.inl ⟨hnone, hcode, hdel⟩
              · exact Or.inr ⟨delegatedTarget, hsome, hcode, hdel⟩
            have hresolved : target.toAdr = ca → resolvedCallee = ca := by
              intro htargetCa
              have hnone : getDelegatedCodeAddress
                  (callCursor.pre.getCode target.toAdr) = none := by
                rw [htargetCa]
                dsimp only [getDelegatedCodeAddress]
                rw [if_neg (not_delegation_of_compile hcallCodeAt)]
              rcases hdelegation with ⟨_, hna, _, _⟩ | ⟨_, hsome, _, _, _⟩
              · exact hna.trans htargetCa
              · simp [hnone] at hsome
            have htargetCode :
                (callMsg e callParent
                  (min gasWord.toNat (except64th availableGas) +
                    (if (Sevm.argWord e amountArg).toNat = 0 then 0
                      else gCallStipend))
                  (Sevm.argWord e amountArg) e.currentTarget target.toAdr
                  resolvedCallee true false
                  ((callCursor.pre.memory.read (0 : B256).toNat
                    (0 : B256).toNat).1) code hasDelegation).currentTarget =
                  ca →
                some code.toList = Prog.compile (weth10 dp) := by
              intro hct
              have htargetCa : target.toAdr = ca := by
                simpa only [callMsg] using hct
              exact callbackCode_eq_compiled_of_target_eq hcallCodeAt
                htargetCa hdelegation'
            have childEffect :=
              ProcessMessageTrace.allowanceRegionDeltaSound_of_forallDeeperAt
                (dp := dp) (ca := ca) (depth := e.depth)
                (parent := callCursor.pre)
                ⟨_, retained, hprocess⟩ hparent hmsgDepth hcallCodeAt
                htargetCode
                (by
                  intro hct
                  have htargetCa : target.toAdr = ca := by
                    simpa only [callMsg] using hct
                  simp only [callMsg, htargetCa, hresolved htargetCa])
                hdeeper
            -- the zero-length return window leaves the memory frame intact
            have hmidMemory' : midD.memory = callParent.memory := by
              simpa only [show (0 : B256).toNat = 0 from rfl, List.take_zero,
                Mem.write] using hmidMemory
            have hwfMid : Mem.Wf midD.memory := by
              rw [hmidMemory', hparentMemory]
              exact Mem.Wf.extends _ hwfCall
            have hreadsMid : Mem.Reads midD.memory
                (Bytes.writeAt img 0 (Sevm.argWord e amountArg).toBytes) := by
              rw [hmidMemory', hparentMemory]
              exact Mem.Reads.extends _ hreadsCall
            have hcodeMid : some (midD.getCode ca).toList =
                Prog.compile (weth10 dp) := by
              rw [getCode_eq_of_state_eq hmidState ca, ← childEffect.codeEq]
              exact hcallCodeAt
            -- the trailing guard is closed by the success continuation
            obtain ⟨htailStorage, htailRead⟩ :=
              Exec.tailGuardAllowanceSound
                (frame := ⟨fpc, e, fpre, .ok fpost, frun, fcommitted⟩)
                (rest := callParent.stack)
                continuation htailCompiled nextSub nextBoundary
                hmidStack hwfMid hreadsMid hcodeMid hcloser
            -- the counted stream of the frame splits at the send child
            have hprefixSplit := callCursor.countedPrefix.descendantCounted_eq
            change Exec.attributionInner dp ca frun =
              [] ++ Exec.attributionInner dp ca callCursor.current
                at hprefixSplit
            have hedgeSplit := hcountedEdge.descendantCounted_eq
            change Exec.attributionInner dp ca callCursor.current =
              counted ++ Exec.attributionInner dp ca continuation
                at hedgeSplit
            have hcountedEq :=
              Exec.Deriv.ParentStepCounted.selected_eq_retained_of_call
                hat ofilled hstepAt retained hcountedEdge
            have hinnerEq : Exec.attributionInner dp ca frun =
                retained.attributionStream dp ca ++
                  Exec.attributionInner dp ca continuation := by
              rw [hprefixSplit, List.nil_append, hedgeSplit, hcountedEq]
            have hmid : ∀ key, InRegion .allowance key →
                (Devm.getStor midD ca).get key =
                  applyAllowanceLedger (Devm.getStor cursor.pre ca)
                    (retained.attributionStream dp ca) key := by
              intro key hkey
              calc (Devm.getStor midD ca).get key
                  = (Devm.getStor child ca).get key :=
                    congrArg (fun state : State => (state.getStor ca).get key)
                      hmidState
                _ = applyAllowanceLedger (Devm.getStor callCursor.pre ca)
                      (retained.attributionStream dp ca) key :=
                    childEffect.storage key hkey
                _ = applyAllowanceLedger (Devm.getStor cursor.pre ca)
                      (retained.attributionStream dp ca) key :=
                    applyAllowanceLedger_congr (hpreCallCa key hkey)
            -- the child's own entry-read soundness, re-based onto the walk's
            -- entry storage across the address-shaped debit
            have hchildRead : AllowanceEntryReadSound
                (Devm.getStor cursor.pre ca)
                (retained.attributionStream dp ca) := by
              have hrebased := AllowanceEntryReadSound.append
                (pre := Devm.getStor cursor.pre ca)
                (mid := Devm.getStor callCursor.pre ca)
                (left := []) (right := retained.attributionStream dp ca)
                (fun key hkey => by
                  rw [applyAllowanceLedger_nil]
                  exact hpreCallCa key hkey)
                (AllowanceEntryReadSound.nil _) childEffect.entryRead
              simpa only [List.nil_append] using hrebased
            have hinnerRead : AllowanceEntryReadSound
                (Devm.getStor cursor.pre ca)
                (Exec.attributionInner dp ca frun) := by
              rw [hinnerEq]
              exact AllowanceEntryReadSound.append hmid hchildRead htailRead
            refine ⟨fun key hkey => ?_, hinnerRead⟩
            calc (Devm.getStor fpost ca).get key
                = applyAllowanceLedger (Devm.getStor midD ca)
                    (Exec.attributionInner dp ca continuation) key :=
                  htailStorage key hkey
              _ = applyAllowanceLedger (Devm.getStor cursor.pre ca)
                    (retained.attributionStream dp ca ++
                      Exec.attributionInner dp ca continuation) key :=
                  (applyAllowanceLedger_append _ _ _ _ key (hmid key hkey)).symm
              _ = applyAllowanceLedger (Devm.getStor cursor.pre ca)
                    (Exec.attributionInner dp ca frun) key := by
                  rw [hinnerEq]

/-- The read-sound redemption walk specialized to a childless terminal
success continuation, as `withdraw`, `withdrawTo` and the zero-recipient
`transfer` use it. -/
private theorem Exec.Frame.CountedCursor.redeemAllowanceSound
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {amountArg target : B256} {sendPrefix successLine : Line}
    {successLast : Linst} {img : Bytes}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (redeemBody amountArg sendPrefix
        (successLine +++ Func.last successLast)) frame.post)
    (htarget : frame.sevm.currentTarget = ca)
    (hstack : [] <<+ cursor.pre.stack)
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img)
    (hcursorCode : some (cursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hsendChildless : ∀ n ∈ sendPrefix, NinstIsChildless n)
    (hsend : ∀ {sendPre callPre : Devm} {value : B256} {tail : Stack},
      value :: tail <<+ sendPre.stack →
      Line.Run frame.sevm sendPre sendPrefix callPre →
      ValueCallOperandPrefix frame.sevm sendPre callPre value target tail)
    (hsuccessChildless : ∀ n ∈ successLine, NinstIsChildless n)
    (hsuccessStor : Func.Inv Devm.getStor Devm.getStor
      (successLine +++ Func.last successLast))
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    (∀ key, InRegion .allowance key →
        (Devm.getStor frame.post ca).get key =
          applyAllowanceLedger (Devm.getStor cursor.pre ca)
            (Exec.attributionInner dp ca frame.run) key) ∧
      AllowanceEntryReadSound (Devm.getStor cursor.pre ca)
        (Exec.attributionInner dp ca frame.run) :=
  cursor.redeemAllowanceRegionSound htarget hstack hwf hreads hcursorCode
    hsendChildless hsend
    (successAllowanceCloserSound_of_childless hsuccessChildless hsuccessStor)
    hdeeper


/-! ## The read-sound redemption arms

Each arm composes two read-sound segments: the frame's own record, which
carries no allowance event and so moves no tagged key and records no read,
and the redemption walk's own stream.  The prefix's read clause is
`AllowanceEntryReadSound.ofFrame`; the walk supplies the rest. -/

/-- `withdraw` transports the allowance region read-soundly. -/
theorem Exec.Frame.allowanceRegionEffectSound_of_withdraw
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    AllowanceRegionEffectSound ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable withdraw) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [withdrawSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorCountedSilent (frame := frame) context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemBody 0 redeemSendToCallerPrefix (Func.last .stop))
    frame.post at bodyCursor
  obtain ⟨hstorage, hread⟩ := bodyCursor.redeemAllowanceSound
    (successLine := []) (target := frame.sevm.caller.toB256)
    context.invocation.2.1 nil_pref
    (by rw [← hbodySilent.memory]; exact context.memory_wf)
    (by rw [← hbodySilent.memory]; exact context.memory_reads_empty)
    (by
      rw [← getCode_eq_of_state_eq hbodySilent.state ca]
      exact context.installed.1)
    (by simp [redeemSendToCallerPrefix, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToCallerPrefix_effect hp hrun)
    (by simp)
    (by func_inv)
    hdeeper
  have hnotlast : ownRecordLast frame.sevm = false := by
    simp [ownRecordLast, isFlashInvocation, isPermitInvocation, hselector,
      withdrawSelector_ne_flashLoanSelector,
      withdrawSelector_ne_permitSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post = none
    simp [frameAllowanceEvent, hnonempty, hselector,
      withdrawSelector_ne_approveSelector,
      withdrawSelector_ne_approveAndCallSelector,
      withdrawSelector_ne_permitSelector,
      withdrawSelector_ne_transferFromSelector,
      withdrawSelector_ne_withdrawFromSelector,
      withdrawSelector_ne_flashLoanSelector,
      withdrawSelector_ne_allowanceSelector]
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotlast]
  have hbodyStor : Devm.getStor frame.pre ca =
      Devm.getStor bodyCursor.pre ca :=
    getStor_eq_of_state_eq hbodySilent.state ca
  have hbodyCode : frame.pre.getCode ca = bodyCursor.pre.getCode ca :=
    getCode_eq_of_state_eq hbodySilent.state ca
  have hprefix : AllowanceRegionEffectSound ca frame.pre bodyCursor.pre
      [CountedFrame.ofFrame dp ca frame] := by
    refine ⟨⟨fun key _hkey => ?_, hbodyCode⟩,
      AllowanceEntryReadSound.ofFrame context.invocation.2.1
        (isFlashInvocation_eq_false_of_ownRecordLast hnotlast)⟩
    rw [applyAllowanceLedger_singleton, hown]
    show (Devm.getStor bodyCursor.pre ca).get key =
      (Devm.getStor frame.pre ca).get key
    exact (congrArg (fun s : Stor => s.get key) hbodyStor).symm
  rw [hstream]
  exact hprefix.append
    ⟨⟨hstorage, hbodyCode.symm.trans
        (Exec.installedCodeEq_committed frame.run frame.committed
          context.installed)⟩,
      hread⟩

/-- `withdrawTo` transports the allowance region read-soundly, exactly as
`withdraw` does with the recipient taken from the address argument. -/
theorem Exec.Frame.allowanceRegionEffectSound_of_withdrawTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    AllowanceRegionEffectSound ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable withdrawTo) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [withdrawToSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorCountedSilent (frame := frame) context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemBody 1 (redeemSendToArgPrefix 0) (Func.last .stop))
    frame.post at bodyCursor
  obtain ⟨hstorage, hread⟩ := bodyCursor.redeemAllowanceSound
    (successLine := []) (target := Sevm.argWord frame.sevm 0)
    context.invocation.2.1 nil_pref
    (by rw [← hbodySilent.memory]; exact context.memory_wf)
    (by rw [← hbodySilent.memory]; exact context.memory_reads_empty)
    (by
      rw [← getCode_eq_of_state_eq hbodySilent.state ca]
      exact context.installed.1)
    (by simp [redeemSendToArgPrefix, pushList, arg, cdl, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToArgPrefix_effect 0 hp hrun)
    (by simp)
    (by func_inv)
    hdeeper
  have hnotlast : ownRecordLast frame.sevm = false := by
    simp [ownRecordLast, isFlashInvocation, isPermitInvocation, hselector,
      withdrawToSelector_ne_flashLoanSelector,
      withdrawToSelector_ne_permitSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post = none
    simp [frameAllowanceEvent, hnonempty, hselector,
      withdrawToSelector_ne_approveSelector,
      withdrawToSelector_ne_approveAndCallSelector,
      withdrawToSelector_ne_permitSelector,
      withdrawToSelector_ne_transferFromSelector,
      withdrawToSelector_ne_withdrawFromSelector,
      withdrawToSelector_ne_flashLoanSelector,
      withdrawToSelector_ne_allowanceSelector]
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotlast]
  have hbodyStor : Devm.getStor frame.pre ca =
      Devm.getStor bodyCursor.pre ca :=
    getStor_eq_of_state_eq hbodySilent.state ca
  have hbodyCode : frame.pre.getCode ca = bodyCursor.pre.getCode ca :=
    getCode_eq_of_state_eq hbodySilent.state ca
  have hprefix : AllowanceRegionEffectSound ca frame.pre bodyCursor.pre
      [CountedFrame.ofFrame dp ca frame] := by
    refine ⟨⟨fun key _hkey => ?_, hbodyCode⟩,
      AllowanceEntryReadSound.ofFrame context.invocation.2.1
        (isFlashInvocation_eq_false_of_ownRecordLast hnotlast)⟩
    rw [applyAllowanceLedger_singleton, hown]
    show (Devm.getStor bodyCursor.pre ca).get key =
      (Devm.getStor frame.pre ca).get key
    exact (congrArg (fun s : Stor => s.get key) hbodyStor).symm
  rw [hstream]
  exact hprefix.append
    ⟨⟨hstorage, hbodyCode.symm.trans
        (Exec.installedCodeEq_committed frame.run frame.committed
          context.installed)⟩,
      hread⟩

/-- The zero-recipient `transfer` branch transports the allowance region
read-soundly, exactly as `withdraw` does. -/
theorem Exec.Frame.allowanceRegionEffectSound_of_transferZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hzero : Sevm.argWord frame.sevm 0 = 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    AllowanceRegionEffectSound ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable transfer) ∈
      weth10Funcs dp := by
    rw [hselector]
    simp [transferSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorCountedSilent (frame := frame) context hnonempty
      hmem with
    ⟨wrapperCursor, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨transferCursor, hnonpayableSilent⟩
  change Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ((arg 0 ++ [iszero]) +++
      (transferZeroThen returnTrue <?> transferNonzeroThen returnTrue))
    frame.post at transferCursor
  rcases transferCursor.peelChildlessLine
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine⟩
  have htargetPrefix : [Sevm.argWord frame.sevm 0 =? 0] <<+
      targetBranchCursor.pre.stack := by
    rcases of_run_append (arg 0) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with ⟨afterZero, hzeroRun, hnil⟩
    cases hnil
    exact prefix_of_iszero hzeroRun (prefix_of_arg nil_pref harg)
  have htargetCheck : (Sevm.argWord frame.sevm 0 =? 0) = 1 := by
    simp [B256.eqCheck, hzero]
  rw [htargetCheck] at htargetPrefix
  rcases targetBranchCursor.selectBranchSuccSilent (flag := (1 : B256))
      (by decide) htargetPrefix with
    ⟨bodyCursor, _hbodyStack, hbranchSilent⟩
  have hlineStor : Devm.getStor transferCursor.pre =
      Devm.getStor targetBranchCursor.pre :=
    Line.of_inv Devm.getStor (by line_inv) htargetLine
  have hlineCode : Devm.getCode transferCursor.pre =
      Devm.getCode targetBranchCursor.pre :=
    Line.of_inv Devm.getCode (by line_inv) htargetLine
  have hlineMem : transferCursor.pre.memory = targetBranchCursor.pre.memory :=
    Line.of_inv Devm.memory (by line_inv) htargetLine
  have hbodyStor : Devm.getStor frame.pre ca =
      Devm.getStor bodyCursor.pre ca :=
    (getStor_eq_of_state_eq hentrySilent.state ca).trans
      ((getStor_eq_of_state_eq hnonpayableSilent.state ca).trans
        ((congrFun hlineStor ca).trans
          (getStor_eq_of_state_eq hbranchSilent.state ca)))
  have hbodyCode : Devm.getCode frame.pre ca =
      Devm.getCode bodyCursor.pre ca :=
    (getCode_eq_of_state_eq hentrySilent.state ca).trans
      ((getCode_eq_of_state_eq hnonpayableSilent.state ca).trans
        ((congrFun hlineCode ca).trans
          (getCode_eq_of_state_eq hbranchSilent.state ca)))
  have hbodyMem : frame.pre.memory = bodyCursor.pre.memory :=
    hentrySilent.memory.trans (hnonpayableSilent.memory.trans
      (hlineMem.trans hbranchSilent.memory))
  change Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (redeemBody 1 redeemSendToCallerPrefix
      (redeemReturnTrueLine +++ Func.last .ret))
    frame.post at bodyCursor
  obtain ⟨hstorage, hread⟩ := bodyCursor.redeemAllowanceSound
    (target := frame.sevm.caller.toB256)
    context.invocation.2.1 nil_pref
    (by rw [← hbodyMem]; exact context.memory_wf)
    (by rw [← hbodyMem]; exact context.memory_reads_empty)
    (by
      rw [← hbodyCode]
      exact context.installed.1)
    (by simp [redeemSendToCallerPrefix, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by
      intro sendPre callPre value tail hp hrun
      exact redeemSendToCallerPrefix_effect hp hrun)
    (by simp [redeemReturnTrueLine, mstoreAt, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by func_inv)
    hdeeper
  have hnotlast : ownRecordLast frame.sevm = false := by
    simp [ownRecordLast, isFlashInvocation, isPermitInvocation, hselector,
      transferSelector_ne_flashLoanSelector,
      transferSelector_ne_permitSelector]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hown : (CountedFrame.ofFrame dp ca frame).allowance = none := by
    show frameAllowanceEvent frame.sevm frame.pre frame.post = none
    simp [frameAllowanceEvent, hnonempty, hselector,
      transferSelector_ne_approveSelector,
      transferSelector_ne_approveAndCallSelector,
      transferSelector_ne_permitSelector,
      transferSelector_ne_transferFromSelector,
      transferSelector_ne_withdrawFromSelector,
      transferSelector_ne_flashLoanSelector,
      transferSelector_ne_allowanceSelector]
  have hstream : Exec.attributionStream dp ca frame.run =
      CountedFrame.ofFrame dp ca frame ::
        Exec.attributionInner dp ca frame.run := by
    rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
        frame.committed, hframe,
      Exec.frameContribution_eq_cons dp ca frame
        (Exec.attributionInner dp ca frame.run) context.invocation hnotlast]
  have hprefix : AllowanceRegionEffectSound ca frame.pre bodyCursor.pre
      [CountedFrame.ofFrame dp ca frame] := by
    refine ⟨⟨fun key _hkey => ?_, hbodyCode⟩,
      AllowanceEntryReadSound.ofFrame context.invocation.2.1
        (isFlashInvocation_eq_false_of_ownRecordLast hnotlast)⟩
    rw [applyAllowanceLedger_singleton, hown]
    show (Devm.getStor bodyCursor.pre ca).get key =
      (Devm.getStor frame.pre ca).get key
    exact (congrArg (fun s : Stor => s.get key) hbodyStor).symm
  rw [hstream]
  exact hprefix.append
    ⟨⟨hstorage, hbodyCode.symm.trans
        (Exec.installedCodeEq_committed frame.run frame.committed
          context.installed)⟩,
      hread⟩


end Weth10

end Blanc
