import Blanc.Weth10AllowanceArmsRedeem
import Blanc.Weth10PermitRawEffect
import Blanc.Weth10StaticSilence

/-!
The ERC-2612 `permit` arm of the allowance-region transport.

A committed `permit` frame checks the deadline, reads and tentatively
increments the tagged nonce, hashes the typed struct, dispatches on the
cached domain separator, and tail-calls `permitRecover`, whose single
`STATICCALL` to precompile address `1` is the only spawn-capable
instruction on the path; the surviving signer-guard branches end in the
`approvePermit` store at the key hashed from the raw owner/spender words.

The counted walk below mirrors that path on the `CountedCursor` altitude,
reaching that `STATICCALL` unconditionally.  Two readings of the crossing
follow from the same walk.

* Under the two precompile-resolution hypotheses — address `1` enabled in
  the static fork rules and no EIP-7702 delegation designator installed on
  it — the call resolves synchronously and the frame retains no
  proper-descendant counted record at all.
* Without them a delegated interpreted child is live in the model, but it
  is a `STATICCALL` child and therefore static, so `Weth10StaticSilence`
  makes its whole counted contribution *write-free*, and the arm's raw
  storage image survives once the crossing is discharged from the
  recursion hypothesis instead.

The arm itself takes the second reading, so no routing premise reaches the
history-level statement: its hypotheses are exactly those of the sibling
callback arms.  The branch and internal-call crossings still expose the
code map, which the first reading needs to carry its no-delegation
hypothesis from frame entry to the exact call boundary.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## Counted crossings that expose the code map and the allowance region

The counted cursor API of `Weth10AttributionChronology` exposes no state
facts across generated branch and internal-call scaffolding, so this
module rebuilds the crossings it needs with two observations attached: the
code map, along which the no-delegation hypothesis stated at frame entry
rides to the exact `STATICCALL` boundary, and the tagged allowance region of
the frame's own account, which the read-sound arm needs at that same
boundary.  Every generated crossing is silent, so both come from one state
equality. -/

private theorem getCode_map_eq_of_state_eq {pre post : Devm}
    (h : pre.state = post.state) :
    Devm.getCode pre = Devm.getCode post :=
  funext (getCode_eq_of_state_eq h)

/-- Two states agree on the current target's tagged allowance region.  This
is the observation the read-sound `permit` arm carries from frame entry to
the recovery `STATICCALL`: every line before that boundary is
storage-invariant except the tentative nonce increment, whose key is
separated from every tagged allowance key. -/
private def AllowanceAgree (sevm : Sevm) (u v : Devm) : Prop :=
  ∀ key, InRegion .allowance key →
    (Devm.getStor v sevm.currentTarget).get key =
      (Devm.getStor u sevm.currentTarget).get key

private theorem AllowanceAgree.refl' {sevm : Sevm} {u : Devm} :
    AllowanceAgree sevm u u := fun _ _ => rfl

private theorem AllowanceAgree.trans {sevm : Sevm} {u v w : Devm}
    (h₁ : AllowanceAgree sevm u v) (h₂ : AllowanceAgree sevm v w) :
    AllowanceAgree sevm u w :=
  fun key hkey => (h₂ key hkey).trans (h₁ key hkey)

private theorem AllowanceAgree.of_stor_eq {sevm : Sevm} {u v : Devm}
    (h : Devm.getStor u = Devm.getStor v) : AllowanceAgree sevm u v :=
  fun _ _ => by rw [congrFun h sevm.currentTarget]

private theorem AllowanceAgree.of_state_eq {sevm : Sevm} {u v : Devm}
    (h : u.state = v.state) : AllowanceAgree sevm u v :=
  .of_stor_eq (funext (getStor_eq_of_state_eq h))

/-- Transport a counted cursor across a named source equality while retaining
its exact entry state. -/
private theorem Exec.Frame.CountedCursor.castSourceFrame
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {source target : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca fs table
      source final)
    (hsource : source = target) :
    ∃ targetCursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca fs table
        target final,
      targetCursor.pre = cursor.pre := by
  subst target
  exact ⟨cursor, rfl⟩

/-- Select whichever branch arm the committed run actually took, exposing
the crossing's code map and allowance region; the silent-frame projection of
`Exec.Frame.CountedCursor.selectBranchSplitSilent`. -/
private theorem Exec.Frame.CountedCursor.selectBranchSplitFrame
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca fs table
      (.branch left right) final) :
    (∃ arm : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca fs table left final,
      Devm.getCode cursor.pre = Devm.getCode arm.pre ∧
      AllowanceAgree frame.sevm cursor.pre arm.pre) ∨
    (∃ arm : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca fs table right final,
      Devm.getCode cursor.pre = Devm.getCode arm.pre ∧
      AllowanceAgree frame.sevm cursor.pre arm.pre) := by
  rcases cursor.selectBranchSplitSilent with ⟨arm, hsilent⟩ | ⟨arm, hsilent⟩
  · exact Or.inl ⟨arm, getCode_map_eq_of_state_eq hsilent.state,
      AllowanceAgree.of_state_eq hsilent.state⟩
  · exact Or.inr ⟨arm, getCode_map_eq_of_state_eq hsilent.state,
      AllowanceAgree.of_state_eq hsilent.state⟩

/-- Follow one generated internal source call, exposing the crossing's code
map and allowance region; the silent-frame projection of
`Exec.Frame.CountedCursor.enterCallSilent`. -/
private theorem Exec.Frame.CountedCursor.enterCallFrame
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca (f₀ :: aux)
        (table 0 (f₀ :: aux)) body final,
        Devm.getCode cursor.pre = Devm.getCode bodyCursor.pre ∧
        AllowanceAgree frame.sevm cursor.pre bodyCursor.pre := by
  rcases cursor.enterCallSilent hcode with
    ⟨body, hget, bodyCursor, hsilent⟩
  exact ⟨body, hget, bodyCursor, getCode_map_eq_of_state_eq hsilent.state,
    AllowanceAgree.of_state_eq hsilent.state⟩

/-! ## The `STATICCALL` crossing

The permit body's single spawn-capable instruction.  Under the enabled
precompile and absent delegation designator, the frame's `Exec` derivation
cannot cross it on an interpreted-child edge, and both surviving edge
kinds carry the empty counted label. -/

/-- The consequences of one spawned permit `STATICCALL` step needed here:
the spawned frame is the call frame of a message whose code address is the
ECRECOVER precompile, whose static block environment is the caller's, and
whose precompile-disable flag is exactly the delegation resolution against
the step's entry code. -/
private def StatcallSpawnFacts
    (sevm : Sevm) (pre : Devm) (frame : Frame) : Prop :=
  ∃ msg : Msg,
    frame = Frame.ofCall msg ∧
    msg.codeAddress = some (1 : B256).toAdr ∧
    msg.benv.stat = sevm.benvStat ∧
    ((getDelegatedCodeAddress (pre.getCode (1 : B256).toAdr) = none ∧
        msg.code = pre.getCode (1 : B256).toAdr ∧
        msg.disablePrecompiles = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (pre.getCode (1 : B256).toAdr) =
          some delegatedTarget ∧
        msg.code = pre.getCode delegatedTarget ∧
        msg.disablePrecompiles = true))

private theorem Xinst.step_statcall_spawn_facts
    {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume}
    (gasWord : B256) (tail : Stack)
    (operands : gasWord :: (1 : B256) :: (0 : B256) ::
      (128 : B256) :: (128 : B256) :: (32 : B256) :: tail <<+
        devm.stack)
    (hspawn : Xinst.step sevm devm .statcall = .spawn frame resume) :
    StatcallSpawnFacts sevm devm frame := by
  simp only [Xinst.step, Bind.bind, Except.bind] at hspawn
  rcases eq1 : Devm.pop devm with err | ⟨actualGasWord, d1⟩ <;>
    simp only [eq1] at hspawn
  · cases hspawn
  have f1 := Devm.pop_of_pop eq1
  have e1 := f1.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rw [e1] at operands
  have hgas : gasWord = actualGasWord :=
    pref_head_unique operands (pref_append [actualGasWord] d1.stack)
  subst actualGasWord
  replace operands := cons_pref_cons_inv operands
  rcases eq2 : Devm.popToAdr d1 with err | ⟨target, d2⟩ <;>
    simp only [eq2] at hspawn
  · cases hspawn
  rcases Devm.pop_of_popToAdr eq2 with
    ⟨targetWord, htargetWord, hpop2⟩
  have f2 := Devm.pop_of_pop hpop2
  have e2 := f2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rw [e2] at operands
  have htarget : (1 : B256) = targetWord :=
    pref_head_unique operands (pref_append [targetWord] d2.stack)
  subst targetWord
  subst target
  rcases eq3 : Devm.popToNat d2 with err | ⟨inputIndex, d3⟩ <;>
    simp only [eq3] at hspawn
  · cases hspawn
  have f3 := Devm.popToNat_worldEq_of_ok eq3
  rcases eq4 : Devm.popToNat d3 with err | ⟨inputSize, d4⟩ <;>
    simp only [eq4] at hspawn
  · cases hspawn
  have f4 := Devm.popToNat_worldEq_of_ok eq4
  rcases eq5 : Devm.popToNat d4 with err | ⟨outputIndex, d5⟩ <;>
    simp only [eq5] at hspawn
  · cases hspawn
  have f5 := Devm.popToNat_worldEq_of_ok eq5
  rcases eq6 : Devm.popToNat d5 with err | ⟨outputSize, d6⟩ <;>
    simp only [eq6] at hspawn
  · cases hspawn
  have f6 := Devm.popToNat_worldEq_of_ok eq6
  have hpre6 : devm.state = d6.state :=
    f1.state.trans (f2.state.trans (f3.1.trans
      (f4.1.trans (f5.1.trans f6.1))))
  rcases hdelegation :
      accessDelegation (addAccessedAddress d6 (1 : B256).toAdr)
        (1 : B256).toAdr with
    ⟨delegated, delegatedAddress, code, delegationGas, d8⟩
  simp only [hdelegation] at hspawn
  have hcodeAt :
      (addAccessedAddress d6 (1 : B256).toAdr).state.getCode
          (1 : B256).toAdr = devm.getCode (1 : B256).toAdr := by
    show d6.state.getCode (1 : B256).toAdr =
      devm.state.getCode (1 : B256).toAdr
    rw [← hpre6]
  have hresolution :
      (getDelegatedCodeAddress (devm.getCode (1 : B256).toAdr) = none ∧
          code = devm.getCode (1 : B256).toAdr ∧ delegated = false) ∨
        (∃ delegatedTarget,
          getDelegatedCodeAddress (devm.getCode (1 : B256).toAdr) =
            some delegatedTarget ∧
          code = devm.getCode delegatedTarget ∧ delegated = true) := by
    have haccess := hdelegation
    dsimp only [accessDelegation] at haccess
    rw [hcodeAt] at haccess
    rcases hdelegate :
        getDelegatedCodeAddress (devm.getCode (1 : B256).toAdr) with
          _ | target <;>
      rw [hdelegate] at haccess <;>
      simp only [Prod.mk.injEq] at haccess
    · exact Or.inl ⟨rfl, haccess.2.2.1.symm, haccess.1.symm⟩
    · refine Or.inr ⟨target, rfl, ?_, haccess.1.symm⟩
      rw [← haccess.2.2.1]
      show (addAccessedAddress d6 (1 : B256).toAdr).state.getCode target =
        devm.state.getCode target
      show d6.state.getCode target = devm.state.getCode target
      rw [← hpre6]
  split at hspawn
  · cases hspawn
  rename_i d9 hcharge
  have hframe := (genericCall_step_spawn_exact hspawn).1
  subst frame
  exact ⟨_, rfl, rfl, rfl, by simpa only [callMsg] using hresolution⟩

private theorem Ninst.step_statcall_spawn_facts
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume}
    (gasWord : B256) (tail : Stack)
    (operands : gasWord :: (1 : B256) :: (0 : B256) ::
      (128 : B256) :: (128 : B256) :: (32 : B256) :: tail <<+
        pre.stack)
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.statcall =
      .spawn frame resume pc') :
    StatcallSpawnFacts sevm pre frame := by
  have hx : Xinst.step sevm pre .statcall = .spawn frame resume := by
    exact XStep.toStep_spawn (by
      simpa only [Ninst.statcall, Ninst.step_exec] using hspawn)
  exact Xinst.step_statcall_spawn_facts gasWord tail operands hx

/-- Value transfer preserves the static block environment. -/
private theorem benvAfterTransfer_stat {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) :
    benv.stat = msg.benv.stat := by
  cases htransfer : msg.shouldTransferValue with
  | false =>
      have hnot : ¬ msg.shouldTransferValue = true := by
        simp [htransfer]
      have hbenv := of_benvAfterTransfer_no hnot h
      subst benv
      rfl
  | true =>
      rcases of_benvAfterTransfer htransfer h with ⟨debit, hsub, rfl⟩
      rfl

/-- No interpreted child can be spawned at the permit call boundary when
the precompile is enabled and undelegated: frame entry would resolve the
message synchronously. -/
private theorem not_run_of_statcallSpawnFacts
    {sevm : Sevm} {pre : Devm} {f : Frame} {childEvm : Evm}
    (hprecomp :
      decide (sevm.benvStat.rules.isPrecomp (1 : B256).toAdr) = true)
    (hnodeleg :
      getDelegatedCodeAddress (pre.getCode (1 : B256).toAdr) = none)
    (hfacts : StatcallSpawnFacts sevm pre f)
    (henter : f.enter = .run childEvm) : False := by
  rcases hfacts with ⟨msg, rfl, hca, hstat, hres⟩
  have hdisable : msg.disablePrecompiles = false := by
    rcases hres with ⟨-, -, hdisable⟩ | ⟨d, hd, -, -⟩
    · exact hdisable
    · rw [hnodeleg] at hd
      cases hd
  have hrf : RunFrame (Frame.ofCall msg)
      (.some ⟨childEvm, .ok pre⟩)
      ((Frame.ofCall msg).settle (.ok pre)) :=
    RunFrame.of_run henter
  have hpm : ProcessMessage msg (.some ⟨childEvm, .ok pre⟩)
      ((Frame.ofCall msg).settle (.ok pre)) := hrf
  rcases ProcessMessage.iff_body.mp hpm with ⟨r0, hbody, -⟩
  unfold FrameBody at hbody
  rcases hbt : msg.benvAfterTransfer with e | benv <;>
    rw [hbt] at hbody
  · cases hbody.1
  · have hca' : (msg.withBenv benv).codeAddress =
        some (1 : B256).toAdr := hca
    rcases of_executeCode_someCode hca' hbody with
      ⟨-, hxl, -⟩ | ⟨hcond, -⟩
    · cases hxl
    · apply hcond
      have hdisable' : (msg.withBenv benv).disablePrecompiles = false :=
        hdisable
      have hstat' : (msg.withBenv benv).benv.stat = sevm.benvStat := by
        show benv.stat = sevm.benvStat
        rw [benvAfterTransfer_stat hbt, hstat]
      rw [hdisable', hstat', hprecomp]
      rfl

/-- An enabled undelegated permit `STATICCALL` edge carries no counted
records: the interpreted-child arm is impossible, and the remaining arms
are label-free. -/
private theorem Exec.Deriv.ParentStepActions.counted_of_permitStatcall
    {dp : DeployParams} {ca : Adr}
    {next current : Exec.Deriv} {selected : List FlowAction}
    (edge : Exec.Deriv.ParentStepActions dp ca next current selected)
    (hat : Ninst.At current.sevm.code current.pc Ninst.statcall)
    (hprecomp : decide
      (current.sevm.benvStat.rules.isPrecomp (1 : B256).toAdr) = true)
    (hnodeleg : getDelegatedCodeAddress
      (Devm.getCode current.devm (1 : B256).toAdr) = none)
    {gasWord : B256} {stack : Stack}
    (operands : gasWord :: (1 : B256) :: (0 : B256) :: (128 : B256) ::
      (128 : B256) :: (32 : B256) :: stack <<+ current.devm.stack) :
    Exec.Deriv.ParentStepCounted dp ca next current [] := by
  cases edge with
  | cont hstep next => exact .cont hstep next
  | doneOk hstep henter hresume next =>
      exact .doneOk hstep henter hresume next
  | runOk hstep henter child hresume next =>
      exfalso
      have hspawn := (Evm.step_next hat).symm.trans hstep
      have hfacts :=
        Ninst.step_statcall_spawn_facts gasWord stack operands hspawn
      exact not_run_of_statcallSpawnFacts hprecomp hnodeleg hfacts henter

/-- Cross the permit `STATICCALL` while preserving the empty counted
prefix.  With the precompile enabled and undelegated the crossing's
counted label is empty whichever arm the original run selected. -/
private theorem Exec.Frame.CountedCursor.crossPermitStaticcall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {tail : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca fs table
      (.next Ninst.statcall tail) final)
    (hprecomp : decide
      (frame.sevm.benvStat.rules.isPrecomp (1 : B256).toAdr) = true)
    (hnodeleg : getDelegatedCodeAddress
      (Devm.getCode cursor.pre (1 : B256).toAdr) = none)
    {gasWord : B256} {stack : Stack}
    (operands : gasWord :: (1 : B256) :: (0 : B256) :: (128 : B256) ::
      (128 : B256) :: (32 : B256) :: stack <<+ cursor.pre.stack) :
    Nonempty (Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca fs table tail final) := by
  have compiled := cursor.run
  cases compiled with
  | next hcompiled htail =>
      have hat : Ninst.At frame.sevm.code cursor.pc Ninst.statcall :=
        ninstAt_of_subcode_next cursor.codeSlice
      rcases cursor.parentPrefix with ⟨before, hbefore⟩
      rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_next (frame := frame) cursor.current hbefore hat
          hcompiled with
        ⟨xl, continuation, selected, _occurrence, hedge, hnextPrefix⟩
      have hcountedEdge :=
        hedge.counted_of_permitStatcall hat hprecomp hnodeleg operands
      obtain ⟨nextBoundary, nextSub⟩ :=
        Func.noPushBefore_next cursor.codeSlice cursor.codeBoundary
      exact ⟨⟨cursor.pc + Ninst.statcall.size, _, continuation,
        ⟨_, hnextPrefix⟩, cursor.countedPrefix.snoc hcountedEdge, htail,
        nextSub, nextBoundary⟩⟩

/-- A successful counted cursor at a nonpayable wrapper reaches its guarded
body, exposing the crossing's code map and allowance region; the
silent-frame projection of
`Exec.Frame.CountedCursor.enterNonpayableSilent`. -/
private theorem Exec.Frame.CountedCursor.enterNonpayableFrame
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca fs table
      (nonpayable body) final) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca fs table body final,
      Devm.getCode cursor.pre = Devm.getCode bodyCursor.pre ∧
      AllowanceAgree frame.sevm cursor.pre bodyCursor.pre := by
  rcases cursor.enterNonpayableSilent with ⟨bodyCursor, hsilent⟩
  exact ⟨bodyCursor, getCode_map_eq_of_state_eq hsilent.state,
    AllowanceAgree.of_state_eq hsilent.state⟩

/-! ## The parent-only suffix after the static child -/

/-- Complete the signer/approval suffix after the `STATICCALL`: the two
rejected arms are fixed reverters, so the retained path ends in the
childless `approvePermit` store and the frame's proper-descendant counted
stream is empty. -/
private theorem Exec.Frame.CountedCursor.finishPermitAfterStaticcall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      permitAfterStaticcall frame.post) :
    Exec.attributionInner dp ca frame.run = [] := by
  unfold permitAfterStaticcall at cursor
  rcases cursor.peelChildlessLine (line := permitFirstSignerGuardLine)
      (by simp [permitFirstSignerGuardLine, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨firstBranchCursor, -⟩
  rcases firstBranchCursor.selectBranchSplitFrame with hsecond | herror
  · rcases hsecond with ⟨secondGuardCursor, -, -⟩
    rcases secondGuardCursor.peelChildlessLine
        (line := permitSecondSignerGuardLine)
        (by simp [permitSecondSignerGuardLine, arg, cdl,
          NinstIsChildless, Ninst.pushB256]) with
      ⟨secondBranchCursor, -⟩
    rcases secondBranchCursor.selectBranchSplitFrame with happrove | herror
    · rcases happrove with ⟨approveCursor, -, -⟩
      have approveCursor' : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux))
          (approvePermitLine +++ Func.stop) frame.post :=
        approvePermit_shape ▸ approveCursor
      rcases approveCursor'.peelChildlessLine
          (by simp [approvePermitLine, argCopy, cdc,
            allowanceKeyFromMemory, pushList, Blanc.arg, cdl, mstoreAt,
            logWith, NinstIsChildless, Ninst.pushB256]) with
        ⟨lastCursor, -⟩
      exact lastCursor.finishAttributionInner
    · rcases herror with ⟨errorCursor, -, -⟩
      have hrun := Func.Run.of_runCompiled errorCursor.run
      cases hrun with
      | call hget _hburn hbody =>
          have hbody' := hbody
          rw [show ((weth10 dp).main :: weth10Aux)[invalidPermitErrorSlot]? =
              some invalidPermitError from by
            simp [weth10Aux, invalidPermitErrorSlot]] at hget
          cases Option.some.inj hget
          exact absurd hbody' Func.not_run_revWith
  · rcases herror with ⟨errorCursor, -, -⟩
    have hrun := Func.Run.of_runCompiled errorCursor.run
    cases hrun with
    | call hget _hburn hbody =>
        have hbody' := hbody
        rw [show ((weth10 dp).main :: weth10Aux)[invalidPermitErrorSlot]? =
            some invalidPermitError from by
          simp [weth10Aux, invalidPermitErrorSlot]] at hget
        cases Option.some.inj hget
        exact absurd hbody' Func.not_run_revWith

/-! ## The unconditional reading of the crossing

Dropping the two routing premises makes the interpreted-child arm live, so
the crossing's counted label is no longer empty.  It is still *write-free*:
a `STATICCALL` child is static whatever address `1` resolves to, and
`Weth10StaticSilence` shows that no counted frame retained under `STATIC`
commits an allowance word. -/

/-- Whatever the permit `STATICCALL` edge turns out to be, its counted label
is write-free. -/
private theorem Exec.Deriv.ParentStepCounted.writeFree_of_statcall
    {dp : DeployParams} {ca : Adr}
    {next current : Exec.Deriv} {counted : List CountedFrame}
    (edge : Exec.Deriv.ParentStepCounted dp ca next current counted)
    (hat : Ninst.At current.sevm.code current.pc Ninst.statcall) :
    WriteFreeLedger counted := by
  cases edge with
  | cont => exact writeFreeLedger_nil
  | doneOk => exact writeFreeLedger_nil
  | runOk hstep henter child _hresume _next =>
      exact writeFreeLedger_statcallCrossing
        ((Evm.step_next hat).symm.trans hstep) henter child

/-- Cross the permit `STATICCALL` with no routing premise at all: its counted
label is write-free, and the parent-only suffix behind it retains nothing, so
the frame's whole proper-descendant counted stream is write-free.  The suffix
closer is supplied by the caller and applied at the *continuation* re-rooted
as its own frame, whose counted prefix is empty by construction. -/
private theorem
    Exec.Frame.CountedCursor.attributionInner_writeFree_of_statcall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)} {tail : Func}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca fs table
      (.next Ninst.statcall tail) frame.post)
    (hfinish : ∀ suffixFrame : Exec.Frame,
      Blanc.Weth10.Exec.Frame.CountedCursor
        (frame := suffixFrame) dp ca fs table tail suffixFrame.post →
      Exec.attributionInner dp ca suffixFrame.run = []) :
    WriteFreeLedger (Exec.attributionInner dp ca frame.run) := by
  have compiled := cursor.run
  cases compiled with
  | next hcompiled htail =>
      rename_i stepPost
      have hat : Ninst.At frame.sevm.code cursor.pc Ninst.statcall :=
        ninstAt_of_subcode_next cursor.codeSlice
      obtain ⟨nextBoundary, nextSub⟩ :=
        Func.noPushBefore_next cursor.codeSlice cursor.codeBoundary
      rcases cursor.parentPrefix with ⟨before, hbefore⟩
      rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_next (frame := frame) cursor.current hbefore hat
          hcompiled with
        ⟨_xl, continuation, _selected, _occurrence, hedge, _hnextPrefix⟩
      rcases hedge.exists_counted with ⟨counted, hcountedEdge⟩
      have hlabel : WriteFreeLedger counted :=
        hcountedEdge.writeFree_of_statcall hat
      have htailNil : Exec.attributionInner dp ca continuation = [] :=
        hfinish ⟨cursor.pc + Ninst.statcall.size, frame.sevm, stepPost,
            frame.out, continuation, frame.committed⟩
          ⟨cursor.pc + Ninst.statcall.size, stepPost, continuation,
            ⟨[], .refl _⟩, .refl _, htail, nextSub, nextBoundary⟩
      have hprefixSplit := cursor.countedPrefix.descendantCounted_eq
      change Exec.attributionInner dp ca frame.run =
        [] ++ Exec.attributionInner dp ca cursor.current at hprefixSplit
      have hedgeSplit := hcountedEdge.descendantCounted_eq
      change Exec.attributionInner dp ca cursor.current =
        counted ++ Exec.attributionInner dp ca continuation at hedgeSplit
      rw [hprefixSplit, List.nil_append, hedgeSplit, htailNil,
        List.append_nil]
      exact hlabel

/-! ## The read-sound reading of the crossing

Write-freeness settles the ledger *replay* across the crossing but says
nothing about what a record retained inside the subtree actually read, so the
entry-read clause needs a second reading.  It is the reading the sibling
callback arms already use: the recursion hypothesis carries the whole child
subtree — read-soundly — against the parent's storage at the call boundary.
Nothing below mentions address `1`, staticness, or any routing premise; a
`STATICCALL` is treated exactly like the `CALL` a callback arm crosses. -/

/-- The message-level consequences of one spawned `STATICCALL` step needed to
feed the recursion hypothesis: the spawned frame is the call frame of a
message entered at the popped target, whose block-environment state is the
step's entry state, whose depth is strictly smaller than the caller's, and
whose code is the delegation resolution of the target's entry code. -/
private def StatcallSpawnMessage
    (sevm : Sevm) (pre : Devm) (frame : Frame) : Prop :=
  ∃ (msg : Msg) (target : Adr) (delegated : Bool),
    frame = Frame.ofCall msg ∧
    msg.currentTarget = target ∧
    msg.codeAddress = some target ∧
    msg.benv.state = pre.state ∧
    msg.depth < sevm.depth ∧
    ((getDelegatedCodeAddress (pre.getCode target) = none ∧
        msg.code = pre.getCode target ∧ delegated = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (pre.getCode target) = some delegatedTarget ∧
        msg.code = pre.getCode delegatedTarget ∧ delegated = true))

/-- A `CALL`-family child is spawned only from a nonzero depth: the exhausted
depth short-circuits to a pushed zero instead. -/
private theorem genericCall.step_spawn_depth_pos
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dpFlag : Bool}
    {f : Jaune.Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress
      stv isSt ii isz oi osz code dpFlag = .spawn f rsm) :
    0 < sevm.depth := by
  rcases Nat.eq_zero_or_pos sevm.depth with hzero | hpos
  · exfalso
    simp only [genericCall.step, hzero, Bind.bind, Except.bind, Pure.pure,
      Except.pure, reduceIte] at hs
    split at hs <;> simp only [XStep.ofExcept, reduceCtorEq] at hs
  · exact hpos

private theorem Xinst.step_statcall_spawn_message
    {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume}
    (hspawn : Xinst.step sevm devm .statcall = .spawn frame resume) :
    StatcallSpawnMessage sevm devm frame := by
  simp only [Xinst.step, Bind.bind, Except.bind] at hspawn
  rcases eq1 : Devm.pop devm with err | ⟨gasWord, d1⟩ <;>
    simp only [eq1] at hspawn
  · cases hspawn
  have f1 := Devm.pop_of_pop eq1
  rcases eq2 : Devm.popToAdr d1 with err | ⟨target, d2⟩ <;>
    simp only [eq2] at hspawn
  · cases hspawn
  rcases Devm.pop_of_popToAdr eq2 with ⟨targetWord, _htargetWord, hpop2⟩
  have f2 := Devm.pop_of_pop hpop2
  rcases eq3 : Devm.popToNat d2 with err | ⟨inputIndex, d3⟩ <;>
    simp only [eq3] at hspawn
  · cases hspawn
  have f3 := Devm.popToNat_worldEq_of_ok eq3
  rcases eq4 : Devm.popToNat d3 with err | ⟨inputSize, d4⟩ <;>
    simp only [eq4] at hspawn
  · cases hspawn
  have f4 := Devm.popToNat_worldEq_of_ok eq4
  rcases eq5 : Devm.popToNat d4 with err | ⟨outputIndex, d5⟩ <;>
    simp only [eq5] at hspawn
  · cases hspawn
  have f5 := Devm.popToNat_worldEq_of_ok eq5
  rcases eq6 : Devm.popToNat d5 with err | ⟨outputSize, d6⟩ <;>
    simp only [eq6] at hspawn
  · cases hspawn
  have f6 := Devm.popToNat_worldEq_of_ok eq6
  have hpre6 : devm.state = d6.state :=
    f1.state.trans (f2.state.trans (f3.1.trans
      (f4.1.trans (f5.1.trans f6.1))))
  rcases hdelegation :
      accessDelegation (addAccessedAddress d6 target) target with
    ⟨delegated, delegatedAddress, code, delegationGas, d8⟩
  simp only [hdelegation] at hspawn
  have hcodeAt :
      (addAccessedAddress d6 target).state.getCode target =
        devm.getCode target := by
    show d6.state.getCode target = devm.state.getCode target
    rw [← hpre6]
  have hresolution :
      ((getDelegatedCodeAddress (devm.getCode target) = none ∧
          code = devm.getCode target ∧ delegated = false) ∨
        (∃ delegatedTarget,
          getDelegatedCodeAddress (devm.getCode target) =
            some delegatedTarget ∧
          code = devm.getCode delegatedTarget ∧ delegated = true)) ∧
      d8.state = devm.state := by
    have haccess := hdelegation
    dsimp only [accessDelegation] at haccess
    rw [hcodeAt] at haccess
    rcases hdelegate : getDelegatedCodeAddress (devm.getCode target) with
        _ | tgt <;>
      rw [hdelegate] at haccess <;>
      simp only [Prod.mk.injEq] at haccess
    · refine ⟨Or.inl ⟨rfl, haccess.2.2.1.symm, haccess.1.symm⟩, ?_⟩
      rw [← haccess.2.2.2.2]
      show d6.state = devm.state
      rw [← hpre6]
    · refine ⟨Or.inr ⟨tgt, rfl, ?_, haccess.1.symm⟩, ?_⟩
      · rw [← haccess.2.2.1]
        show (addAccessedAddress d6 target).state.getCode tgt =
          devm.state.getCode tgt
        show d6.state.getCode tgt = devm.state.getCode tgt
        rw [← hpre6]
      · rw [← haccess.2.2.2.2]
        show d6.state = devm.state
        rw [← hpre6]
  split at hspawn
  · cases hspawn
  rename_i d9 hcharge
  have hd9 : d9.state = devm.state :=
    (chargeGas_worldEq_of_ok hcharge).1.symm.trans hresolution.2
  have hdepth := genericCall.step_spawn_depth_pos hspawn
  have hframe := (genericCall_step_spawn_exact hspawn).1
  subst frame
  refine ⟨_, target, delegated, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · show ((d9.memExtends _).withReturnData []).state = devm.state
    exact hd9
  · show sevm.depth - 1 < sevm.depth
    omega
  · simpa only [callMsg] using hresolution.1

private theorem Ninst.step_statcall_spawn_message
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume}
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.statcall =
      .spawn frame resume pc') :
    StatcallSpawnMessage sevm pre frame := by
  have hx : Xinst.step sevm pre .statcall = .spawn frame resume :=
    XStep.toStep_spawn (by
      simpa only [Ninst.statcall, Ninst.step_exec] using hspawn)
  exact Xinst.step_statcall_spawn_message hx

/-- Whatever the permit `STATICCALL` edge turns out to be, every record its
counted label retains read the word the parent's storage held at the call
boundary.  The interpreted-child arm is discharged by the read-sound
recursion hypothesis, exactly as a callback arm discharges its `CALL`; the
label-free arms are vacuous. -/
private theorem entryReadSound_statcallCrossing
    {dp : DeployParams} {ca : Adr}
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {f : Jaune.Frame} {rsm : Resume} {cevm : Evm} {raw : Execution}
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.statcall = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (installed : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt sevm.depth ca (weth10 dp)
      (fun p s d out _ => Exec.CoreAllowanceReadSound dp ca p s d out)) :
    AllowanceEntryReadSound (Devm.getStor pre ca)
      (if h : Blanc.Frame.settlementCommits f raw = true then
        Exec.frameContribution dp ca
          (Exec.Frame.ofRun child
            (Blanc.Frame.raw_commits_of_settlementCommits h))
          (Exec.attributionInner dp ca child)
       else []) := by
  by_cases hcommit : Blanc.Frame.settlementCommits f raw = true
  · rw [dif_pos hcommit]
    have hcommits :=
      Blanc.Frame.raw_commits_of_settlementCommits hcommit
    have hstream : Exec.attributionStream dp ca child =
        Exec.frameContribution dp ca (Exec.Frame.ofRun child hcommits)
          (Exec.attributionInner dp ca child) := by
      unfold Exec.attributionStream
      rw [dif_pos hcommits]
    rw [← hstream]
    obtain ⟨msg, target, delegated, hframe, hcurrent, hcodeAddress, hstate,
      hdepth, hres⟩ := Ninst.step_statcall_spawn_message hspawn
    have hrun : RunFrame f (some (cevm, raw)) (f.settle raw) :=
      RunFrame.of_run henter
    rcases hsettle : Jaune.Frame.settle f raw with err | settled
    · rw [Blanc.Frame.settlementCommits, hsettle] at hcommit
      exact absurd hcommit (by simp)
    · rw [hsettle] at hrun
      subst hframe
      have hpm : ProcessMessage msg (some (cevm, raw)) (.ok settled) := hrun
      have hchild :=
        ProcessMessageTrace.allowanceRegionDeltaSound_of_forallDeeperAt
          (dp := dp) (ca := ca) (depth := sevm.depth) (parent := pre)
          ⟨_, RetainedXlot.some child, hpm⟩ hstate.symm hdepth installed
          (fun hct =>
            callbackCode_eq_compiled_of_target_eq installed
              (hcurrent.symm.trans hct) hres)
          (fun hct => by rw [hcodeAddress, ← hcurrent, hct])
          hdeeper
      exact hchild.entryRead
  · rw [dif_neg hcommit]
    exact .nil _

/-- Read-sound reading of one permit `STATICCALL` edge, in the shape the
counted walk consumes; the entry-read sibling of
`Exec.Deriv.ParentStepCounted.writeFree_of_statcall`. -/
private theorem Exec.Deriv.ParentStepCounted.entryReadSound_of_statcall
    {dp : DeployParams} {ca : Adr}
    {next current : Exec.Deriv} {counted : List CountedFrame}
    (edge : Exec.Deriv.ParentStepCounted dp ca next current counted)
    (hat : Ninst.At current.sevm.code current.pc Ninst.statcall)
    (installed :
      some (current.devm.getCode ca).toList = Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt current.sevm.depth ca (weth10 dp)
      (fun p s d out _ => Exec.CoreAllowanceReadSound dp ca p s d out)) :
    AllowanceEntryReadSound (Devm.getStor current.devm ca) counted := by
  cases edge with
  | cont => exact .nil _
  | doneOk => exact .nil _
  | runOk hstep henter child _hresume _next =>
      exact entryReadSound_statcallCrossing
        ((Evm.step_next hat).symm.trans hstep) henter child installed hdeeper

/-- Cross the permit `STATICCALL` read-soundly with no routing premise: the
crossing's counted label is entry-read sound against the boundary storage,
and the parent-only suffix behind it retains nothing, so the frame's whole
proper-descendant counted stream is entry-read sound there.  The entry-read
sibling of `attributionInner_writeFree_of_statcall`, with the same suffix
closer supplied by the caller. -/
private theorem
    Exec.Frame.CountedCursor.attributionInner_entryReadSound_of_statcall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)} {tail : Func}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca fs table
      (.next Ninst.statcall tail) frame.post)
    (installed :
      some (cursor.pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun p s d out _ => Exec.CoreAllowanceReadSound dp ca p s d out))
    (hfinish : ∀ suffixFrame : Exec.Frame,
      Blanc.Weth10.Exec.Frame.CountedCursor
        (frame := suffixFrame) dp ca fs table tail suffixFrame.post →
      Exec.attributionInner dp ca suffixFrame.run = []) :
    AllowanceEntryReadSound (Devm.getStor cursor.pre ca)
      (Exec.attributionInner dp ca frame.run) := by
  have compiled := cursor.run
  cases compiled with
  | next hcompiled htail =>
      rename_i stepPost
      have hat : Ninst.At frame.sevm.code cursor.pc Ninst.statcall :=
        ninstAt_of_subcode_next cursor.codeSlice
      obtain ⟨nextBoundary, nextSub⟩ :=
        Func.noPushBefore_next cursor.codeSlice cursor.codeBoundary
      rcases cursor.parentPrefix with ⟨before, hbefore⟩
      rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_next (frame := frame) cursor.current hbefore hat
          hcompiled with
        ⟨_xl, continuation, _selected, _occurrence, hedge, _hnextPrefix⟩
      rcases hedge.exists_counted with ⟨counted, hcountedEdge⟩
      have hlabel :
          AllowanceEntryReadSound (Devm.getStor cursor.pre ca) counted :=
        hcountedEdge.entryReadSound_of_statcall hat installed hdeeper
      have htailNil : Exec.attributionInner dp ca continuation = [] :=
        hfinish ⟨cursor.pc + Ninst.statcall.size, frame.sevm, stepPost,
            frame.out, continuation, frame.committed⟩
          ⟨cursor.pc + Ninst.statcall.size, stepPost, continuation,
            ⟨[], .refl _⟩, .refl _, htail, nextSub, nextBoundary⟩
      have hprefixSplit := cursor.countedPrefix.descendantCounted_eq
      change Exec.attributionInner dp ca frame.run =
        [] ++ Exec.attributionInner dp ca cursor.current at hprefixSplit
      have hedgeSplit := hcountedEdge.descendantCounted_eq
      change Exec.attributionInner dp ca cursor.current =
        counted ++ Exec.attributionInner dp ca continuation at hedgeSplit
      rw [hprefixSplit, List.nil_append, hedgeSplit, htailNil,
        List.append_nil]
      exact hlabel

/-! ## The counted entry with the code map attached

Local mirrors of `Exec.Frame.compiledMainCursorCounted`,
the dispatch traversal, and `Exec.Frame.compiledSelectorBodyCursorCounted`
that additionally expose the entry segment's code-map preservation. -/

/-- The counted selector-body entry with the entry segment's code map and
allowance region attached; the silent-frame projection of
`Exec.Frame.compiledSelectorBodyCursorCountedSilent`. -/
private theorem Exec.Frame.compiledSelectorBodyCursorFrame
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {body : Func}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) body frame.post,
      Devm.getCode frame.pre = Devm.getCode bodyCursor.pre ∧
      AllowanceAgree frame.sevm frame.pre bodyCursor.pre := by
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorCountedSilent (frame := frame) context hnonempty hmem
    with ⟨bodyCursor, hsilent⟩
  exact ⟨bodyCursor, getCode_map_eq_of_state_eq hsilent.state,
    AllowanceAgree.of_state_eq hsilent.state⟩

/-! ## From the selected permit body to the single spawn-capable step -/

/-- From the counted cursor at the selected `nonpayable (permit dp)` body,
reach the body's single `STATICCALL` with its six ECRECOVER operands, the
code map and the tagged allowance region carried along: every crossing
before it is childless scaffolding, the rejected deadline arm is a fixed
reverter, and the one storage write on the way — the tentative nonce
increment — lands in the nonce region.  Continuation-passing, because a
`CountedCursor` is data and cannot be existentially quantified in a
`Prop`. -/
private theorem Exec.Frame.reachPermitStatcall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {motive : Prop}
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp))
    (bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (nonpayable (permit dp)) frame.post)
    (k : ∀ (boundaryCursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux))
          (Ninst.statcall ::: permitAfterStaticcall) frame.post)
        (gasWord : B256) (stack : Stack),
        gasWord :: (1 : B256) :: (0 : B256) :: (128 : B256) ::
            (128 : B256) :: (32 : B256) :: stack <<+ boundaryCursor.pre.stack →
        Devm.getCode bodyCursor.pre = Devm.getCode boundaryCursor.pre →
        AllowanceAgree frame.sevm bodyCursor.pre boundaryCursor.pre →
        motive) :
    motive := by
  rcases bodyCursor.enterNonpayableFrame with
    ⟨permitCursor, hcodeWrap, hagreeWrap⟩
  change Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (permitDeadlineLine +++
      (.branch (permitAfterDeadline dp) (.call expiredPermitErrorSlot)))
    frame.post at permitCursor
  rcases permitCursor.peelChildlessLine (line := permitDeadlineLine)
      (by simp [permitDeadlineLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨deadlineBranchCursor, hdeadlineLine⟩
  have hcodeDeadline : Devm.getCode permitCursor.pre =
      Devm.getCode deadlineBranchCursor.pre :=
    Line.of_inv Devm.getCode (by
      unfold permitDeadlineLine arg cdl
      line_inv) hdeadlineLine
  have hagreeDeadline :
      AllowanceAgree frame.sevm permitCursor.pre deadlineBranchCursor.pre :=
    .of_stor_eq (Line.of_inv Devm.getStor (by
      unfold permitDeadlineLine arg cdl
      line_inv) hdeadlineLine)
  rcases deadlineBranchCursor.selectBranchSplitFrame with hlive | hexpired
  · rcases hlive with ⟨liveCursor, hcodeBranch, hagreeBranch⟩
    change Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (permitNoncePrepare +++
        (permitStructPrepare +++ permitDomainDispatch dp))
      frame.post at liveCursor
    rcases liveCursor.peelChildlessLine (line := permitNoncePrepare)
        (by simp [permitNoncePrepare, addressArg, normalizeAddress,
          pushAddressMask, tagNonceKey, mstoreAt, Blanc.arg, cdl,
          NinstIsChildless, Ninst.pushB256]) with
      ⟨structCursor, hnonceLine⟩
    have hcodeNonce : Devm.getCode liveCursor.pre =
        Devm.getCode structCursor.pre :=
      Line.of_inv Devm.getCode (by
        unfold permitNoncePrepare addressArg normalizeAddress
          pushAddressMask tagNonceKey mstoreAt Blanc.arg cdl
        line_inv) hnonceLine
    have hagreeNonce :
        AllowanceAgree frame.sevm liveCursor.pre structCursor.pre := by
      intro key hkey
      rw [(of_permitNoncePrepare_raw nil_pref hnonceLine).2.1,
        Stor.get_set_ne _
          (permitRuntimeNonceKey_ne_allowance frame.sevm hkey) _]
    rcases structCursor.peelChildlessLine (line := permitStructPrepare)
        (by simp [permitStructPrepare, argCopy, cdc, arg, cdl, mstoreAt,
          pushList, NinstIsChildless, Ninst.pushB256]) with
      ⟨domainCursor, hstructLine⟩
    have hcodeStruct : Devm.getCode structCursor.pre =
        Devm.getCode domainCursor.pre :=
      Line.of_inv Devm.getCode (by
        unfold permitStructPrepare argCopy cdc arg cdl mstoreAt pushList
        line_inv) hstructLine
    have hagreeStruct :
        AllowanceAgree frame.sevm structCursor.pre domainCursor.pre :=
      .of_stor_eq (Line.of_inv Devm.getStor (by
        unfold permitStructPrepare argCopy cdc arg cdl mstoreAt pushList
        line_inv) hstructLine)
    rcases domainCursor.castSourceFrame (permitDomainDispatch_shape dp) with
      ⟨domainCursor, hdomainPre⟩
    have hcodeStruct : Devm.getCode structCursor.pre =
        Devm.getCode domainCursor.pre :=
      hcodeStruct.trans (congrArg Devm.getCode hdomainPre.symm)
    have hagreeStruct :
        AllowanceAgree frame.sevm structCursor.pre domainCursor.pre := by
      simpa only [hdomainPre] using hagreeStruct
    rcases domainCursor.peelChildlessLine
        (line := permitDomainTestLine dp)
        (by simp [permitDomainTestLine, pushDeployWord,
          NinstIsChildless]) with
      ⟨domainBranchCursor, hdomainTestLine⟩
    have hcodeDomainTest : Devm.getCode domainCursor.pre =
        Devm.getCode domainBranchCursor.pre :=
      Line.of_inv Devm.getCode (by
        unfold permitDomainTestLine pushDeployWord
        line_inv) hdomainTestLine
    have hagreeDomainTest :
        AllowanceAgree frame.sevm domainCursor.pre domainBranchCursor.pre :=
      .of_stor_eq (Line.of_inv Devm.getStor (by
        unfold permitDomainTestLine pushDeployWord
        line_inv) hdomainTestLine)
    have hcodeToDomainBranch : Devm.getCode bodyCursor.pre =
        Devm.getCode domainBranchCursor.pre :=
      hcodeWrap.trans (hcodeDeadline.trans (hcodeBranch.trans
        (hcodeNonce.trans (hcodeStruct.trans hcodeDomainTest))))
    have hagreeToDomainBranch :
        AllowanceAgree frame.sevm bodyCursor.pre domainBranchCursor.pre :=
      hagreeWrap.trans (hagreeDeadline.trans (hagreeBranch.trans
        (hagreeNonce.trans (hagreeStruct.trans hagreeDomainTest))))
    have finish :
        ∀ callCursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
            ((weth10 dp).main :: weth10Aux)
            (table 0 ((weth10 dp).main :: weth10Aux))
            (.call permitRecoverSlot) frame.post,
          Devm.getCode bodyCursor.pre = Devm.getCode callCursor.pre →
          AllowanceAgree frame.sevm bodyCursor.pre callCursor.pre →
          motive := by
      intro callCursor hcodeToCall hagreeToCall
      rcases callCursor.enterCallFrame hcode with
        ⟨body, hget, recoverCursor, hcodeCall, hagreeCall⟩
      have hbody : body = permitRecover := by
        simpa [weth10, weth10Aux, permitRecoverSlot] using hget.symm
      subst body
      rcases recoverCursor.castSourceFrame
          permitRecover_afterStaticcall_shape with
        ⟨recoverCursor, hrecoverPre⟩
      have hcodeCall : Devm.getCode callCursor.pre =
          Devm.getCode recoverCursor.pre :=
        hcodeCall.trans (congrArg Devm.getCode hrecoverPre.symm)
      have hagreeCall :
          AllowanceAgree frame.sevm callCursor.pre recoverCursor.pre := by
        simpa only [hrecoverPre] using hagreeCall
      rcases recoverCursor.peelChildlessLine
          (line := permitDigest ++ permitRecoverPrepare)
          (by simp [permitDigest, permitRecoverPrepare,
            permitRecoverWrites, pushList, mstoreAt, arg, cdl,
            NinstIsChildless, Ninst.pushB256]) with
        ⟨callBoundaryCursor, hprefixLine⟩
      have hcodePrefix : Devm.getCode recoverCursor.pre =
          Devm.getCode callBoundaryCursor.pre :=
        Line.of_inv Devm.getCode (by
          unfold permitDigest permitRecoverPrepare permitRecoverWrites
            pushList mstoreAt arg cdl
          line_inv) hprefixLine
      have hagreePrefix :
          AllowanceAgree frame.sevm recoverCursor.pre
            callBoundaryCursor.pre :=
        .of_stor_eq (Line.of_inv Devm.getStor (by
          unfold permitDigest permitRecoverPrepare permitRecoverWrites
            pushList mstoreAt arg cdl
          line_inv) hprefixLine)
      rcases of_run_append permitDigest hprefixLine with
        ⟨preparePre, hdigest, hprepare⟩
      have hfirst : ∃ firstPost,
          Line.Run frame.sevm preparePre (mstoreAt 0) firstPost := by
        have hprepareCopy := hprepare
        unfold permitRecoverPrepare permitRecoverWrites at hprepareCopy
        rcases of_run_append (mstoreAt 0) hprepareCopy with
          ⟨firstPost, hfirstRun, _hrest⟩
        exact ⟨firstPost, hfirstRun⟩
      rcases hfirst with ⟨firstPost, hfirstRun⟩
      rcases mstoreAt_stack_head hfirstRun with
        ⟨word, tail, hword⟩
      rcases permitRecoverPrepare_stack hword hprepare with
        ⟨gasWord, hoperands⟩
      exact k callBoundaryCursor gasWord tail hoperands
        (hcodeToCall.trans (hcodeCall.trans hcodePrefix))
        (hagreeToCall.trans (hagreeCall.trans hagreePrefix))
    rcases domainBranchCursor.selectBranchSplitFrame with
      hcalculated | hcached
    · rcases hcalculated with ⟨calculatedCursor, hcodeArm, hagreeArm⟩
      rcases calculatedCursor.peelChildlessLine
          (line := permitCalculatedDomainPrefix)
          (by simp [permitCalculatedDomainPrefix,
            calculateDomainSeparator, pushList, mstoreAt,
            NinstIsChildless, Ninst.pushB256]) with
        ⟨callCursor, hcalculatedLine⟩
      have hcodeLine : Devm.getCode calculatedCursor.pre =
          Devm.getCode callCursor.pre :=
        Line.of_inv Devm.getCode (by
          unfold permitCalculatedDomainPrefix calculateDomainSeparator
            pushList mstoreAt
          line_inv) hcalculatedLine
      have hagreeLine :
          AllowanceAgree frame.sevm calculatedCursor.pre callCursor.pre :=
        .of_stor_eq (Line.of_inv Devm.getStor (by
          unfold permitCalculatedDomainPrefix calculateDomainSeparator
            pushList mstoreAt
          line_inv) hcalculatedLine)
      exact finish callCursor
        (hcodeToDomainBranch.trans (hcodeArm.trans hcodeLine))
        (hagreeToDomainBranch.trans (hagreeArm.trans hagreeLine))
    · rcases hcached with ⟨cachedCursor, hcodeArm, hagreeArm⟩
      rcases cachedCursor.peelChildlessLine
          (line := permitCachedDomainPrefix dp)
          (by simp [permitCachedDomainPrefix, pushDeployWord,
            NinstIsChildless]) with
        ⟨callCursor, hcachedLine⟩
      have hcodeLine : Devm.getCode cachedCursor.pre =
          Devm.getCode callCursor.pre :=
        Line.of_inv Devm.getCode (by
          unfold permitCachedDomainPrefix pushDeployWord
          line_inv) hcachedLine
      have hagreeLine :
          AllowanceAgree frame.sevm cachedCursor.pre callCursor.pre :=
        .of_stor_eq (Line.of_inv Devm.getStor (by
          unfold permitCachedDomainPrefix pushDeployWord
          line_inv) hcachedLine)
      exact finish callCursor
        (hcodeToDomainBranch.trans (hcodeArm.trans hcodeLine))
        (hagreeToDomainBranch.trans (hagreeArm.trans hagreeLine))
  · rcases hexpired with ⟨errorCursor, -, -⟩
    have hrun := Func.Run.of_runCompiled errorCursor.run
    cases hrun with
    | call hget _hburn hbody =>
        have hbody' := hbody
        rw [show ((weth10 dp).main :: weth10Aux)[expiredPermitErrorSlot]? =
            some expiredPermitError from by
          simp [weth10Aux, expiredPermitErrorSlot]] at hget
        cases Option.some.inj hget
        exact absurd hbody' Func.not_run_revWith

/-! ## The two readings of the reached crossing -/

/-- With the precompile enabled and undelegated the crossing carries no
counted records at all, so the frame's proper-descendant counted stream is
empty. -/
private theorem Exec.Frame.attributionInner_eq_nil_of_permitBodyCursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp))
    (bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (nonpayable (permit dp)) frame.post)
    (hprecomp : decide
      (frame.sevm.benvStat.rules.isPrecomp (1 : B256).toAdr) = true)
    (hnodeleg : getDelegatedCodeAddress
      (Devm.getCode bodyCursor.pre (1 : B256).toAdr) = none) :
    Exec.attributionInner dp ca frame.run = [] := by
  refine Blanc.Weth10.Exec.Frame.reachPermitStatcall (frame := frame) hcode bodyCursor ?_
  intro boundaryCursor _gasWord _stack hoperands hcodeBoundary _hagree
  have hnodelegBoundary : getDelegatedCodeAddress
      (Devm.getCode boundaryCursor.pre (1 : B256).toAdr) = none := by
    rw [← congrFun hcodeBoundary (1 : B256).toAdr]
    exact hnodeleg
  rcases boundaryCursor.crossPermitStaticcall hprecomp hnodelegBoundary
      hoperands with
    ⟨suffixCursor⟩
  exact suffixCursor.finishPermitAfterStaticcall

/-- Without any routing premise the crossing may retain an interpreted static
child, but every counted record it contributes is non-writing, so the frame's
proper-descendant counted stream is write-free. -/
private theorem Exec.Frame.attributionInner_writeFree_of_permitBodyCursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp))
    (bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (nonpayable (permit dp)) frame.post) :
    WriteFreeLedger (Exec.attributionInner dp ca frame.run) := by
  refine Blanc.Weth10.Exec.Frame.reachPermitStatcall (frame := frame) hcode bodyCursor ?_
  intro boundaryCursor _gasWord _stack _hoperands _hcodeBoundary _hagree
  exact Blanc.Weth10.Exec.Frame.CountedCursor.attributionInner_writeFree_of_statcall boundaryCursor
    (fun _ suffixCursor => suffixCursor.finishPermitAfterStaticcall)

/-- Without any routing premise the crossing may retain an interpreted static
child, but every counted record it contributes read the word the frame's
*entry* storage held at that record's key: the recursion hypothesis carries
the subtree read-soundly against the boundary storage, and the only write
between frame entry and the boundary is the tentative nonce increment, whose
key is separated from every tagged allowance key. -/
private theorem
    Exec.Frame.attributionInner_entryReadSound_of_permitBodyCursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp))
    (bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor (frame := frame) dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (nonpayable (permit dp)) frame.post)
    (htarget : frame.sevm.currentTarget = ca)
    (hentryCode : Devm.getCode frame.pre = Devm.getCode bodyCursor.pre)
    (hentryAgree : AllowanceAgree frame.sevm frame.pre bodyCursor.pre)
    (installed :
      some (frame.pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun p s d out _ => Exec.CoreAllowanceReadSound dp ca p s d out)) :
    AllowanceEntryReadSound (Devm.getStor frame.pre ca)
      (Exec.attributionInner dp ca frame.run) := by
  refine Blanc.Weth10.Exec.Frame.reachPermitStatcall (frame := frame) hcode bodyCursor ?_
  intro boundaryCursor _gasWord _stack _hoperands hcodeBoundary hagree
  have hinstalled : some (boundaryCursor.pre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← congrFun (hentryCode.trans hcodeBoundary) ca]
    exact installed
  refine AllowanceEntryReadSound.congr (fun key hkey => ?_)
    (Blanc.Weth10.Exec.Frame.CountedCursor.attributionInner_entryReadSound_of_statcall boundaryCursor hinstalled
      hdeeper
      (fun _ suffixCursor => suffixCursor.finishPermitAfterStaticcall))
  have hfull := (hentryAgree.trans hagree) key hkey
  rwa [htarget] at hfull

/-! ## The `permit` arm -/

private theorem one_toAdr_local : (1 : B256).toAdr = (1 : Adr) := rfl

/-- A committed authentic `permit` frame with the ECRECOVER precompile
enabled and undelegated contributes no proper-descendant counted records;
the counted mirror of the chronology module's empty-slot outcome.

The two precompile-resolution hypotheses are load-bearing: without them
the model admits an EIP-7702 delegation designator on address `1`, whose
interpreted static child may retain counted view frames of its own. -/
theorem Exec.Frame.attributionInner_eq_nil_of_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "permit" [.address, .address, .uint256, .uint256,
        .uint 8, .bytes 32, .bytes 32])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hprecomp :
      decide (frame.sevm.benvStat.rules.isPrecomp 1) = true)
    (hnodeleg :
      getDelegatedCodeAddress (frame.pre.getCode 1) = none) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hmem : (Sevm.selector frame.sevm, nonpayable (permit dp)) ∈
      weth10Funcs dp := by
    rw [hselector]
    exact permit_mem_weth10Funcs dp
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorFrame (frame := frame) context hnonempty hmem with
    ⟨bodyCursor, hcodeEntry, -⟩
  refine Blanc.Weth10.Exec.Frame.attributionInner_eq_nil_of_permitBodyCursor (frame := frame)
    context.invocation.2.2.2 bodyCursor
    (by rw [one_toAdr_local]; exact hprecomp) ?_
  rw [one_toAdr_local, ← congrFun hcodeEntry (1 : Adr)]
  exact hnodeleg

/-- A committed authentic `permit` frame contributes only non-writing
proper-descendant counted records, with no hypothesis about how address `1`
resolves.  Its single spawn-capable instruction is a `STATICCALL`, so any
interpreted child it admits runs under `STATIC`, and no counted frame
retained under `STATIC` commits an allowance word. -/
theorem Exec.Frame.attributionInner_writeFree_of_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "permit" [.address, .address, .uint256, .uint256,
        .uint 8, .bytes 32, .bytes 32])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    WriteFreeLedger (Exec.attributionInner dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable (permit dp)) ∈
      weth10Funcs dp := by
    rw [hselector]
    exact permit_mem_weth10Funcs dp
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorFrame (frame := frame) context hnonempty hmem with
    ⟨bodyCursor, -, -⟩
  exact Blanc.Weth10.Exec.Frame.attributionInner_writeFree_of_permitBodyCursor (frame := frame)
    context.invocation.2.2.2 bodyCursor

/-- A committed authentic `permit` frame's proper-descendant counted records
all observed the frame's *entry* allowance word at their own key, with no
hypothesis about how address `1` resolves.  Together with write-freeness this
is everything the strengthened carrier asks of the descendant stream. -/
theorem Exec.Frame.attributionInner_entryReadSound_of_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "permit" [.address, .address, .uint256, .uint256,
        .uint 8, .bytes 32, .bytes 32])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    AllowanceEntryReadSound (Devm.getStor frame.pre ca)
      (Exec.attributionInner dp ca frame.run) := by
  have hmem : (Sevm.selector frame.sevm, nonpayable (permit dp)) ∈
      weth10Funcs dp := by
    rw [hselector]
    exact permit_mem_weth10Funcs dp
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorFrame (frame := frame) context hnonempty hmem with
    ⟨bodyCursor, hcodeEntry, hagreeEntry⟩
  exact Blanc.Weth10.Exec.Frame.attributionInner_entryReadSound_of_permitBodyCursor (frame := frame)
    context.invocation.2.2.2 bodyCursor context.invocation.2.1 hcodeEntry
    hagreeEntry context.installed.1 hdeeper

/-! ## Discharging the raw effect's crossing assumption

`permit_exec_raw_effect_region` leaves its `STATICCALL` crossing to the
caller.  The recursion hypothesis discharges it for every child at once: a
`STATICCALL` child is static, a static subtree's counted stream is
write-free, and replaying a write-free ledger is the identity on the entry
storage — so whatever the child does to its own accounts, `ca`'s allowance
region comes back unchanged. -/

/-- The read-sound recursion hypothesis downgrades to the landed one,
pointwise over the deeper executions it quantifies. -/
private theorem forallDeeperAt_allowanceSound_of_readSound
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    (h : ForallDeeperAt depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    ForallDeeperAt depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out) :=
  fun pc sevm devm exn ex hdeep hat =>
    (h pc sevm devm exn ex hdeep hat).coreAllowanceSound

private theorem permitStatcallRegionSilent_of_forallDeeperAt
    {dp : DeployParams} {ca : Adr} {e : Sevm} {pre : Devm}
    (htarget : e.currentTarget = ca)
    (installed : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm childPre out)) :
    PermitStatcallRegionSilent e (Devm.getCode pre) := by
  intro u v gasWord tail hcodeU hoperands hrun key hkey
  rw [htarget]
  have hcodeAt : some (u.getCode ca).toList = Prog.compile (weth10 dp) := by
    rw [show u.getCode ca = pre.getCode ca from congrFun hcodeU ca]
    exact installed
  rcases of_run_statcall_val_with_depth hoperands hrun with hfail | hsuccess
  · rw [← getStor_eq_of_state_eq hfail.2.1.1 ca]
  · rcases hsuccess with
      ⟨parent, child, xl, dpFlag, code, avail, hdepthPos, _hstack,
        hparentState, _hparentMemory, hdelegation, hfilled, hprocess,
        _herr, _hresume, hstateV, _hreturnData, _hmemory, _hstackV⟩
    obtain ⟨retained⟩ := exists_retainedXlot_of_filled hfilled
    have hfree : WriteFreeLedger (retained.attributionStream dp ca) := by
      cases retained with
      | none => exact writeFreeLedger_nil
      | some childRun =>
          refine Exec.attributionStream_writeFree_of_static childRun ?_
          have hstatic := Blanc.Frame.enter_run_isStatic (RunFrame.some_inv
            hprocess).1
          simpa only [Jaune.Frame.ofCall, callMsg, Bool.true_or] using hstatic
    have hchild := ProcessMessageTrace.allowanceRegionDelta_of_forallDeeperAt
      (dp := dp) (ca := ca) (depth := e.depth) (parent := u)
      ⟨xl, retained, hprocess⟩
      (by simpa only [callMsg] using hparentState.symm)
      (by dsimp only [callMsg]; omega)
      hcodeAt
      (by
        intro hct
        have htargetCa : (1 : B256).toAdr = ca := by
          simpa only [callMsg] using hct
        exact callbackCode_eq_compiled_of_target_eq hcodeAt htargetCa
          hdelegation)
      (by
        intro hct
        have htargetCa : (1 : B256).toAdr = ca := by
          simpa only [callMsg] using hct
        simp only [callMsg, htargetCa])
      hdeeper
    have hstor := hchild.storage key hkey
    rw [applyAllowanceLedger_writeFree _ key hfree] at hstor
    rw [getStor_eq_of_state_eq hstateV ca]
    exact hstor

/-! ## The frame's own trailing record -/

/-- The own record of a committed authentic `permit` frame: a `.permitStore`
of the raw third argument word at the projected raw owner/spender pair. -/
private theorem permit_own_allowance_event
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hselector : Sevm.selector frame.sevm = permitSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    (CountedFrame.ofFrame dp ca frame).allowance =
      some { owner := Sevm.argWord frame.sevm 0
             spender := Sevm.argWord frame.sevm 1
             caller := frame.sevm.caller
             depth := frame.sevm.depth
             visit := .permitStore (Sevm.argWord frame.sevm 2) } := by
  show frameAllowanceEvent frame.sevm frame.pre frame.post = _
  simp [frameAllowanceEvent, hnonempty, hselector,
    permitSelector_ne_approveSelector,
    permitSelector_ne_approveAndCallSelector]

/-- `permit`'s own record reads nothing: a `.permitStore` visit carries a
written word only.  This is exactly why the arm needs no flash-style
exemption even though `Exec.frameContribution` places its record after its
subtree — the entry-read clause is vacuous at that split. -/
private theorem permit_own_read_eq_none
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hselector : Sevm.selector frame.sevm = permitSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∀ event, (CountedFrame.ofFrame dp ca frame).allowance = some event →
      event.visit.read? = none := by
  intro event hevent
  rw [permit_own_allowance_event hselector hnonempty] at hevent
  have heq := Option.some.inj hevent
  subst heq
  rfl

/-- The `permit` attribution stream is its descendant stream followed by its
own record: `Exec.frameContribution` classifies `permit` alongside
`flashLoan` through `ownRecordLast`, because `permitRecover` performs the
recovery `STATICCALL` before the `approvePermit` store. -/
private theorem Exec.Frame.attributionStream_of_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = permitSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Exec.attributionStream dp ca frame.run =
      Exec.attributionInner dp ca frame.run ++
        [CountedFrame.ofFrame dp ca frame] := by
  have hpermit : isPermitInvocation frame.sevm = true := by
    simp [isPermitInvocation, hselector, hnonempty]
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  rw [Exec.attributionStream_eq_frameContribution dp ca frame.run
      frame.committed, hframe,
    Exec.frameContribution_eq_append_of_permit dp ca frame _
      context.invocation hpermit]

/-- The `permit` frame's own record transports the allowance region on its
own: the raw effect's only allowance-region write is the `approvePermit`
store at the projected owner/spender key, and the tentative nonce increment
lands in the nonce region, disjoint from every tagged allowance key.  No
calldata decoding hypothesis occurs — `permit_exec_raw_effect_region` names
the runtime keys the body actually computes, so short and dirty calldata are
covered on the same footing as a canonical ABI encoding. -/
private theorem Exec.Frame.allowanceRegionEffect_ownRecord_of_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = permitSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hsilent : PermitStatcallRegionSilent frame.sevm
      (Devm.getCode frame.pre)) :
    AllowanceRegionEffect ca frame.pre frame.post
      [CountedFrame.ofFrame dp ca frame] := by
  have hwfPre : Mem.Wf frame.pre.memory := context.memory_wf
  have hown := permit_own_allowance_event (dp := dp) (ca := ca)
    hselector hnonempty
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error _ => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst hpc
      have hcode := context.invocation.2.2.2
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hcodeEq : Devm.getCode pre ca = Devm.getCode post ca :=
        Exec.installedCodeEq run context.installed
      have hselE : Sevm.selector e = permitSelector := hselector
      have hne0 : e.data.length.toB256 ≠ 0 := hnonempty
      have hraw := permit_exec_raw_effect_region dp hsilent hwfPre run
        hcode hselE hne0
      dsimp only at hraw
      rcases hraw with ⟨_, hstor⟩
      refine ⟨fun key hkey => ?_, hcodeEq⟩
      show (Devm.getStor post ca).get key =
        applyAllowanceLedger (Devm.getStor pre ca)
          [CountedFrame.ofFrame dp ca ⟨0, e, pre, .ok post, run, committed⟩]
          key
      rw [applyAllowanceLedger_singleton, hown]
      simp only [AllowanceEvent.key, AllowanceVisit.written?]
      rw [← htarget]
      show (Devm.getStor post e.currentTarget).get key = _
      rw [hstor key hkey, show projectedAllowanceKey (Sevm.argWord e 0)
        (Sevm.argWord e 1) = permitRuntimeAllowanceKey e from rfl]
      by_cases hkeyCase : permitRuntimeAllowanceKey e = key
      · rw [if_pos hkeyCase, ← hkeyCase, Stor.get_set_self]
      · rw [if_neg hkeyCase, Stor.get_set_ne _ hkeyCase _,
          Stor.get_set_ne _ (permitRuntimeNonceKey_ne_allowance e hkey) _]

/-! ## The two `permit` arms -/

/-- `permit` transports the allowance region: its own record stores the raw
third argument word at the projected owner/spender key, which is exactly the
runtime key the compiled body writes, and every counted record its
`STATICCALL` child can contribute is non-writing, so the record replays
behind a transparent prefix.  The tentative nonce increment writes a
nonce-region key, disjoint from every tagged allowance key.

The record trails its subtree rather than leading it because `permitRecover`
performs the recovery `STATICCALL` before the `approvePermit` store, so the
ledger order matches the runtime order: `Exec.frameContribution` classifies
`permit` alongside `flashLoan` through `ownRecordLast`.  Both placements
transport the same storage here — the child stream is write-free — but only
this one is chronological, and chronology is what the attribution roots read.

No calldata decoding hypothesis occurs: `permit_exec_raw_effect_region` names
the runtime keys the body actually computes, so short and dirty calldata are
covered on the same footing as a canonical ABI encoding.  No premise about
how address `1` resolves occurs either: the recursion hypothesis discharges
the `STATICCALL` crossing, exactly as it does for the sibling callback
arms. -/
theorem Exec.Frame.allowanceRegionEffect_of_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "permit" [.address, .address, .uint256, .uint256,
        .uint 8, .bytes 32, .bytes 32])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceSound dp ca pc sevm pre out)) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  rw [Blanc.Weth10.Exec.Frame.attributionStream_of_permit (frame := frame) context hselector hnonempty]
  exact AllowanceRegionEffect.snoc_writeFree
    (Blanc.Weth10.Exec.Frame.allowanceRegionEffect_ownRecord_of_permit (frame := frame) context hselector
      hnonempty
      (permitStatcallRegionSilent_of_forallDeeperAt context.invocation.2.1
        context.installed.1 hdeeper))
    (Blanc.Weth10.Exec.Frame.attributionInner_writeFree_of_permit (frame := frame) context hselector hnonempty)

/-- The strengthened carrier's `permit` arm.  The storage side is the arm
above; the new entry-read clause splits exactly two ways along the
chronological ledger `inner ++ [own]`.

* At the trailing own record the prefix is the whole descendant stream, and
  the clause is *vacuous*: a `.permitStore` visit records no read.  This is
  what makes a flash-style exemption unnecessary here, and it is a
  consequence of the corrected `Exec.frameContribution` placement, not an
  accident — under the old `own :: inner` order the clause would have
  demanded permit's stored word where an interpreted child inside the
  recovery subtree had read the pre-store word.
* At a record inside the recovery subtree the prefix is a prefix of a
  write-free ledger, so the replay collapses to the entry storage, and the
  obligation is that the record observed `ca`'s frame-entry allowance word.
  The recursion hypothesis supplies exactly that at the `STATICCALL`
  boundary, and between frame entry and that boundary the body touches only
  the nonce-region key.

No premise about how address `1` resolves occurs, exactly as in the arm
above; the hypotheses are those of the sibling callback arms with
`Exec.CoreAllowanceSound` strengthened to its read-sound sibling. -/
theorem Exec.Frame.allowanceRegionEffectSound_of_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "permit" [.address, .address, .uint256, .uint256,
        .uint 8, .bytes 32, .bytes 32])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreAllowanceReadSound dp ca pc sevm pre out)) :
    AllowanceRegionEffectSound ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  rw [Blanc.Weth10.Exec.Frame.attributionStream_of_permit (frame := frame) context hselector hnonempty]
  exact AllowanceRegionEffectSound.snoc_writeFree
    (Blanc.Weth10.Exec.Frame.allowanceRegionEffect_ownRecord_of_permit (frame := frame) context hselector
      hnonempty
      (permitStatcallRegionSilent_of_forallDeeperAt context.invocation.2.1
        context.installed.1
        (forallDeeperAt_allowanceSound_of_readSound hdeeper)))
    (Blanc.Weth10.Exec.Frame.attributionInner_writeFree_of_permit (frame := frame) context hselector hnonempty)
    (Blanc.Weth10.Exec.Frame.attributionInner_entryReadSound_of_permit (frame := frame) context hselector
      hnonempty hdeeper)
    (permit_own_read_eq_none hselector hnonempty)

end Weth10

end Blanc
