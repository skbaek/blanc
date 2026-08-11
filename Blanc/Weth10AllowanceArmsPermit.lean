import Blanc.Weth10AllowanceArmsBalance

/-!
The ERC-2612 `permit` arm of the allowance-region transport.

A committed `permit` frame checks the deadline, reads and tentatively
increments the tagged nonce, hashes the typed struct, dispatches on the
cached domain separator, and tail-calls `permitRecover`, whose single
`STATICCALL` to precompile address `1` is the only spawn-capable
instruction on the path; the surviving signer-guard branches end in the
`approvePermit` store at the key hashed from the raw owner/spender words.

The counted walk below mirrors that path on the `CountedCursor` altitude.
Under the two precompile-resolution hypotheses — address `1` enabled in
the static fork rules and no EIP-7702 delegation designator installed on
it — the `STATICCALL` resolves synchronously, the crossing contributes no
counted records, and the frame's attribution stream is its own record
alone.  Without those hypotheses a delegated interpreted child is live in
the model and can retain counted frames of its own; that arm is out of
scope here and reported to the goal owner.

The branch and internal-call crossings additionally expose the code map,
so the no-delegation hypothesis stated at frame entry transports to the
exact call boundary.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## Local copies of the compiled body lines

`Weth10HolderFlowPermitChronology` keeps its permit line decompositions
private, so this module re-declares the ones it needs, byte for byte. -/

private theorem prepend_append_local
    (left right : Line) (tail : Func) :
    (left ++ right) +++ tail = left +++ (right +++ tail) := by
  induction left with
  | nil => rfl
  | cons head left ih => simp [prepend, ih]

private def permitDeadlineLine : Line := arg 3 ++ [Ninst.timestamp, Ninst.gt]

private def permitFirstSignerGuardLine : Line :=
  [Ninst.pop, Ninst.pushB256 128, Ninst.mload, Ninst.dup 0, Ninst.iszero]

private def permitSecondSignerGuardLine : Line :=
  arg 0 ++ [Ninst.eq, Ninst.iszero]

private def approvePermitLine : Line :=
  argCopy 0 0 2 ++ allowanceKeyFromMemory ++
  Blanc.arg 2 ++ [Ninst.swap 0, Ninst.sstore] ++
  Blanc.arg 2 ++ mstoreAt 0 ++ Blanc.arg 1 ++ Blanc.arg 0 ++
  [Ninst.pushB256 Blanc.approvalEvent] ++ logWith 2 0 1

private theorem approvePermit_shape :
    approvePermit = approvePermitLine +++ Func.stop := by
  simp only [approvePermit, approvePermitLine, prepend_append_local,
    List.append_assoc, prepend]

private def permitAfterStaticcall : Func :=
  permitFirstSignerGuardLine +++
    (.branch
      (permitSecondSignerGuardLine +++
        (.branch approvePermit (.call invalidPermitErrorSlot)))
      (.call invalidPermitErrorSlot))

private theorem permitRecover_afterStaticcall_shape :
    permitRecover =
      (permitDigest ++ permitRecoverPrepare) +++
        (Ninst.statcall ::: permitAfterStaticcall) := by
  rw [permitRecover_eq, recoverPermitSigner_eq_prepare]
  unfold permitSignerGuards permitAfterStaticcall
    permitFirstSignerGuardLine permitSecondSignerGuardLine
  rfl

private def permitDomainTestLine (dp : DeployParams) : Line :=
  [Ninst.dup 1, pushDeployWord dp.deploymentChainId, Ninst.eq]

private def permitCalculatedDomainPrefix : Line :=
  [Ninst.swap 0] ++ calculateDomainSeparator

private def permitCachedDomainPrefix (dp : DeployParams) : Line :=
  [Ninst.swap 0, Ninst.pop, pushDeployWord dp.cachedDomainSeparator]

private theorem permitDomainDispatch_shape (dp : DeployParams) :
    permitDomainDispatch dp =
      permitDomainTestLine dp +++
        (.branch
          (permitCalculatedDomainPrefix +++ .call permitRecoverSlot)
          (permitCachedDomainPrefix dp +++ .call permitRecoverSlot)) := by
  rfl

/-! ## Counted crossings that expose the code map

The counted cursor API of `Weth10AttributionChronology` exposes no state
facts across generated branch and internal-call scaffolding, so this
module rebuilds the two crossings it needs with the code map attached;
the no-delegation hypothesis stated at frame entry rides these equalities
to the exact `STATICCALL` boundary. -/

private theorem getCode_map_eq_of_state_eq {pre post : Devm}
    (h : pre.state = post.state) :
    Devm.getCode pre = Devm.getCode post :=
  funext (getCode_eq_of_state_eq h)

/-- Select whichever branch arm the committed run actually took, exposing
the crossing's code-map equality; the code-map projection of
`Exec.Frame.CountedCursor.selectBranchSplitSilent`. -/
private theorem Exec.Frame.CountedCursor.selectBranchSplitCode
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : frame.CountedCursor dp ca fs table
      (.branch left right) final) :
    (∃ arm : frame.CountedCursor dp ca fs table left final,
      Devm.getCode cursor.pre = Devm.getCode arm.pre) ∨
    (∃ arm : frame.CountedCursor dp ca fs table right final,
      Devm.getCode cursor.pre = Devm.getCode arm.pre) := by
  rcases cursor.selectBranchSplitSilent with ⟨arm, hsilent⟩ | ⟨arm, hsilent⟩
  · exact Or.inl ⟨arm, getCode_map_eq_of_state_eq hsilent.state⟩
  · exact Or.inr ⟨arm, getCode_map_eq_of_state_eq hsilent.state⟩

/-- Follow one generated internal source call, exposing the crossing's
code-map equality; the code-map projection of
`Exec.Frame.CountedCursor.enterCallSilent`. -/
private theorem Exec.Frame.CountedCursor.enterCallCode
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    (cursor : frame.CountedCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      ∃ bodyCursor : frame.CountedCursor dp ca (f₀ :: aux)
        (table 0 (f₀ :: aux)) body final,
        Devm.getCode cursor.pre = Devm.getCode bodyCursor.pre := by
  rcases cursor.enterCallSilent hcode with
    ⟨body, hget, bodyCursor, hsilent⟩
  exact ⟨body, hget, bodyCursor, getCode_map_eq_of_state_eq hsilent.state⟩

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
    (cursor : frame.CountedCursor dp ca fs table
      (.next Ninst.statcall tail) final)
    (hprecomp : decide
      (frame.sevm.benvStat.rules.isPrecomp (1 : B256).toAdr) = true)
    (hnodeleg : getDelegatedCodeAddress
      (Devm.getCode cursor.pre (1 : B256).toAdr) = none)
    {gasWord : B256} {stack : Stack}
    (operands : gasWord :: (1 : B256) :: (0 : B256) :: (128 : B256) ::
      (128 : B256) :: (32 : B256) :: stack <<+ cursor.pre.stack) :
    Nonempty (frame.CountedCursor dp ca fs table tail final) := by
  have compiled := cursor.run
  cases compiled with
  | next hcompiled htail =>
      have hat : Ninst.At frame.sevm.code cursor.pc Ninst.statcall :=
        ninstAt_of_subcode_next cursor.codeSlice
      rcases cursor.parentPrefix with ⟨before, hbefore⟩
      rcases frame.advance_runCompiled_next cursor.current hbefore hat
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
body, exposing the crossing's code-map equality; the code-map projection of
`Exec.Frame.CountedCursor.enterNonpayableSilent`. -/
private theorem Exec.Frame.CountedCursor.enterNonpayableCode
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {final : Devm}
    (cursor : frame.CountedCursor dp ca fs table
      (nonpayable body) final) :
    ∃ bodyCursor : frame.CountedCursor dp ca fs table body final,
      Devm.getCode cursor.pre = Devm.getCode bodyCursor.pre := by
  rcases cursor.enterNonpayableSilent with ⟨bodyCursor, hsilent⟩
  exact ⟨bodyCursor, getCode_map_eq_of_state_eq hsilent.state⟩

/-! ## The exact operand image at the call boundary -/

private theorem exists_head_of_run_mstoreAt_local
    {e : Sevm} {pre post : Devm} {k : B256}
    (run : Line.Run e pre (mstoreAt k) post) :
    ∃ word tail, word :: tail <<+ pre.stack := by
  unfold mstoreAt at run
  rcases Line.of_run_cons run with ⟨afterPush, hpush, run⟩
  rcases Line.of_run_cons run with ⟨afterStore, hstore, hnil⟩
  cases hnil
  have pushed := of_run_pushB256 hpush
  rcases of_run_mstore hstore with ⟨offset, word, hpop⟩
  have hstack : (k * 32) :: pre.stack =
      offset :: word :: post.stack :=
    pushed.stack.symm.trans hpop
  injection hstack with hoff htail
  refine ⟨word, post.stack, ?_⟩
  rw [htail]
  simpa using (pref_append (word :: post.stack) [])

/-- The arbitrary word consumed into scratch word zero is enough to derive
the six exact ECRECOVER operands at the following `STATICCALL`; the local
copy of the chronology module's private stack fact. -/
private theorem permitRecoverPrepare_stack_local
    {sevm : Sevm} {pre post : Devm} {word : B256} {tail : Stack}
    (hp : word :: tail <<+ pre.stack)
    (run : Line.Run sevm pre permitRecoverPrepare post) :
    ∃ gasWord : B256,
      gasWord :: (1 : B256) :: (0 : B256) :: (128 : B256) ::
        (128 : B256) :: (32 : B256) :: tail <<+ post.stack := by
  unfold permitRecoverPrepare permitRecoverWrites at run
  rcases of_run_append (mstoreAt 0) run with ⟨s1, h1, run⟩
  rcases of_run_mstoreAt_val h1 hp with ⟨hp1, hm1⟩
  rcases of_run_append (arg 4) run with ⟨s2, h2, run⟩
  have hp2 : Sevm.argWord sevm 4 :: tail <<+ s2.stack :=
    prefix_of_arg hp1 h2
  rcases of_run_append (mstoreAt 1) run with ⟨s3, h3, run⟩
  rcases of_run_mstoreAt_val h3 hp2 with ⟨hp3, hm3⟩
  rcases of_run_append (arg 5) run with ⟨s4, h4, run⟩
  have hp4 : Sevm.argWord sevm 5 :: tail <<+ s4.stack :=
    prefix_of_arg hp3 h4
  rcases of_run_append (mstoreAt 2) run with ⟨s5, h5, run⟩
  rcases of_run_mstoreAt_val h5 hp4 with ⟨hp5, hm5⟩
  rcases of_run_append (arg 6) run with ⟨s6, h6, run⟩
  have hp6 : Sevm.argWord sevm 6 :: tail <<+ s6.stack :=
    prefix_of_arg hp5 h6
  rcases of_run_append (mstoreAt 3) run with ⟨s7, h7, run⟩
  rcases of_run_mstoreAt_val h7 hp6 with ⟨hp7, hm7⟩
  rcases of_run_append [Ninst.pushB256 0] run with ⟨s8, h8, run⟩
  rcases Line.of_run_cons h8 with ⟨u8, q8, hnil⟩
  cases hnil
  have hp8 : (0 : B256) :: tail <<+ s8.stack :=
    prefix_of_push (of_run_pushB256 q8) hp7
  rcases of_run_append (mstoreAt 4) run with ⟨s9, h9, run⟩
  rcases of_run_mstoreAt_val h9 hp8 with ⟨hp9, hm9⟩
  rcases of_run_append (pushList [32, 128, 128, 0, 1]) run with
    ⟨s10, hpushes, hgas⟩
  simp only [pushList, List.map] at hpushes
  rcases Line.of_run_cons hpushes with ⟨u1, q1, hpushes⟩
  have hp10a : (32 : B256) :: tail <<+ u1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp9
  rcases Line.of_run_cons hpushes with ⟨u2, q2, hpushes⟩
  have hp10b : (128 : B256) :: (32 : B256) :: tail <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp10a
  rcases Line.of_run_cons hpushes with ⟨u3, q3, hpushes⟩
  have hp10c : (128 : B256) :: (128 : B256) :: (32 : B256) ::
      tail <<+ u3.stack :=
    prefix_of_push (of_run_pushB256 q3) hp10b
  rcases Line.of_run_cons hpushes with ⟨u4, q4, hpushes⟩
  have hp10d : (0 : B256) :: (128 : B256) :: (128 : B256) ::
      (32 : B256) :: tail <<+ u4.stack :=
    prefix_of_push (of_run_pushB256 q4) hp10c
  rcases Line.of_run_cons hpushes with ⟨u5, q5, hnil⟩
  cases hnil
  have hp10 : (1 : B256) :: (0 : B256) :: (128 : B256) ::
      (128 : B256) :: (32 : B256) :: tail <<+ s10.stack :=
    prefix_of_push (of_run_pushB256 q5) hp10d
  rcases Line.of_run_cons hgas with ⟨s11, q11, hnil⟩
  cases hnil
  rcases of_run_gas q11 with ⟨gasWord, hpush⟩
  exact ⟨gasWord, prefix_of_push hpush hp10⟩

/-! ## The parent-only suffix after the static child -/

/-- Complete the signer/approval suffix after the `STATICCALL`: the two
rejected arms are fixed reverters, so the retained path ends in the
childless `approvePermit` store and the frame's proper-descendant counted
stream is empty. -/
private theorem Exec.Frame.CountedCursor.finishPermitAfterStaticcall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (cursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      permitAfterStaticcall frame.post) :
    Exec.attributionInner dp ca frame.run = [] := by
  unfold permitAfterStaticcall at cursor
  rcases cursor.peelChildlessLine (line := permitFirstSignerGuardLine)
      (by simp [permitFirstSignerGuardLine, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨firstBranchCursor, -⟩
  rcases firstBranchCursor.selectBranchSplitCode with hsecond | herror
  · rcases hsecond with ⟨secondGuardCursor, -⟩
    rcases secondGuardCursor.peelChildlessLine
        (line := permitSecondSignerGuardLine)
        (by simp [permitSecondSignerGuardLine, arg, cdl,
          NinstIsChildless, Ninst.pushB256]) with
      ⟨secondBranchCursor, -⟩
    rcases secondBranchCursor.selectBranchSplitCode with happrove | herror
    · rcases happrove with ⟨approveCursor, -⟩
      have approveCursor' : frame.CountedCursor dp ca
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
    · rcases herror with ⟨errorCursor, -⟩
      have hrun := Func.Run.of_runCompiled errorCursor.run
      cases hrun with
      | call hget _hburn hbody =>
          have hbody' := hbody
          rw [show ((weth10 dp).main :: weth10Aux)[invalidPermitErrorSlot]? =
              some invalidPermitError from by
            simp [weth10Aux, invalidPermitErrorSlot]] at hget
          cases Option.some.inj hget
          exact absurd hbody' Func.not_run_revWith
  · rcases herror with ⟨errorCursor, -⟩
    have hrun := Func.Run.of_runCompiled errorCursor.run
    cases hrun with
    | call hget _hburn hbody =>
        have hbody' := hbody
        rw [show ((weth10 dp).main :: weth10Aux)[invalidPermitErrorSlot]? =
            some invalidPermitError from by
          simp [weth10Aux, invalidPermitErrorSlot]] at hget
        cases Option.some.inj hget
        exact absurd hbody' Func.not_run_revWith

/-! ## The counted entry with the code map attached

Local mirrors of `Exec.Frame.compiledMainCursorCounted`,
the dispatch traversal, and `Exec.Frame.compiledSelectorBodyCursorCounted`
that additionally expose the entry segment's code-map preservation. -/

/-- The counted selector-body entry with the entry segment's code-map
preservation attached; the code-map projection of
`Exec.Frame.compiledSelectorBodyCursorCountedSilent`. -/
private theorem Exec.Frame.compiledSelectorBodyCursorCode
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {body : Func}
    (context : frame.AuthenticContext dp ca)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp) :
    ∃ bodyCursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) body frame.post,
      Devm.getCode frame.pre = Devm.getCode bodyCursor.pre := by
  rcases frame.compiledSelectorBodyCursorCountedSilent context hnonempty hmem
    with ⟨bodyCursor, hsilent⟩
  exact ⟨bodyCursor, getCode_map_eq_of_state_eq hsilent.state⟩

/-! ## From the selected permit body to the empty counted stream -/

/-- From the counted cursor at the selected `nonpayable (permit dp)` body,
the frame's proper-descendant counted stream is empty: every crossing on
the retained path is childless scaffolding except the single enabled
undelegated `STATICCALL`, whose label is empty, and the rejected arms are
fixed reverters. -/
private theorem Exec.Frame.attributionInner_eq_nil_of_permitBodyCursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp))
    (bodyCursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (nonpayable (permit dp)) frame.post)
    (hprecomp : decide
      (frame.sevm.benvStat.rules.isPrecomp (1 : B256).toAdr) = true)
    (hnodeleg : getDelegatedCodeAddress
      (Devm.getCode bodyCursor.pre (1 : B256).toAdr) = none) :
    Exec.attributionInner dp ca frame.run = [] := by
  rcases bodyCursor.enterNonpayableCode with ⟨permitCursor, hcodeWrap⟩
  change frame.CountedCursor dp ca
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
  rcases deadlineBranchCursor.selectBranchSplitCode with hlive | hexpired
  · rcases hlive with ⟨liveCursor, hcodeBranch⟩
    change frame.CountedCursor dp ca
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
    rcases structCursor.peelChildlessLine (line := permitStructPrepare)
        (by simp [permitStructPrepare, argCopy, cdc, arg, cdl, mstoreAt,
          pushList, NinstIsChildless, Ninst.pushB256]) with
      ⟨domainCursor, hstructLine⟩
    have hcodeStruct : Devm.getCode structCursor.pre =
        Devm.getCode domainCursor.pre :=
      Line.of_inv Devm.getCode (by
        unfold permitStructPrepare argCopy cdc arg cdl mstoreAt pushList
        line_inv) hstructLine
    change frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (permitDomainTestLine dp +++
        (.branch
          (permitCalculatedDomainPrefix +++ .call permitRecoverSlot)
          (permitCachedDomainPrefix dp +++ .call permitRecoverSlot)))
      frame.post at domainCursor
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
    have hcodeToDomainBranch : Devm.getCode bodyCursor.pre =
        Devm.getCode domainBranchCursor.pre :=
      hcodeWrap.trans (hcodeDeadline.trans (hcodeBranch.trans
        (hcodeNonce.trans (hcodeStruct.trans hcodeDomainTest))))
    have finish :
        ∀ callCursor : frame.CountedCursor dp ca
            ((weth10 dp).main :: weth10Aux)
            (table 0 ((weth10 dp).main :: weth10Aux))
            (.call permitRecoverSlot) frame.post,
          Devm.getCode bodyCursor.pre = Devm.getCode callCursor.pre →
          Exec.attributionInner dp ca frame.run = [] := by
      intro callCursor hcodeToCall
      rcases callCursor.enterCallCode hcode with
        ⟨body, hget, recoverCursor, hcodeCall⟩
      have hbody : body = permitRecover := by
        simpa [weth10, weth10Aux, permitRecoverSlot] using hget.symm
      subst body
      change frame.CountedCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        ((permitDigest ++ permitRecoverPrepare) +++
          (Ninst.statcall ::: permitAfterStaticcall)) frame.post
        at recoverCursor
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
      rcases exists_head_of_run_mstoreAt_local hfirstRun with
        ⟨word, tail, hword⟩
      rcases permitRecoverPrepare_stack_local hword hprepare with
        ⟨gasWord, hoperands⟩
      have hnodelegBoundary : getDelegatedCodeAddress
          (Devm.getCode callBoundaryCursor.pre (1 : B256).toAdr) = none := by
        rw [← congrFun (hcodeToCall.trans
          (hcodeCall.trans hcodePrefix)) (1 : B256).toAdr]
        exact hnodeleg
      rcases callBoundaryCursor.crossPermitStaticcall hprecomp
          hnodelegBoundary hoperands with
        ⟨suffixCursor⟩
      exact suffixCursor.finishPermitAfterStaticcall
    rcases domainBranchCursor.selectBranchSplitCode with
      hcalculated | hcached
    · rcases hcalculated with ⟨calculatedCursor, hcodeArm⟩
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
      exact finish callCursor
        (hcodeToDomainBranch.trans (hcodeArm.trans hcodeLine))
    · rcases hcached with ⟨cachedCursor, hcodeArm⟩
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
      exact finish callCursor
        (hcodeToDomainBranch.trans (hcodeArm.trans hcodeLine))
  · rcases hexpired with ⟨errorCursor, -⟩
    have hrun := Func.Run.of_runCompiled errorCursor.run
    cases hrun with
    | call hget _hburn hbody =>
        have hbody' := hbody
        rw [show ((weth10 dp).main :: weth10Aux)[expiredPermitErrorSlot]? =
            some expiredPermitError from by
          simp [weth10Aux, expiredPermitErrorSlot]] at hget
        cases Option.some.inj hget
        exact absurd hbody' Func.not_run_revWith

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
    (context : frame.AuthenticContext dp ca)
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
  rcases frame.compiledSelectorBodyCursorCode context hnonempty hmem with
    ⟨bodyCursor, hcodeEntry⟩
  refine frame.attributionInner_eq_nil_of_permitBodyCursor
    context.invocation.2.2.2 bodyCursor
    (by rw [one_toAdr_local]; exact hprecomp) ?_
  rw [one_toAdr_local, ← congrFun hcodeEntry (1 : Adr)]
  exact hnodeleg

/-- `permit` transports the allowance region on canonical calldata: the
attribution stream is the frame's own record alone, and its event stores
the raw third argument word at the projected owner/spender key, which the
canonical decode identifies with the tagged `allowanceKey`.  The tentative
nonce increment writes a nonce-region key, disjoint from every tagged
allowance key. -/
theorem Exec.Frame.allowanceRegionEffect_of_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {owner spender : Adr} {value deadline : B256}
    {v : UInt8} {sigR sigS : B256}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm =
      selector "permit" [.address, .address, .uint256, .uint256,
        .uint 8, .bytes 32, .bytes 32])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hprecomp :
      decide (frame.sevm.benvStat.rules.isPrecomp 1) = true)
    (hnodeleg :
      getDelegatedCodeAddress (frame.pre.getCode 1) = none)
    (hdec : DecodesPermit frame.sevm owner spender value deadline
      v sigR sigS) :
    AllowanceRegionEffect ca frame.pre frame.post
      (Exec.attributionStream dp ca frame.run) := by
  have hinner : Exec.attributionInner dp ca frame.run = [] :=
    frame.attributionInner_eq_nil_of_permit context hselector hnonempty
      hprecomp hnodeleg
  have hneFlash : permitSelector ≠ flashLoanSelector := by decide +kernel
  have hsel : Sevm.selector frame.sevm = permitSelector := hselector
  have hnotflash : isFlashInvocation frame.sevm = false := by
    simp [isFlashInvocation, hsel, hneFlash]
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
      rcases exec_enters_weth10Nonpayable_logs run hcode hselE hne0
          (permit_mem_weth10Funcs dp) with
        ⟨mid, _hvalue, hstorEntry, _hbalEntry, hcodeEntry, hmemoryEntry,
          _hlogsEntry, _houtputEntry, hbody⟩
      have hnodelegMid : getDelegatedCodeAddress (mid.getCode 1) = none := by
        rw [congrFun hcodeEntry 1]
        exact hnodeleg
      have hwfMid : Mem.Wf mid.memory := by
        rw [hmemoryEntry]
        exact context.memory_wf
      have hrMid : Mem.Reads mid.memory [] := by
        rw [hmemoryEntry]
        exact context.memory_reads_empty
      have hsuccess := permit_selected_success_effect dp hprecomp
        hnodelegMid hdec nil_pref hwfMid hrMid hbody
      dsimp only at hsuccess
      rcases hsuccess with ⟨_, _, hstorMid, _, _⟩
      have hneApprove : permitSelector ≠ approveSelector := by
        decide +kernel
      have hneApproveCall : permitSelector ≠ approveAndCallSelector := by
        decide +kernel
      have hown : (CountedFrame.ofFrame dp ca
          (⟨0, e, pre, .ok post, run, committed⟩ : Exec.Frame)).allowance =
          some { owner := Sevm.argWord e 0
                 spender := Sevm.argWord e 1
                 caller := e.caller
                 depth := e.depth
                 visit := .permitStore (Sevm.argWord e 2) } := by
        show frameAllowanceEvent e pre post =
          some { owner := Sevm.argWord e 0
                 spender := Sevm.argWord e 1
                 caller := e.caller
                 depth := e.depth
                 visit := .permitStore (Sevm.argWord e 2) }
        simp [frameAllowanceEvent, hne0, hselE, hneApprove, hneApproveCall]
      have hargs := argWords_of_decodesPermit hdec
      have hkeyEq : projectedAllowanceKey (Sevm.argWord e 0)
          (Sevm.argWord e 1) = allowanceKey owner spender := by
        rw [hargs.1, hargs.2.1]
        exact permitAllowanceRuntimeKey_eq owner spender
      have hnonceNe : ∀ key, InRegion .allowance key →
          nonceKey owner ≠ key := by
        intro key hkey h
        exact regions_disjoint (x := .nonce) (y := .allowance) (by decide)
          key (h ▸ nonceKey_region owner) hkey
      refine ⟨fun key hkey => ?_, hcodeEq⟩
      show (Devm.getStor post ca).get key =
        applyAllowanceLedger (Devm.getStor pre ca)
          [CountedFrame.ofFrame dp ca ⟨0, e, pre, .ok post, run, committed⟩]
          key
      rw [applyAllowanceLedger_singleton, hown]
      simp only [AllowanceEvent.key, AllowanceVisit.written?]
      rw [← htarget]
      show (Devm.getStor post e.currentTarget).get key = _
      rw [hstorMid, hkeyEq]
      by_cases hkeyCase : allowanceKey owner spender = key
      · rw [if_pos hkeyCase, ← hkeyCase, Stor.get_set_self,
          hargs.2.2.1]
      · rw [if_neg hkeyCase, Stor.get_set_ne _ hkeyCase _,
          Stor.get_set_ne _ (hnonceNe key hkey) _,
          congrFun hstorEntry e.currentTarget]

end Weth10

end Blanc
