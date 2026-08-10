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
the crossing's code-map equality; the counted mirror of
`Exec.Frame.CompiledCursor.selectBranch`. -/
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
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero hroom hpop hleft =>
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases frame.advance_cont_counted cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases frame.advance_cont_counted afterPush hpPush hcPush
          hstepJumpi with
        ⟨armExec, hpArm, hcArm⟩
      exact Or.inl ⟨⟨cursor.pc + 4, _, armExec, hpArm, hcArm, hleft,
        hsubLeft, hboundLeft⟩, getCode_map_eq_of_state_eq hpop.state⟩
  | succ hne hroom hpop hright =>
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases frame.advance_cont_counted cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases frame.advance_cont_counted afterPush hpPush hcPush
          hstepJumpi with
        ⟨afterJump, hpJump, hcJump⟩
      rcases frame.advance_cont_counted afterJump hpJump hcJump
          hstepJumpdest with
        ⟨armExec, hpArm, hcArm⟩
      exact Or.inr ⟨⟨loc + 1, _, armExec, hpArm, hcArm, hright,
        hsubRight, hboundRight⟩, getCode_map_eq_of_state_eq hpop.state⟩

/-- Follow one generated internal source call, exposing the crossing's
code-map equality; the counted mirror of
`Exec.Frame.CompiledCursor.enterCall`. -/
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
  cases hrun : cursor.run with
  | call hget hroom hburn hbody =>
      rcases subcode_compile_call cursor.codeSlice with
        ⟨loc, p, hgetTable, hloc, hpushAt, hjump⟩
      have hpf := (Prog.get?_table (m := 0)).symm.trans
        (congrArg (Prod.snd <$> ·) hgetTable)
      rw [hget] at hpf
      simp only [Option.map_eq_map, Option.map_some,
        Option.some.injEq] at hpf
      subst p
      rcases subcode_of_get?_eq_some hcode hgetTable with
        ⟨hjumpdest, hsub⟩
      have hjumpable := Prog.jumpable_of_get?_table hcode hgetTable
      rcases hpushAt with ⟨le, hpush⟩
      rcases Evm.call_steps (le := le) hpush hjump hjumpdest
          hjumpable.1 hloc hroom hburn with
        ⟨hstepPush, hstepJump, hstepJumpdest⟩
      rcases frame.advance_cont_counted cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases frame.advance_cont_counted afterPush hpPush hcPush
          hstepJump with
        ⟨afterJump, hpJump, hcJump⟩
      rcases frame.advance_cont_counted afterJump hpJump hcJump
          hstepJumpdest with
        ⟨bodyExec, hpBody, hcBody⟩
      exact ⟨_, hget, ⟨loc + 1, _, bodyExec, hpBody, hcBody, hbody,
        hsub, hjumpable.2⟩, getCode_map_eq_of_state_eq hburn.state⟩

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

private theorem genericCall_step_spawn_exact_local
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isStatic : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume}
    (hspawn : genericCall.step sevm devm gas value caller target codeAddress
      stv isStatic ii isz oi osz code disablePrecompiles =
        .spawn frame resume) :
    frame = Frame.ofCall
      (callMsg sevm (devm.withReturnData []) gas value caller target
        codeAddress stv isStatic ((devm.memory.read ii isz).1) code
        disablePrecompiles) := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hspawn
  repeat' split at hspawn
  all_goals
    simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hspawn
  all_goals obtain ⟨rfl, rfl⟩ := hspawn
  all_goals exact rfl

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
  have hframe := genericCall_step_spawn_exact_local hspawn
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

/-- Local copy of the counted module's private slice fact: the first
instruction of a compiled `.next` block is installed at the block's
starting program counter. -/
private theorem ninstAt_of_subcode_next_local
    {code : ByteArray} {sourceTable : List (Nat × Func)} {pc : Nat}
    {n : Ninst} {tail : Func}
    (sub : subcode code.toList pc
      (Func.compile sourceTable pc (.next n tail))) :
    Ninst.At code pc n := by
  rcases of_subcode sub with ⟨compiled, compiledEq, slice⟩
  rcases of_bind_eq_some compiledEq with ⟨rest, restEq, headEq⟩
  simp [pure] at headEq
  rw [← headEq] at slice
  exact Ninst.at_of_slice (List.slice_prefix slice)

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
        ninstAt_of_subcode_next_local cursor.codeSlice
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

/-- Select the fall-through arm of a compiled branch when the flag is
known zero, exposing the crossing's code-map equality; the counted mirror
of `Exec.Frame.CountedCursor.selectBranchZero`. -/
private theorem Exec.Frame.CountedCursor.selectBranchZeroCode
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {stack : Stack}
    (cursor : frame.CountedCursor dp ca fs table
      (.branch left right) final)
    (hstack : (0 : B256) :: stack <<+ cursor.pre.stack) :
    ∃ arm : frame.CountedCursor dp ca fs table left final,
      stack <<+ arm.pre.stack ∧
      Devm.getCode cursor.pre = Devm.getCode arm.pre := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      _hjumpdest, _hjumpable, _hsubRight, _hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero hroom hpop hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases frame.advance_cont_counted cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases frame.advance_cont_counted afterPush hpPush hcPush
          hstepJumpi with
        ⟨armExec, hpArm, hcArm⟩
      exact ⟨⟨cursor.pc + 4, _, armExec, hpArm, hcArm, hleft,
        hsubLeft, hboundLeft⟩, hw.2, getCode_map_eq_of_state_eq hpop.state⟩
  | succ hne _hroom hpop _hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hne hw.1).elim

/-- Select the jumped arm of a compiled branch when the flag is known
nonzero, exposing the crossing's code-map equality; the counted mirror of
`Exec.Frame.CountedCursor.selectBranchSucc`. -/
private theorem Exec.Frame.CountedCursor.selectBranchSuccCode
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {flag : B256} {stack : Stack}
    (cursor : frame.CountedCursor dp ca fs table
      (.branch left right) final)
    (hflag : flag ≠ 0)
    (hstack : flag :: stack <<+ cursor.pre.stack) :
    ∃ arm : frame.CountedCursor dp ca fs table right final,
      stack <<+ arm.pre.stack ∧
      Devm.getCode cursor.pre = Devm.getCode arm.pre := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, _hsubLeft, _hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero _hroom hpop _hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hflag hw.1.symm).elim
  | succ hne hroom hpop hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases frame.advance_cont_counted cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases frame.advance_cont_counted afterPush hpPush hcPush
          hstepJumpi with
        ⟨afterJump, hpJump, hcJump⟩
      rcases frame.advance_cont_counted afterJump hpJump hcJump
          hstepJumpdest with
        ⟨armExec, hpArm, hcArm⟩
      exact ⟨⟨loc + 1, _, armExec, hpArm, hcArm, hright,
        hsubRight, hboundRight⟩, hw.2, getCode_map_eq_of_state_eq hpop.state⟩

/-- A successful counted cursor at a nonpayable wrapper reaches its guarded
body, exposing the crossing's code-map equality; the counted mirror of
`Exec.Frame.CountedCursor.enterNonpayable`. -/
private theorem Exec.Frame.CountedCursor.enterNonpayableCode
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {final : Devm}
    (cursor : frame.CountedCursor dp ca fs table
      (nonpayable body) final) :
    ∃ bodyCursor : frame.CountedCursor dp ca fs table body final,
      Devm.getCode cursor.pre = Devm.getCode bodyCursor.pre := by
  have hvalue : frame.sevm.value = 0 :=
    value_eq_zero_of_run_nonpayable
      (Func.Run.of_runCompiled cursor.run)
  change frame.CountedCursor dp ca fs table
    ([Ninst.callvalue, Ninst.iszero] +++ (body <?> Func.rev)) final
    at cursor
  rcases cursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨branchCursor, hline⟩
  have hflagPrefix : [frame.sevm.value =? 0] <<+
      branchCursor.pre.stack := by
    rcases Line.of_run_cons hline with
      ⟨afterValue, hcallvalue, hrestValue⟩
    rcases Line.of_run_cons hrestValue with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    have hvaluePrefix : [frame.sevm.value] <<+ afterValue.stack :=
      prefix_of_push (of_run_callvalue hcallvalue) nil_pref
    exact prefix_of_iszero hzero hvaluePrefix
  rw [hvalue] at hflagPrefix
  have hone : ((0 : B256) =? 0) = 1 := by simp [B256.eqCheck]
  rw [hone] at hflagPrefix
  rcases branchCursor.selectBranchSuccCode (flag := (1 : B256))
      (by decide) hflagPrefix with
    ⟨bodyCursor, _hbodyStack, hcodeBranch⟩
  have hcodeLine : Devm.getCode cursor.pre = Devm.getCode branchCursor.pre :=
    Line.of_inv Devm.getCode (by line_inv) hline
  exact ⟨bodyCursor, hcodeLine.trans hcodeBranch⟩

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

/-- Local copy of the counted module's private burn-determinism fact. -/
private theorem Devm.eq_of_burnBy_local
    {cost : Nat} {pre left right : Devm}
    (hleft : Devm.BurnBy cost pre left)
    (hright : Devm.BurnBy cost pre right) : left = right := by
  apply Devm.eq_of_proj
  · exact hleft.stack.symm.trans hright.stack
  · exact hleft.memory.symm.trans hright.memory
  · have hl := hleft.gasLeft
    have hr := hright.gasLeft
    omega
  · exact hleft.logs.symm.trans hright.logs
  · exact hleft.refundCounter.symm.trans hright.refundCounter
  · exact hleft.output.symm.trans hright.output
  · exact hleft.accountsToDelete.symm.trans hright.accountsToDelete
  · exact hleft.returnData.symm.trans hright.returnData
  · exact hleft.error.symm.trans hright.error
  · exact hleft.accessedAddresses.symm.trans hright.accessedAddresses
  · exact hleft.accessedStorageKeys.symm.trans hright.accessedStorageKeys
  · exact hleft.state.symm.trans hright.state
  · exact hleft.createdAccounts.symm.trans hright.createdAccounts
  · exact hleft.transientStorage.symm.trans hright.transientStorage

private theorem Exec.Frame.compiledMainCursorCode
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca) :
    ∃ mainCursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (weth10 dp).main frame.post,
      Devm.getCode frame.pre = Devm.getCode mainCursor.pre := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hcode := context.invocation.2.2.2
      have hcompiled := Prog.runCompiled_of_exec e pre (weth10 dp) post
        (weth10_pcFree dp) run hcode
      rcases hcompiled with ⟨compiledMid, hcompiledBurn, hmain⟩
      have hget :
          (table 0 (((weth10 dp).main) :: weth10Aux))[0]? =
            some (0, (weth10 dp).main) := rfl
      rcases subcode_of_get?_eq_some hcode hget with ⟨hjumpdest, hsub⟩
      have hboundary : noPushBefore e.code 1 32 = true :=
        (Prog.jumpable_of_get?_table hcode hget).2
      rcases jumpdest_at_exact run hjumpdest with
        ⟨actualMid, continuation, hburn, hgas, _hprec⟩
      have hburnBy := Devm.BurnBy.of_burn hburn hgas
      have hmid : actualMid = compiledMid :=
        Devm.eq_of_burnBy_local hburnBy hcompiledBurn
      subst compiledMid
      have hstep : Evm.step ⟨0, e, pre⟩ = .cont 1 actualMid :=
        Evm.jumpdest_cont hjumpdest hburnBy
      have hrootPrefix : Exec.Deriv.ParentPrefixActions dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨0, e, pre, .ok post, run⟩ [] :=
        Exec.Deriv.ParentPrefixActions.refl _
      have hrootCounted : Exec.Deriv.ParentPrefixCounted dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨0, e, pre, .ok post, run⟩ [] :=
        Exec.Deriv.ParentPrefixCounted.refl _
      rcases Exec.Frame.advance_cont_counted
          (frame := ⟨0, e, pre, .ok post, run, committed⟩)
          run ⟨[], hrootPrefix⟩ hrootCounted hstep with
        ⟨actualContinuation, hentryPrefix, hentryCounted⟩
      exact ⟨⟨1, actualMid, actualContinuation, hentryPrefix,
        hentryCounted, hmain, hsub, hboundary⟩,
        getCode_map_eq_of_state_eq hburnBy.state⟩

private theorem Exec.Frame.CountedCursor.reachDispatchLeafCode
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)} {final : Devm}
    {sig w : B256} {f body : Func} {k : Nat} {stack : Stack}
    (hmem : (sig, f) ∈ [(w, body)])
    (cursor : frame.CountedCursor dp ca fs table
      (dispatchWith k (.leaf w body)) final)
    (hstack : sig :: stack <<+ cursor.pre.stack) :
    ∃ bodyCursor : frame.CountedCursor dp ca fs table f final,
      stack <<+ bodyCursor.pre.stack ∧
      Devm.getCode cursor.pre = Devm.getCode bodyCursor.pre := by
  have heq : (sig, f) = (w, body) := List.mem_singleton.mp hmem
  injection heq with hsig hfun
  subst w
  subst body
  change frame.CountedCursor dp ca fs table
    ([Ninst.pushB256 sig, Ninst.eq] +++ (f <?> .call k)) final at cursor
  rcases cursor.peelChildlessLine
      (by simp [NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, hline⟩
  have hcodeLine : Devm.getCode cursor.pre =
      Devm.getCode branchCursor.pre :=
    Line.of_inv Devm.getCode (by line_inv) hline
  have hflag : (sig =? sig) :: stack <<+ branchCursor.pre.stack := by
    rcases Line.of_run_cons hline with ⟨afterPush, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨afterEq, heqRun, hnil⟩
    cases hnil
    have hpushed : sig :: sig :: stack <<+ afterPush.stack := by
      simpa using prefix_of_push (of_run_pushB256 hpush) hstack
    exact prefix_of_eq heqRun hpushed
  rw [show (sig =? sig) = 1 from by simp [B256.eqCheck]] at hflag
  rcases branchCursor.selectBranchSuccCode
      (left := .call k) (right := f) (flag := (1 : B256))
      (by decide) hflag with
    ⟨bodyCursor, hbodyStack, hcodeBranch⟩
  exact ⟨bodyCursor, hbodyStack, hcodeLine.trans hcodeBranch⟩

private theorem Exec.Frame.CountedCursor.reachDispatchWithCode_build :
    ∀ {n : Nat} {xs : List (B256 × Func)} {sig : B256} {f : Func}
      {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
      {fs : List Func} {table : List (Nat × Func)} {k : Nat}
      {final : Devm} {stack : Stack},
      DispatchTree.sorted xs = true →
      xs.length ≤ n + 1 →
      (sig, f) ∈ xs →
      (cursor : frame.CountedCursor dp ca fs table
        (dispatchWith k (DispatchTree.build n xs)) final) →
      (sig :: stack <<+ cursor.pre.stack) →
      ∃ bodyCursor : frame.CountedCursor dp ca fs table f final,
        stack <<+ bodyCursor.pre.stack ∧
        Devm.getCode cursor.pre = Devm.getCode bodyCursor.pre := by
  intro n
  induction n with
  | zero =>
      intro xs sig f dp ca frame fs table k final stack _hsorted hlen hmem
        cursor hstack
      rcases xs with _ | ⟨⟨w, body⟩, _ | ⟨y, ys⟩⟩
      · cases hmem
      · exact cursor.reachDispatchLeafCode hmem hstack
      · exfalso
        simp only [List.length_cons] at hlen
        omega
  | succ n ih =>
      intro xs sig f dp ca frame fs table k final stack hsorted hlen hmem
        cursor hstack
      rcases xs with _ | ⟨⟨w, body⟩, _ | ⟨y, ys⟩⟩
      · cases hmem
      · exact cursor.reachDispatchLeafCode hmem hstack
      · simp only [List.length_cons] at hlen
        have htakeLen :
            (((w, body) :: y :: ys).take
              ((((w, body) :: y :: ys).length + 1) / 2)).length ≤
              n + 1 := by
          simp only [List.length_take, List.length_cons]
          omega
        have hdropLen :
            (((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2)).length ≤
              n + 1 := by
          simp only [List.length_drop, List.length_cons]
          omega
        obtain ⟨z, zs, hdrop⟩ :
            ∃ z zs, ((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2) = z :: zs := by
          rcases hd : ((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2) with _ | ⟨z, zs⟩
          · exfalso
            have hl := congrArg List.length hd
            simp only [List.length_drop, List.length_cons,
              List.length_nil] at hl
            omega
          · exact ⟨z, zs, rfl⟩
        have hsortedSplit : DispatchTree.sorted
            (((w, body) :: y :: ys).take
                ((((w, body) :: y :: ys).length + 1) / 2) ++
              ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2)) = true := by
          rw [List.take_append_drop]
          exact hsorted
        have hsortedTake := DispatchTree.sorted_append_left hsortedSplit
        have hsortedDrop := DispatchTree.sorted_append_right hsortedSplit
        have hmemSplit :
            (sig, f) ∈ ((w, body) :: y :: ys).take
                ((((w, body) :: y :: ys).length + 1) / 2) ∨
              (sig, f) ∈ ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2) := by
          apply List.mem_append.mp
          rw [List.take_append_drop]
          exact hmem
        change frame.CountedCursor dp ca fs table
          ([Ninst.dup 0,
              Ninst.pushB256 (leftmostFsig
                (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2)))),
              Ninst.gt] +++
            (dispatchWith k
                (DispatchTree.build n
                  (((w, body) :: y :: ys).take
                    ((((w, body) :: y :: ys).length + 1) / 2))) <?>
              dispatchWith k
                (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2))))) final
          at cursor
        rcases cursor.peelChildlessLine
            (by simp [NinstIsChildless, Ninst.pushB256]) with
          ⟨branchCursor, hline⟩
        have hcodeLine : Devm.getCode cursor.pre =
            Devm.getCode branchCursor.pre :=
          Line.of_inv Devm.getCode (by line_inv) hline
        have hflagPrefix :
            (leftmostFsig (DispatchTree.build n
                (((w, body) :: y :: ys).drop
                  ((((w, body) :: y :: ys).length + 1) / 2))) >? sig) ::
              sig :: stack <<+ branchCursor.pre.stack := by
          rcases Line.of_run_cons hline with
            ⟨afterDup, hdup, hrestDup⟩
          rcases Line.of_run_cons hrestDup with
            ⟨afterPush, hpush, hrestPush⟩
          rcases Line.of_run_cons hrestPush with
            ⟨afterGt, hgt, hnil⟩
          cases hnil
          have hdupStack : sig :: sig :: stack <<+ afterDup.stack :=
            prefix_of_dup_val hdup (by show_nth) hstack
          have hpushStack :
              leftmostFsig (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2))) ::
                sig :: sig :: stack <<+ afterPush.stack := by
            simpa using prefix_of_push (of_run_pushB256 hpush) hdupStack
          exact prefix_of_gt hgt hpushStack
        have hleftmost :
            leftmostFsig (DispatchTree.build n
              (((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2))) = z.fst := by
          rw [hdrop, DispatchTree.leftmostFsig_build]
        rw [hleftmost] at hflagPrefix
        rcases hmemSplit with hmemTake | hmemDrop
        · have hlt : sig < z.fst := by
            have hz : z ∈ ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2) := by
              rw [hdrop]
              exact List.mem_cons_self ..
            exact DispatchTree.fst_lt_of_sorted_append
              hsortedSplit hmemTake hz
          have hcheck : (z.fst >? sig) = 1 := by
            simp [B256.gtCheck, hlt]
          rw [hcheck] at hflagPrefix
          rcases branchCursor.selectBranchSuccCode (flag := (1 : B256))
              (by decide) hflagPrefix with
            ⟨leftCursor, hleftStack, hcodeBranch⟩
          rcases ih hsortedTake htakeLen hmemTake leftCursor hleftStack with
            ⟨bodyCursor, hbodyStack, hcodeRec⟩
          exact ⟨bodyCursor, hbodyStack,
            hcodeLine.trans (hcodeBranch.trans hcodeRec)⟩
        · have hle : z.fst ≤ sig := by
            have hsortedZ : DispatchTree.sorted (z :: zs) = true := by
              rw [← hdrop]
              exact hsortedDrop
            rw [hdrop] at hmemDrop
            exact DispatchTree.fst_le_of_sorted_mem hsortedZ hmemDrop
          have hcheck : (z.fst >? sig) = 0 := by
            simp [B256.gtCheck, not_lt_of_ge hle]
          rw [hcheck] at hflagPrefix
          rcases branchCursor.selectBranchZeroCode hflagPrefix with
            ⟨rightCursor, hrightStack, hcodeBranch⟩
          rcases ih hsortedDrop hdropLen hmemDrop rightCursor hrightStack with
            ⟨bodyCursor, hbodyStack, hcodeRec⟩
          exact ⟨bodyCursor, hbodyStack,
            hcodeLine.trans (hcodeBranch.trans hcodeRec)⟩

/-- The counted selector-body entry with the entry segment's code-map
preservation attached; the local mirror of
`Exec.Frame.compiledSelectorBodyCursorCounted`. -/
private theorem Exec.Frame.compiledSelectorBodyCursorCode
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {body : Func}
    (context : frame.AuthenticContext dp ca)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp) :
    ∃ bodyCursor : frame.CountedCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) body frame.post,
      Devm.getCode frame.pre = Devm.getCode bodyCursor.pre := by
  rcases frame.compiledMainCursorCode context with ⟨mainCursor, hcodeMain⟩
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ([Ninst.calldatasize, Ninst.iszero] +++
      (receiveEther <?>
        (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))))
    frame.post at mainCursor
  rcases mainCursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨entryBranchCursor, hentryLine⟩
  have hcodeEntry : Devm.getCode mainCursor.pre =
      Devm.getCode entryBranchCursor.pre :=
    Line.of_inv Devm.getCode (by line_inv) hentryLine
  have hflagPrefix :
      [frame.sevm.data.length.toB256 =? 0] <<+
        entryBranchCursor.pre.stack := by
    rcases Line.of_run_cons hentryLine with
      ⟨afterSize, hsize, hrestSize⟩
    rcases Line.of_run_cons hrestSize with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    have hsizePrefix : [frame.sevm.data.length.toB256] <<+
        afterSize.stack :=
      prefix_of_push (of_run_calldatasize hsize) nil_pref
    exact prefix_of_iszero hzero hsizePrefix
  have hflagZero : (frame.sevm.data.length.toB256 =? 0) = 0 := by
    simp [B256.eqCheck, hnonempty]
  rw [hflagZero] at hflagPrefix
  rcases entryBranchCursor.selectBranchZeroCode hflagPrefix with
    ⟨dispatchPrefixCursor, _hdispatchStack, hcodeEntryBranch⟩
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))
    frame.post at dispatchPrefixCursor
  rcases dispatchPrefixCursor.peelChildlessLine
      (by simp [fsig, cdl, shiftRight, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨dispatchCursor, hfsig⟩
  have hcodeFsig : Devm.getCode dispatchPrefixCursor.pre =
      Devm.getCode dispatchCursor.pre :=
    Line.of_inv Devm.getCode (by
      unfold fsig cdl shiftRight
      line_inv) hfsig
  have hselectorPrefix : Sevm.selector frame.sevm :: [] <<+
      dispatchCursor.pre.stack :=
    prefix_of_fsig nil_pref hfsig
  change frame.CountedCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (dispatchWith fallbackSlot
      (DispatchTree.ofSorted (weth10Funcs dp))) frame.post at dispatchCursor
  rcases dispatchCursor.reachDispatchWithCode_build (weth10Funcs_sorted dp)
      (Nat.le_succ _) hmem hselectorPrefix with
    ⟨bodyCursor, _hbodyStack, hcodeDispatch⟩
  exact ⟨bodyCursor, hcodeMain.trans (hcodeEntry.trans
    (hcodeEntryBranch.trans (hcodeFsig.trans hcodeDispatch)))⟩

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
