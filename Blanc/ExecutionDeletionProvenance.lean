import Blanc.ExecutionRetainedDeletionSafety
import Blanc.ExecutionRetainedCodeSettlement
import Blanc.ExecutionHistoricalAdmission
import Blanc.ExecutionCommittedCell

/-! Deletion-set provenance without an installed-code premise. -/

namespace Blanc

open Jaune

/-- Successful SELFDESTRUCT either preserves the deletion set or inserts only
its own storage-context address. No account-code or creation premise is used. -/
theorem Linst.selfdestruct_accountsToDelete_noStateGas
    {sevm : Sevm} {pre post : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : Linst.Run sevm pre .selfdestruct (.ok post)) :
    post.accountsToDelete = pre.accountsToDelete ∨
      post.accountsToDelete = pre.accountsToDelete.insert sevm.currentTarget := by
  dsimp only [Linst.Run, Linst.run, Except.bind_ok, ne_eq, ite_not,
    Lean.Elab.WF.paramLet, Devm.balReadAccount_accessedAddresses,
    Devm.balReadAccount_getAcct] at run
  simp only [hsg] at run
  obtain ⟨⟨donee, popped⟩, pop, run⟩ := Except.bind_eq_ok run
  dsimp only [Except.bind_ok] at run
  obtain ⟨charged, charge, run⟩ := Except.bind_eq_ok run
  obtain ⟨_, _, run⟩ := Except.bind_eq_ok run
  obtain ⟨debited, debit, run⟩ := Except.bind_eq_ok run
  have accessAtd :
      (match sevm.benvStat.rules.access with
      | .eip2929 =>
          if donee ∉ popped.accessedAddresses then
            (addAccessedAddress
              ((popped.balReadAccount sevm.benvStat.rules donee).balReadAccount
                sevm.benvStat.rules sevm.currentTarget) donee,
              gasSelfDestruct + sevm.benvStat.rules.gas.coldAccountAccess)
          else
            ((popped.balReadAccount sevm.benvStat.rules donee).balReadAccount
              sevm.benvStat.rules sevm.currentTarget, gasSelfDestruct)
      | .flat _ =>
          ((popped.balReadAccount sevm.benvStat.rules donee).balReadAccount
            sevm.benvStat.rules sevm.currentTarget, gasSelfDestruct)).1.accountsToDelete =
        popped.accountsToDelete := by
    have reads : ((popped.balReadAccount sevm.benvStat.rules donee).balReadAccount
        sevm.benvStat.rules sevm.currentTarget).accountsToDelete = popped.accountsToDelete :=
      ((Devm.balReadAccount_instructionFrame _ _ _).accountsToDelete.trans
        (Devm.balReadAccount_instructionFrame _ _ _).accountsToDelete).symm
    cases sevm.benvStat.rules.access with
    | flat _ => exact reads
    | eip2929 => dsimp only; split <;> exact reads
  simp only [Devm.balReadAccount_accessedAddresses] at charge
  have chargeAtd : charged.accountsToDelete = _ :=
    congrArg Prod.fst (chargeGas_delSets_eq charge)
  have popAtd : popped.accountsToDelete = pre.accountsToDelete :=
    congrArg Prod.fst (Devm.popToAdr_delSets_eq pop)
  have chargedAtd := chargeAtd.trans (accessAtd.trans popAtd)
  have debitAtd : debited.accountsToDelete = charged.accountsToDelete := by
    have debitedEq := Jaune.Option.toExcept_eq_ok debit
    unfold Devm.subBal at debitedEq
    obtain ⟨state, _, output⟩ := Jaune.of_bind_eq_some debitedEq
    cases output
    rfl
  let credited := debited.creditBeneficiary sevm.benvStat.rules donee
    (popped.getAcct sevm.currentTarget).bal
  have creditAtd : credited.accountsToDelete = debited.accountsToDelete :=
    congrArg Prod.fst (Devm.creditBeneficiary_delSets _ _ _ _)
  have original : credited.accountsToDelete = pre.accountsToDelete :=
    creditAtd.trans (debitAtd.trans chargedAtd)
  change (if sevm.currentTarget ∈ credited.createdAccounts ∨
      sevm.benvStat.rules.settle.selfdestructOnlyCreated = false then
    .ok (creditSelfdestructRefund sevm.benvStat.rules
      (sevm.currentTarget ∈ credited.accountsToDelete)
      (addAccountToDelete (credited.setBal sevm.currentTarget 0) sevm.currentTarget))
    else .ok credited : Execution) = .ok post at run
  split at run
  · rw [← Except.ok.inj run]
    apply Or.inr
    have refund := congrArg Prod.fst (creditSelfdestructRefund_delSets
      sevm.benvStat.rules (sevm.currentTarget ∈ credited.accountsToDelete)
      (addAccountToDelete (credited.setBal sevm.currentTarget 0) sevm.currentTarget))
    change (creditSelfdestructRefund _ _ _).accountsToDelete = _
    exact refund.trans (congrArg (fun atd : AdrSet => atd.insert sevm.currentTarget) original)
  · rw [← Except.ok.inj run]
    exact Or.inl original

/-- Every newly scheduled terminal deletion belongs to this instruction's
SELFDESTRUCT storage context. -/
theorem Linst.accountsToDelete_origin_noStateGas
    {sevm : Sevm} {pre post : Devm} {l : Linst} {a : Adr}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : Linst.Run sevm pre l (.ok post))
    (member : a ∈ post.accountsToDelete) :
    a ∈ pre.accountsToDelete ∨ (a = sevm.currentTarget ∧ l = .selfdestruct) := by
  by_cases destruct : l = .selfdestruct
  · subst l
    rcases Linst.selfdestruct_accountsToDelete_noStateGas hsg run with unchanged | inserted
    · exact Or.inl (unchanged ▸ member)
    · rw [inserted, Std.HashSet.mem_insert] at member
      rcases member with same | prior
      · exact Or.inr ⟨(eq_of_beq same).symm, rfl⟩
      · exact Or.inl prior
  · have frame := Linst.run_instructionFrame sevm pre l destruct
    rw [run] at frame
    exact Or.inl (frame.accountsToDelete ▸ member)


/-- An early CREATE completion never adds a scheduled deletion. -/
theorem GenericCreate.step_done_atd
    {sevm : Sevm} {pre post : Devm} {endowment : B256} {address : Adr}
    {mi ms : Nat}
    (step : genericCreate.step sevm pre endowment address mi ms = .done (.ok post)) :
    post.accountsToDelete = pre.accountsToDelete := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at step
  repeat' split at step
  all_goals simp only [XStep.ofExcept, reduceCtorEq, XStep.done.injEq,
    Except.ok.injEq] at step
  all_goals subst post
  all_goals rename_i pushed pushEq
  all_goals exact congrArg Prod.fst (Devm.push_delSets_eq pushEq)

/-- An early CALL completion never adds a scheduled deletion. -/
theorem GenericCall.step_done_atd
    {sevm : Sevm} {pre post : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dp : Bool}
    (step : genericCall.step sevm pre gas value caller target codeAddress stv
      isSt ii isz oi osz code dp = .done (.ok post)) :
    post.accountsToDelete = pre.accountsToDelete := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at step
  repeat' split at step
  all_goals simp only [XStep.ofExcept, reduceCtorEq, XStep.done.injEq,
    Except.ok.injEq] at step
  all_goals subst post
  rename_i pushed pushEq
  exact congrArg Prod.fst (Devm.push_delSets_eq pushEq)

/-- A childless executable instruction preserves the deletion set. -/
theorem Xinst.step_done_atd_noStateGas
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Xinst.step sevm pre x = .done (.ok post)) :
    post.accountsToDelete = pre.accountsToDelete := by
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with
    ⟨out, shape, frame⟩ | ⟨d, value, address, mi, ms, frame, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isSt,
      ii, isz, oi, osz, code, dp, frame, _, _, _, shape⟩
  · rw [shape] at step
    cases step
    exact frame.accountsToDelete.symm
  · rw [shape] at step
    exact (GenericCreate.step_done_atd step).trans frame.accountsToDelete.symm
  · rw [shape] at step
    exact (GenericCall.step_done_atd step).trans frame.accountsToDelete.symm

/-- Ordinary continuation steps cannot schedule deletions. -/
theorem Evm.step_cont_atd_noStateGas {pc pc' : Nat} {sevm : Sevm}
    {pre post : Devm}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post) :
    post.accountsToDelete = pre.accountsToDelete := by
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none => rw [Evm.step_invOp decoded] at step; cases step
  | some instruction =>
    cases instruction with
    | last last => rw [Evm.step_last decoded] at step; cases step
    | jump jumpInst =>
      rw [Evm.step_jump decoded] at step
      cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
      | error error => rw [jumpEq] at step; cases step
      | ok pair =>
        rcases pair with ⟨actualPc, actualPost⟩
        rw [jumpEq] at step
        cases step
        exact congrArg Prod.fst (Jinst.inv_delSets jumpEq)
    | next instruction =>
      have nstep : Ninst.step ⟨pc, sevm, pre⟩ instruction = .cont pc' post := by
        rw [← Evm.step_next decoded]
        exact step
      have nrun : Ninst.StepRun pc sevm pre instruction .none (.ok post) := by
        unfold Ninst.StepRun
        rw [nstep]
        exact ⟨rfl, rfl⟩
      cases instruction with
      | exec executable =>
        simp only [Ninst.step_exec, XStep.toStep] at nstep
        cases actual : Xinst.step sevm pre executable with
        | spawn frame resume => rw [actual] at nstep; cases nstep
        | done out =>
          rw [actual] at nstep
          cases out with
          | error error => cases nstep
          | ok actualPost =>
            cases nstep
            exact Xinst.step_done_atd_noStateGas hsg actual
      | reg regular =>
        have run : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post :=
          ((Step.run_ofExecution (xl := (.none : Xlot))).mp nrun).2.symm
        exact (congrArg Prod.fst (Rinst.inv_delSets run)).symm
      | push bytes bound =>
        exact (Ninst.push_instructionFrame_effectRec
          (hxs := bound) (xl := .none) trivial nrun).accountsToDelete.symm
      | dupn imm =>
        exact (Ninst.dupn_instructionFrame_effectRec
          (xl := .none) trivial nrun).accountsToDelete.symm
      | swapn imm =>
        exact (Ninst.swapn_instructionFrame_effectRec
          (xl := .none) trivial nrun).accountsToDelete.symm
      | exchange imm =>
        exact (Ninst.exchange_instructionFrame_effectRec
          (xl := .none) trivial nrun).accountsToDelete.symm

/-- A committed CREATE resumption merges exactly parent and child deletions. -/
theorem Resume.create_atd_of_clean {parent child post : Devm} {address : Adr}
    (clean : child.error.isSome = false)
    (run : (Resume.create parent address).run (.ok child) = .ok post) :
    post.accountsToDelete = parent.accountsToDelete.union child.accountsToDelete := by
  simp only [Resume.run, liftToExecution, Bind.bind, Except.bind, clean,
    Bool.false_eq_true, ↓reduceIte] at run
  exact congrArg Prod.fst (Devm.push_delSets_eq run)

/-- A committed CALL resumption merges exactly parent and child deletions. -/
theorem Resume.call_atd_of_clean {parent child post : Devm} {oi os : Nat}
    (clean : child.error.isSome = false)
    (run : (Resume.call parent oi os).run (.ok child) = .ok post) :
    post.accountsToDelete = parent.accountsToDelete.union child.accountsToDelete := by
  simp only [Resume.run, liftToExecution, Bind.bind, Except.bind, clean,
    Bool.false_eq_true, ↓reduceIte] at run
  cases hp : (incorporateChildOnSuccess parent child child.output).push 1 with
  | error e => simp only [hp, reduceCtorEq] at run
  | ok pushed =>
    simp only [hp, Except.ok.injEq] at run
    subst post
    exact congrArg Prod.fst (Devm.push_delSets_eq hp)


/-- Child entry inherits only deletions already present in the spawning parent. -/
theorem Evm.step_spawn_enter_atd_subset_noStateGas
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume} {child : Evm} {a : Adr}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run child)
    (member : a ∈ child.dyna.accountsToDelete) : a ∈ pre.accountsToDelete := by
  obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with
    ⟨execution, shape, _⟩ |
    ⟨d, endowment, address, mi, ms, pref, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, dp, pref, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · obtain ⟨rfl, rfl⟩ := genericCreate_step_spawn_exact spawn
    obtain ⟨entry, transfer, childEq⟩ := Frame.enter_run_inv enter
    rw [childEq] at member
    change a ∈ (if sevm.benvStat.rules.settle.selfdestructRefund = 0 then
      ∅ else d.accountsToDelete) at member
    split at member
    · exact False.elim (AdrSet.not_mem_empty member)
    · exact pref.accountsToDelete ▸ member
  · obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
    obtain ⟨entry, transfer, childEq⟩ := Frame.enter_run_inv enter
    rw [childEq] at member
    change a ∈ (if sevm.benvStat.rules.settle.selfdestructRefund = 0 then
      ∅ else d.accountsToDelete) at member
    split at member
    · exact False.elim (AdrSet.not_mem_empty member)
    · exact pref.accountsToDelete ▸ member

/-- A selected child return introduces only deletions from that child's raw
committed endpoint, in addition to the saved spawning parent's deletions. -/
theorem Evm.step_spawn_resume_atd_origin_noStateGas
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {child : Evm} {raw : Execution} {a : Adr}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run child)
    (selected : Frame.settlementCommits frame raw = true)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (member : a ∈ post.accountsToDelete) :
    a ∈ pre.accountsToDelete ∨
      a ∈ (Execution.committedPost raw
        (Frame.raw_commits_of_settlementCommits selected)).accountsToDelete := by
  obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with
    ⟨execution, shape, _⟩ |
    ⟨d, endowment, address, mi, ms, pref, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, dp, pref, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · obtain ⟨rfl, rfl⟩ := genericCreate_step_spawn_exact spawn
    cases settled : (Frame.ofCreate (createMsg sevm
        (addAccessedAddress (((d.withGasLeft (d.gasLeft - except64th d.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) address)
        (except64th d.gasLeft) endowment address (d.memory.read mi ms).1)).settle raw with
    | error err => simp only [Frame.settlementCommits, settled, Bool.false_eq_true] at selected
    | ok result =>
      have clean : result.error.isSome = false := by
        simpa only [Frame.settlementCommits, settled, Option.isNone_iff_eq_none,
          Option.isSome_eq_false_iff] using selected
      have process : ProcessCreateMessage _ (.some ⟨child, raw⟩) (.ok result) :=
        settled ▸ RunFrame.of_run enter
      obtain ⟨inner, charged, innerRun, _, charge, installed⟩ :=
        ProcessCreateMessage.ok_charge_of_clean process clean
      have resultAtd : result.accountsToDelete =
          (Execution.committedPost raw
            (Frame.raw_commits_of_settlementCommits selected)).accountsToDelete := by
        rw [installed]
        have chargeAtd : charged.accountsToDelete = inner.accountsToDelete :=
          congrArg Prod.fst (chargeCodeGas_delSets_ok charge)
        exact chargeAtd.trans (ProcessMessage.ok_atd_eq_committedPost innerRun
          (Frame.raw_commits_of_settlementCommits selected))
      rw [settled] at resumed
      rw [Resume.create_atd_of_clean clean resumed] at member
      have member := Std.HashSet.mem_union_iff.mp member
      rcases member with prior | added
      · exact Or.inl (pref.accountsToDelete ▸ prior)
      · exact Or.inr (resultAtd ▸ added)
  · obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
    cases settled : (Frame.ofCall (callMsg sevm (d.withReturnData []) gas value caller target
        codeAddress stv isStatic (d.memory.read ii isz).1 code dp)).settle raw with
    | error err => simp only [Frame.settlementCommits, settled, Bool.false_eq_true] at selected
    | ok result =>
      have clean : result.error.isSome = false := by
        simpa only [Frame.settlementCommits, settled, Option.isNone_iff_eq_none,
          Option.isSome_eq_false_iff] using selected
      have process : ProcessMessage _ (.some ⟨child, raw⟩) (.ok result) :=
        settled ▸ RunFrame.of_run enter
      have resultAtd := ProcessMessage.ok_atd_eq_committedPost process
        (Frame.raw_commits_of_settlementCommits selected)
      rw [settled] at resumed
      rw [Resume.call_atd_of_clean clean resumed] at member
      have member := Std.HashSet.mem_union_iff.mp member
      rcases member with prior | added
      · exact Or.inl (pref.accountsToDelete ▸ prior)
      · exact Or.inr (resultAtd ▸ added)


/-- Precompiles preserve the inherited deletion set, including handled failures. -/
theorem executeCode.handle_precompile_ok_atd
    {msg : Msg} {address : Adr} {post : Devm} {stateGas : Option StateGasRules}
    (h : executeCode.handleErrorWith stateGas
        (executePrecomp (initEvm msg) address) = .ok post) :
    post.accountsToDelete = msg.inheritedDeletions := by
  cases hsg : stateGas
  · simp only [hsg, executeCode.handleErrorWith] at h
    unfold executePrecomp applyPrecompResult at h
    cases hpre : precompileRun (initEvm msg) address with
    | error error cost =>
      simp only [hpre] at h
      cases error <;> simp only [executeCode.handleError, Except.ok.injEq, reduceCtorEq] at h
      · exact (congrArg Devm.accountsToDelete h).symm.trans rfl
      · exact (congrArg Devm.accountsToDelete h).symm.trans rfl
    | ok cost output =>
      simp only [executeCode.handleError, hpre, Except.ok.injEq] at h
      exact (congrArg Devm.accountsToDelete h).symm.trans rfl
  · simp only [hsg, executeCode.handleErrorWith] at h
    unfold executePrecomp applyPrecompResult at h
    cases hpre : precompileRun (initEvm msg) address with
    | error error cost =>
      simp only [hpre] at h
      cases error <;> simp only [executeCode.handleErrorAmsterdam, Except.ok.injEq, reduceCtorEq] at h
      · exact (congrArg Devm.accountsToDelete h).symm.trans rfl
      · exact (congrArg Devm.accountsToDelete h).symm.trans rfl
    | ok cost output =>
      simp only [executeCode.handleErrorAmsterdam, hpre, Except.ok.injEq] at h
      exact (congrArg Devm.accountsToDelete h).symm.trans rfl

/-- A synchronous message result contains exactly its inherited deletions. -/
theorem ProcessMessage.none_ok_atd {msg : Msg} {post : Devm}
    (process : ProcessMessage msg .none (.ok post)) :
    post.accountsToDelete = msg.inheritedDeletions := by
  obtain ⟨result, body, settled⟩ := ProcessMessage.iff_body.mp process
  unfold FrameBody at body
  cases transfer : msg.benvAfterTransfer with
  | error error =>
    rw [transfer] at body
    rw [body.2, processMessage.settle_error] at settled
    cases settled
  | ok entry =>
    rw [transfer] at body
    rcases of_executeCode_cases body with ⟨address, execute⟩ | ⟨raw, impossible, _⟩
    · cases result with
      | error error =>
        rw [processMessage.settle_error] at settled
        cases settled
      | ok raw =>
        have inherited := executeCode.handle_precompile_ok_atd execute
        unfold processMessage.settle at settled
        simp only [bind, Except.bind] at settled
        split at settled <;>
          exact (congrArg Devm.accountsToDelete (Except.ok.inj settled)).trans inherited
    · cases impossible

/-- Clean synchronous CREATE deposit keeps the inherited deletion set. -/
theorem ProcessCreateMessage.none_ok_atd_of_clean {msg : Msg} {post : Devm}
    (process : ProcessCreateMessage msg .none (.ok post))
    (clean : post.error.isSome = false) :
    post.accountsToDelete = msg.inheritedDeletions := by
  obtain ⟨inner, charged, innerRun, _, charge, installed⟩ :=
    ProcessCreateMessage.ok_charge_of_clean process clean
  rw [installed]
  have chargeAtd : charged.accountsToDelete = inner.accountsToDelete :=
    congrArg Prod.fst (chargeCodeGas_delSets_ok charge)
  have innerAtd := ProcessMessage.none_ok_atd innerRun
  exact chargeAtd.trans innerAtd

/-- A successful terminal driver step either keeps a deletion or executes
SELFDESTRUCT at that deletion's storage context. -/
theorem Evm.step_halt_atd_origin_noStateGas {pc : Nat} {sevm : Sevm}
    {pre post : Devm} {a : Adr}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .halt (.ok post))
    (member : a ∈ post.accountsToDelete) :
    a ∈ pre.accountsToDelete ∨
      (sevm.currentTarget = a ∧ Linst.At sevm.code pc .selfdestruct) := by
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none => rw [Evm.step_invOp decoded] at step; cases step
  | some instruction =>
    cases instruction with
    | next n =>
      rw [Evm.step_next decoded] at step
      exact (Ninst.step_ne_halt_ok step).elim
    | jump j =>
      rw [Evm.step_jump decoded] at step
      exact (Step.ofJump_ne_halt_ok step).elim
    | last l =>
      rw [Evm.step_last decoded] at step
      have run : Linst.Run sevm pre l (.ok post) := Step.halt.inj step
      rcases Linst.accountsToDelete_origin_noStateGas hsg run member with prior | ⟨same, rfl⟩
      · exact Or.inl prior
      · exact Or.inr ⟨same.symm, decoded⟩


/-- Synchronous child completion cannot originate a deletion. -/
theorem Evm.step_doneOk_atd_subset_noStateGas
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {result : MessageExecution} {a : Adr}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .done result)
    (resumed : resume.run result = .ok post)
    (member : a ∈ post.accountsToDelete) : a ∈ pre.accountsToDelete := by
  obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with
    ⟨execution, shape, _⟩ |
    ⟨d, endowment, address, mi, ms, pref, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, dp, pref, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · obtain ⟨rfl, rfl⟩ := genericCreate_step_spawn_exact spawn
    cases result with
    | error err => exact (Resume.create_run_error resumed).elim
    | ok child =>
      by_cases failed : child.error.isSome = true
      · rw [Resume.create_atd_of_error failed resumed] at member
        exact pref.accountsToDelete ▸ member
      · have clean : child.error.isSome = false := Bool.eq_false_iff.mpr failed
        have atd := ProcessCreateMessage.none_ok_atd_of_clean (RunFrame.of_done enter) clean
        rw [Resume.create_atd_of_clean clean resumed] at member
        rcases Std.HashSet.mem_union_iff.mp member with prior | added
        · exact pref.accountsToDelete ▸ prior
        · rw [atd] at added
          change a ∈ (if sevm.benvStat.rules.settle.selfdestructRefund = 0 then
            ∅ else d.accountsToDelete) at added
          split at added
          · exact (AdrSet.not_mem_empty added).elim
          · exact pref.accountsToDelete ▸ added
  · obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
    cases result with
    | error err => exact (Resume.call_run_error resumed).elim
    | ok child =>
      by_cases failed : child.error.isSome = true
      · rw [Resume.call_atd_of_error failed resumed] at member
        exact pref.accountsToDelete ▸ member
      · have clean : child.error.isSome = false := Bool.eq_false_iff.mpr failed
        have atd := ProcessMessage.none_ok_atd (RunFrame.of_done enter)
        rw [Resume.call_atd_of_clean clean resumed] at member
        rcases Std.HashSet.mem_union_iff.mp member with prior | added
        · exact pref.accountsToDelete ▸ prior
        · rw [atd] at added
          change a ∈ (if sevm.benvStat.rules.settle.selfdestructRefund = 0 then
            ∅ else d.accountsToDelete) at added
          split at added
          · exact (AdrSet.not_mem_empty added).elim
          · exact pref.accountsToDelete ▸ added

/-- Every newly scheduled deletion in a committing execution comes from a
SELFDESTRUCT node retained by complete settlement. This includes accounts
created during the same execution; no entry code or created-set premise is used. -/
theorem Exec.retained_atd_origin_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none) {a : Adr}
    (member : a ∈ (Execution.committedPost out committed).accountsToDelete) :
    a ∈ pre.accountsToDelete ∨ ∃ node ∈ Exec.retainedNodes run,
      node.sevm.currentTarget = a ∧ Linst.At node.sevm.code node.pc .selfdestruct := by
  revert committed hsg member
  induction run with
  | @halt pc sevm pre result hstep =>
    intro committed hsg member
    cases result with
    | error error => cases committed
    | ok post =>
      rcases Evm.step_halt_atd_origin_noStateGas hsg hstep member with prior | terminal
      · exact Or.inl prior
      · refine Or.inr ⟨⟨pc, sevm, pre, .ok post, .halt hstep⟩, ?_, terminal⟩
        rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits]
        exact List.mem_cons_self
  | cont hstep next ih =>
    intro committed hsg member
    rcases ih committed hsg member with prior | ⟨node, hn, ht⟩
    · exact Or.inl (Evm.step_cont_atd_noStateGas hsg hstep ▸ prior)
    · refine Or.inr ⟨node, ?_, ht⟩
      rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
        ← Exec.retainedNodes_eq_of_commits next committed]
      exact List.mem_cons_of_mem _ hn
  | doneErr hstep enter resumed =>
    intro committed
    cases committed
  | doneOk hstep enter resumed next ih =>
    intro committed hsg member
    rcases ih committed hsg member with prior | ⟨node, hn, ht⟩
    · exact Or.inl (Evm.step_doneOk_atd_subset_noStateGas hsg hstep enter resumed prior)
    · refine Or.inr ⟨node, ?_, ht⟩
      rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
        ← Exec.retainedNodes_eq_of_commits next committed]
      exact List.mem_cons_of_mem _ hn
  | runErr hstep enter child resumed ihc =>
    intro committed
    cases committed
  | @runOk pc sevm pre frame resume pc' childEvm raw post out
      hstep enter child resumed next ihc ih =>
    intro committed hsg member
    by_cases selected : Frame.settlementCommits frame raw = true
    · have chronology := Exec.retainedNodes_runOk_of_settlementCommits
        hstep enter child resumed next committed selected
      rcases ih committed hsg member with prior | ⟨node, hn, ht⟩
      · rcases Evm.step_spawn_resume_atd_origin_noStateGas hsg hstep enter
          selected resumed prior with initial | added
        · exact Or.inl initial
        · have childCommitted := Frame.raw_commits_of_settlementCommits selected
          have childGas := (Evm.step_spawn_child_benvStat hstep enter).symm ▸ hsg
          rcases ihc childCommitted childGas added with inherited | ⟨node, hn, ht⟩
          · exact Or.inl (Evm.step_spawn_enter_atd_subset_noStateGas hsg hstep enter inherited)
          · refine Or.inr ⟨node, ?_, ht⟩
            rw [chronology]
            exact List.mem_cons_of_mem _ (List.mem_append_left _ hn)
      · refine Or.inr ⟨node, ?_, ht⟩
        rw [chronology]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hn)
    · have chronology := Exec.retainedNodes_runOk_of_not_settlementCommits
        hstep enter child resumed next committed selected
      rcases ih committed hsg member with prior | ⟨node, hn, ht⟩
      · exact Or.inl (Evm.step_spawn_resume_atd_of_discarded_noStateGas
          hsg hstep selected resumed ▸ prior)
      · refine Or.inr ⟨node, ?_, ht⟩
        rw [chronology]
        exact List.mem_cons_of_mem _ hn

/-- Retained terminal exclusion preserves deletion absence even for accounts
created after root entry. -/
theorem Exec.not_mem_atd_of_retained_terminal_safe
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none) {a : Adr}
    (initial : a ∉ pre.accountsToDelete)
    (safe : ∀ node ∈ Exec.retainedNodes run,
      node.sevm.currentTarget = a → ¬ Linst.At node.sevm.code node.pc .selfdestruct) :
    a ∉ (Execution.committedPost out committed).accountsToDelete := by
  intro member
  rcases Exec.retained_atd_origin_noStateGas run committed hsg member with prior | ⟨node, hn, ht⟩
  · exact initial prior
  · exact safe node hn ht.1 ht.2

namespace ExecutionTrace

/-- A selected interpreter root inherits exactly the enclosing message's
deletion set; creating its account does not add a pending deletion. -/
theorem RetainedXlot.settledRoot_entry_atd
    {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot) (process : RunFrame frame slot out)
    {R : Exec.Frame} (member : R ∈ retained.settledRoots) :
    R.pre.accountsToDelete = frame.inner.inheritedDeletions := by
  cases retained with
  | none => cases member
  | some run =>
    simp only [RetainedXlot.settledRoots] at member
    split at member
    · rw [List.mem_singleton] at member
      subst R
      obtain ⟨benv, transfer, entered⟩ := Frame.enter_run_inv (RunFrame.some_inv process).1
      exact congrArg (fun evm : Evm => evm.dyna.accountsToDelete) entered
    · cases member

/-- CALL settlement selects its original root without changing its entry set. -/
theorem ProcessMessageTrace.settledRoot_entry_atd
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out)
    {R : Exec.Frame} (member : R ∈ trace.settledRoots) :
    R.pre.accountsToDelete = msg.inheritedDeletions := by
  rcases trace with ⟨slot, retained, process⟩
  have entry := retained.settledRoot_entry_atd process (R := R)
  cases retained with
  | none => cases member
  | some run =>
    simp only [ProcessMessageTrace.settledRoots] at member
    split at member
    · exact entry member
    · cases member

/-- CREATE initialization changes the world but preserves inherited deletions. -/
theorem ProcessCreateMessageTrace.settledRoot_entry_atd
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out)
    {R : Exec.Frame} (member : R ∈ trace.settledRoots) :
    R.pre.accountsToDelete = msg.inheritedDeletions := by
  rcases trace with ⟨slot, retained, process⟩
  have entry := retained.settledRoot_entry_atd process (R := R)
  cases retained with
  | none => cases member
  | some run =>
    simp only [ProcessCreateMessageTrace.settledRoots] at member
    split at member
    · exact entry member
    · cases member

/-- Code delegation and CREATE preparation preserve the selected root's
incoming deletion set, independently of the target account's initial code. -/
theorem MessageCallTrace.settledRoot_entry_atd
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    {R : Exec.Frame} (member : R ∈ trace.settledRoots) :
    R.pre.accountsToDelete = msg.inheritedDeletions := by
  cases trace with
  | createCollision => cases member
  | createRun target collision evm core inner result =>
    exact inner.settledRoot_entry_atd member
  | callRun target delegated refund delegation execMsg execMsgEq evm core inner result =>
    rw [inner.settledRoot_entry_atd member, execMsgEq,
      messageCallExecutionMessage_inherited delegation]

/-- Every address is absent from an actual transaction root's initial deletion
set. This is a preparation fact, not a supplied installed-account invariant. -/
theorem TransactionTrace.settledRoot_entry_not_deleted
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    {R : Exec.Frame} (member : R ∈ trace.settledRoots) (a : Adr) :
    a ∉ R.pre.accountsToDelete := by
  rw [trace.message.settledRoot_entry_atd member]
  exact trace.not_mem_msg_inheritedDeletions a

/-- Retained terminal safety alone excludes final deletion for an actual
transaction, even if the account was created earlier in this same root. -/
theorem TransactionTrace.not_deleted_of_retained_terminal_safe
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    {R : Exec.Frame} (member : R ∈ trace.settledRoots) {a : Adr}
    (safe : ∀ node ∈ Exec.retainedNodes R.run,
      node.sevm.currentTarget = a → ¬ Linst.At node.sevm.code node.pc .selfdestruct) :
    a ∉ trace.messageOut.accountsToDelete := by
  have frames : R ∈ trace.settledFrames := by
    rw [trace.settledFrames_eq]
    exact List.mem_flatMap.mpr ⟨R, member, by
      simp only [Exec.committedFrames, R.committed, ↓reduceDIte]
      exact List.mem_cons_self⟩
  have raw := trace.message.mem_rawFrames_of_mem_settledFrames R frames
  have rootGas : R.sevm.benvStat.rules.stateGas = none :=
    (trace.rootEntryIn (F := fun fork => fork.ruleSet.stateGas = none) hsg _ raw).2
  exact trace.not_mem_accountsToDelete_of_settledRoot hsg member
    (Exec.not_mem_atd_of_retained_terminal_safe R.run R.committed rootGas
      (trace.settledRoot_entry_not_deleted member a) safe)

/-- Nonempty code at an actual retained node reaches the transaction endpoint
once retained terminals at that address are safe. No entry installation,
not-created premise or supplied final deletion exclusion remains. -/
theorem TransactionTrace.retainedNode_getCode_of_terminal_safe
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    {R : Exec.Frame} (member : R ∈ trace.settledRoots)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.run) {a : Adr}
    (nonempty : (N.devm.getCode a).toList ≠ [])
    (safe : ∀ node ∈ Exec.retainedNodes R.run,
      node.sevm.currentTarget = a → ¬ Linst.At node.sevm.code node.pc .selfdestruct) :
    state.getCode a = N.devm.getCode a := by
  exact trace.retainedNode_getCode_noStateGas hsg member retained nonempty
    (trace.not_deleted_of_retained_terminal_safe hsg member safe)

/-- A clean CALL result is deletion-free at an address when its actual retained
roots are; synchronous precompiles only carry the inherited set. -/
theorem ProcessMessageTrace.not_deleted_of_settledRoots
    {msg : Msg} {post : Devm} (trace : ProcessMessageTrace msg (.ok post))
    (clean : post.error.isNone = true) {a : Adr}
    (inherited : a ∉ msg.inheritedDeletions)
    (roots : ∀ R ∈ trace.settledRoots, a ∉ R.post.accountsToDelete) :
    a ∉ post.accountsToDelete := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => rw [ProcessMessage.none_ok_atd process]; exact inherited
  | @some pc sevm pre raw run =>
    have settles : Frame.settlementCommits (Frame.ofCall msg) raw = true := by
      unfold Frame.settlementCommits
      rw [← (RunFrame.some_inv process).2]
      exact clean
    have committed := Frame.raw_commits_of_settlementCommits settles
    have member : Exec.Frame.ofRun run committed ∈
        (ProcessMessageTrace.mk _ (.some run) process).settledRoots := by
      simp only [ProcessMessageTrace.settledRoots, settles, ↓reduceIte,
        RetainedXlot.settledRoots, committed, ↓reduceDIte, List.mem_singleton]
    rw [(ProcessMessageTrace.mk _ (.some run) process).settledRoot_post_atd member]
    exact roots _ member

/-- Clean CREATE deposit preserves root deletion exclusion; synchronous
completion introduces no deletion beyond the inherited set. -/
theorem ProcessCreateMessageTrace.not_deleted_of_settledRoots
    {msg : Msg} {post : Devm} (trace : ProcessCreateMessageTrace msg (.ok post))
    (clean : post.error.isNone = true) {a : Adr}
    (inherited : a ∉ msg.inheritedDeletions)
    (roots : ∀ R ∈ trace.settledRoots, a ∉ R.post.accountsToDelete) :
    a ∉ post.accountsToDelete := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
    rw [ProcessCreateMessage.none_ok_atd_of_clean process
      (by cases eq : post.error with
          | none => rfl
          | some error => rw [eq] at clean; cases clean)]
    exact inherited
  | @some pc sevm pre raw run =>
    have settles : Frame.settlementCommits (Frame.ofCreate msg) raw = true := by
      unfold Frame.settlementCommits
      rw [← (RunFrame.some_inv process).2]
      exact clean
    have committed := Frame.raw_commits_of_settlementCommits settles
    have member : Exec.Frame.ofRun run committed ∈
        (ProcessCreateMessageTrace.mk _ (.some run) process).settledRoots := by
      simp only [ProcessCreateMessageTrace.settledRoots, settles, ↓reduceIte,
        RetainedXlot.settledRoots, committed, ↓reduceDIte, List.mem_singleton]
    rw [(ProcessCreateMessageTrace.mk _ (.some run) process).settledRoot_post_atd member]
    exact roots _ member

/-- Deletion exclusion through every message outcome, including empty retained
root lists and discarded constructor/code-deposit executions. -/
theorem MessageCallTrace.not_deleted_of_settledRoots
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none) {a : Adr}
    (inherited : a ∉ msg.inheritedDeletions)
    (roots : ∀ R ∈ trace.settledRoots, a ∉ R.post.accountsToDelete) :
    a ∉ out.accountsToDelete := by
  cases trace with
  | createCollision target collision result =>
    exact (processMessageCall_createCollision_out_noStateGas hsg target collision result).2 a
  | createRun target collision evm core inner result =>
    exact (processMessageCall_createRun_noDel_of_clean hsg target collision core result
      (fun clean => inner.not_deleted_of_settledRoots clean inherited roots)).2
  | callRun target delegated refund delegation execMsg execMsgEq evm core inner result =>
    have execInherited : a ∉ execMsg.inheritedDeletions := by
      rw [execMsgEq, messageCallExecutionMessage_inherited delegation]
      exact inherited
    exact (processMessageCall_callRun_noDel_of_clean hsg target delegation execMsgEq core result
      (fun clean => inner.not_deleted_of_settledRoots clean execInherited roots)).2

/-- An actual transaction is deletion-free when every retained root excludes
SELFDESTRUCT at the address. No retained root need exist. -/
theorem TransactionTrace.not_deleted_of_retained_terminals
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (safe : ∀ R ∈ trace.settledRoots, ∀ node ∈ Exec.retainedNodes R.run,
      node.sevm.currentTarget = a → ¬ Linst.At node.sevm.code node.pc .selfdestruct) :
    a ∉ trace.messageOut.accountsToDelete := by
  by_cases existsRoot : ∃ R, R ∈ trace.settledRoots
  · obtain ⟨R, member⟩ := existsRoot
    exact trace.not_deleted_of_retained_terminal_safe hsg member (safe R member)
  · exact trace.message.not_deleted_of_settledRoots
      (by rw [prepareMessage_benv trace.prepared]; exact hsg)
      (trace.not_mem_msg_inheritedDeletions a)
      (fun R member => (existsRoot ⟨R, member⟩).elim)

/-- Installed nonempty, nondesignator code survives a transaction under actual
retained terminal safety, including accounts created earlier in the block. -/
theorem TransactionTrace.code_preserved_of_retained_terminals
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) {a : Adr} {C : ByteArray}
    (installed : benv.state.getCode a = C) (nonempty : C.toList ≠ [])
    (nondesignator : ¬ isValidDelegation C)
    (safe : ∀ R ∈ trace.settledRoots, ∀ node ∈ Exec.retainedNodes R.run,
      node.sevm.currentTarget = a → ¬ Linst.At node.sevm.code node.pc .selfdestruct) :
    a ∉ trace.messageOut.accountsToDelete ∧ state.getCode a = C := by
  have notDeleted := trace.not_deleted_of_retained_terminals hsg safe
  refine ⟨notDeleted, ?_⟩
  exact (trace.cell_property_of_settledRoots 0 hsg installed nonempty nondesignator notDeleted
    (fun _ => True) (by intro R member ready; trivial) trivial).2

/-- Sequential transactions preserve code from its actual installation state.
The account may occur in the block's created-account set; only actual retained
terminals constrain deletion, including transactions with no retained roots. -/
theorem ApplyTransactionsTrace.code_preserved_of_retained_terminals
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr} {C : ByteArray}
    (installed : benv.state.getCode a = C) (nonempty : C.toList ≠ [])
    (nondesignator : ¬ isValidDelegation C)
    (safe : ∀ R ∈ trace.settledRoots, ∀ node ∈ Exec.retainedNodes R.run,
      node.sevm.currentTarget = a → ¬ Linst.At node.sevm.code node.pc .selfdestruct) :
    trace.NoDelScheduled a ∧ finalBenv.state.getCode a = C := by
  induction trace with
  | nil => exact ⟨trivial, installed⟩
  | cons head tail ih =>
    obtain ⟨headSafe, headCode⟩ := head.code_preserved_of_retained_terminals hsg
      installed nonempty nondesignator
      (fun R member => safe R (List.mem_append_left _ member))
    obtain ⟨tailSafe, finalCode⟩ := ih hsg headCode
      (fun R member => safe R (List.mem_append_right _ member))
    exact ⟨⟨headSafe, tailSafe⟩, finalCode⟩

end ExecutionTrace

end Blanc
