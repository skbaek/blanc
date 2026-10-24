import Blanc.ExecutionAccountingReplay

/-!
# Historical accounting step seams (`stateGas = none` twins)

The modern step seams used by the accounting core
(`Xinst.targetBalanceMono_of_none`, `Ninst.targetBalanceMono_of_none`,
`Ninst.foreignNone_getStor_eq`, `SettlementCarrier.xinstForeignSome_observed`
and its `ReplayCarrier` wrapper) take `CoveredFork` only to reach the
executable-instruction shape `Xinst.step_shapeCovered`, which is itself the
`stateGas = none` shape `Xinst.step_shapeNoStateGas` read through
`CoveredFork.rules_stateGas_none`.

This module is the additive historical counterpart: the same statements over
`sevm.benvStat.rules.stateGas = none`, with no fork-domain premise at all.
The fork-free `Ninst.foreignNone_getStor_eq'` drops the unused hypothesis
entirely. Later In layers supply the `stateGas = none` fact from their fork
domain (`HistFork.stateGas_none`, `BodyStageCapabilities.stateGas_none`).
-/

namespace Blanc

open Jaune

/-- `stateGas = none` twin of `Xinst.targetBalanceMono_of_none`: every
successful no-interpreter executable instruction outside `ca` cannot lower
`ca`'s balance. -/
theorem Xinst.targetBalanceMono_of_none_noStateGas
    {ca : Adr} {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : Xinst.Run sevm pre x .none (.ok post))
    (target_ne : sevm.currentTarget ≠ ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256) :
    (pre.state.bal ca).toNat ≤ (post.state.bal ca).toNat := by
  unfold Xinst.Run at run
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with
    ⟨ex, step_eq, frame⟩ |
    ⟨d, endowment, newAddress, mi, ms, framePrefix, step_eq⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, inputSize, oi, outputSize, code, delegated, framePrefix, _, callerShape,
      _, step_eq⟩ <;>
    rw [step_eq] at run
  · obtain ⟨-, rfl⟩ := run
    exact Nat.le_of_eq
      (congrArg (fun state : State => (state.bal ca).toNat) frame.state)
  · have sumD : sum d.state.bal < 2 ^ 256 := by
      rw [← framePrefix.state]
      exact sum_nof
    have mono := GenericCreate.targetBalanceMono_of_none
      run target_ne sumD
    rw [framePrefix.state]
    exact mono
  · have sumD : sum d.state.bal < 2 ^ 256 := by
      rw [← framePrefix.state]
      exact sum_nof
    have callerNe : stv = true → caller ≠ ca := by
      intro transfer
      rcases callerShape with ⟨_, caller_eq⟩ | ⟨no_transfer, _⟩
      · rw [caller_eq]
        exact target_ne
      · rw [transfer] at no_transfer
        contradiction
    have mono := GenericCall.targetBalanceMono_of_none
      run callerNe sumD
    rw [framePrefix.state]
    exact mono

/-- `stateGas = none` twin of `Ninst.targetBalanceMono_of_none`: every
successful nonrecursive instruction in a foreign frame cannot lower the
observed account's balance. -/
theorem Ninst.targetBalanceMono_of_none_noStateGas
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : Ninst.StepRun pc sevm pre n .none (.ok post))
    (target_ne : sevm.currentTarget ≠ ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256) :
    (pre.state.bal ca).toNat ≤ (post.state.bal ca).toNat := by
  cases n with
  | reg regular =>
      have regularRun : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post :=
        ((Step.run_ofExecution (xl := (.none : Xlot))).mp run).2.symm
      exact Nat.le_of_eq (congrArg B256.toNat
        (congrFun (Rinst.preserves_bal regularRun) ca))
  | exec executable =>
      simp only [Ninst.StepRun, Ninst.step_exec] at run
      exact Xinst.targetBalanceMono_of_none_noStateGas hsg
        (XStep.run_toStep.mp run) target_ne sum_nof
  | push bytes bound =>
      have frame := Ninst.push_instructionFrame_effectRec
        (hxs := bound) (xl := .none) trivial run
      exact Nat.le_of_eq
        (congrArg (fun state : State => (state.bal ca).toNat) frame.state)
  | dupn imm =>
      have frame := Ninst.dupn_instructionFrame_effectRec
        (xl := .none) trivial run
      exact Nat.le_of_eq
        (congrArg (fun state : State => (state.bal ca).toNat) frame.state)
  | swapn imm =>
      have frame := Ninst.swapn_instructionFrame_effectRec
        (xl := .none) trivial run
      exact Nat.le_of_eq
        (congrArg (fun state : State => (state.bal ca).toNat) frame.state)
  | exchange imm =>
      have frame := Ninst.exchange_instructionFrame_effectRec
        (xl := .none) trivial run
      exact Nat.le_of_eq
        (congrArg (fun state : State => (state.bal ca).toNat) frame.state)

/-- Fork-free twin of `Ninst.foreignNone_getStor_eq`: the modern fork
hypothesis is unused, so the historical form drops it entirely. -/
theorem Ninst.foreignNone_getStor_eq'
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (run : Ninst.StepRun pc sevm pre n .none (.ok post))
    (target_ne : sevm.currentTarget ≠ ca)
    (hp : State.Protected pre.state ca) :
    Devm.getStor post ca = Devm.getStor pre ca := by
  cases n with
  | reg regular =>
      have regularRun : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post :=
        ((Step.run_ofExecution (xl := (.none : Xlot))).mp run).2.symm
      by_cases store : regular = .sstore
      · subst regular
        exact sstore_preserves_getStor_ne regularRun target_ne
      · exact (congrFun (Rinst.preserves_stor store regularRun) ca).symm
  | exec executable =>
      simp only [Ninst.StepRun, Ninst.step_exec] at run
      exact Xinst.none_getStor_eq (XStep.run_toStep.mp run) ca hp
  | push bytes bound =>
      have frame := Ninst.push_instructionFrame_effectRec
        (hxs := bound) (xl := .none) trivial run
      exact (frame.getStor ca).symm
  | dupn imm =>
      have frame := Ninst.dupn_instructionFrame_effectRec
        (xl := .none) trivial run
      exact (frame.getStor ca).symm
  | swapn imm =>
      have frame := Ninst.swapn_instructionFrame_effectRec
        (xl := .none) trivial run
      exact (frame.getStor ca).symm
  | exchange imm =>
      have frame := Ninst.exchange_instructionFrame_effectRec
        (xl := .none) trivial run
      exact (frame.getStor ca).symm

namespace ExecutionAccountingReplay

namespace SettlementCarrier

variable {ca : Adr}

/-- `stateGas = none` twin of `SettlementCarrier.xinstForeignSome_observed`:
recursive accounting transport for one actual filled executable slot in a
foreign frame, observed. The slot contributes its child's observation exactly
when the spawned frame settles. -/
theorem xinstForeignSome_observed_noStateGas (C : SettlementCarrier ca)
    {O : Type} (obs : List C.Step → List O) (obs_nil : obs [] = [])
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    {cevm : Evm} {raw : Execution} {settled : Devm}
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (frameRun : RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled))
    (resumeRun : resume.run (.ok settled) = .ok post)
    (target_ne : sevm.currentTarget ≠ ca)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (protection : ∀ owner, C.storageOwners owner → State.Protected pre.state owner)
    (sum_nof : sum pre.state.bal < 2 ^ 256)
    {child : List O}
    (body : ∀ committed : Execution.commits raw = true, ∃ steps,
      C.Replay (C.frameEntry cevm.sta cevm.dyna.state) steps
        (C.ofState (Execution.committedPost raw committed).state) ∧
      obs steps = child) :
    ∃ steps,
      C.Replay (C.ofState pre.state) steps (C.ofState post.state) ∧
      obs steps = if Frame.settlementCommits frame raw = true
        then child else [] := by
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with
    ⟨execution, shape, hprefix⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, callShape, _,
      shape⟩ <;> rw [shape] at spawn
  · cases spawn
  · rcases genericCreate_step_spawn_exact spawn with ⟨rfl, rfl⟩
    let createPre :=
      addAccessedAddress
        (((d.withGasLeft
            (d.gasLeft - except64th d.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress
    let msg := createMsg sevm createPre (except64th d.gasLeft)
      endowment newAddress ((d.memory.read mi ms).1)
    have process : ProcessCreateMessage msg (.some ⟨cevm, raw⟩)
        (.ok settled) := by
      simpa only [ProcessCreateMessage, msg, createPre] using frameRun
    have dSum : sum d.state.bal < 2 ^ 256 := by
      rw [← hprefix.state]
      exact sum_nof
    have preparedStor : createPre.state.getStor = d.state.getStor := by
      simpa only [createPre] using
        genericCreate_prepared_getStor sevm d newAddress
          (UInt64.add_one_ne_zero_of_ne_max
            (genericCreate_step_spawn_nonce_ne_max spawn))
    have preparedBalance : createPre.state.bal = d.state.bal := by
      simpa only [createPre] using genericCreate_prepared_bal sevm d newAddress
    have preparedSnapshot :
        C.ofState createPre.state = C.ofState d.state :=
      C.worldSilent (fun owner _ => congrFun preparedStor owner) preparedBalance
    have creatorNonce : (d.state.get sevm.currentTarget).nonce + 1 ≠ 0 :=
      UInt64.add_one_ne_zero_of_ne_max (genericCreate_step_spawn_nonce_ne_max spawn)
    have dProtected : ∀ owner, C.storageOwners owner → State.Protected d.state owner := by
      intro owner observed
      rw [← hprefix.state]
      exact protection owner observed
    have preparedProtected : ∀ owner, C.storageOwners owner →
        State.Protected createPre.state owner := by
      intro owner observed
      change State.Protected (d.state.incrNonce sevm.currentTarget) owner
      unfold State.Protected
      by_cases equal : sevm.currentTarget = owner
      · subst owner
        left
        simpa only [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce] using creatorNonce
      · rw [State.incrNonce, State.setAccount_get_ne _ equal]
        exact dProtected owner observed
    have targetAway : ∀ owner, C.storageOwners owner → msg.currentTarget ≠ owner := by
      intro owner observed equal
      have fresh := genericCreate_step_spawn_target_unprotected spawn
      apply fresh
      have targetEq : newAddress = owner := equal
      rw [targetEq]
      exact dProtected owner observed
    have entrySafe : EntryStorageSafe C.storageOwners msg := by
      intro owner observed _ _
      exact Or.inr (preparedProtected owner observed)
    have callerNe : msg.shouldTransferValue = true → msg.caller ≠ ca := by
      simpa only [msg, createMsg, ne_eq, forall_const] using target_ne
    have valueZero : msg.shouldTransferValue = false →
        msg.currentTarget = ca → msg.value = 0 := by
      simp only [msg, createMsg, Bool.true_eq_false, IsEmpty.forall_iff]
    have msgSum : sum msg.benv.state.bal < 2 ^ 256 := by
      change sum createPre.state.bal < 2 ^ 256
      rw [preparedBalance]
      exact dSum
    rcases C.processCreateMessage_of_body_observed obs obs_nil process callerNe
        valueZero targetAway entrySafe msgSum body with ⟨steps, replay, observed⟩
    have postState : post.state = settled.state :=
      Resume.create_state resumeRun
    refine ⟨steps, ?_, observed⟩
    rw [hprefix.state, ← preparedSnapshot, postState]
    exact replay
  · rcases genericCall_step_spawn_exact spawn with ⟨rfl, rfl⟩
    let msg := callMsg sevm (d.withReturnData []) gas value caller target
      codeAddress stv isStatic ((d.memory.read ii isz).1) code
      disablePrecompiles
    have process : ProcessMessage msg (.some ⟨cevm, raw⟩) (.ok settled) := by
      simpa only [ProcessMessage, msg] using frameRun
    have dSum : sum d.state.bal < 2 ^ 256 := by
      rw [← hprefix.state]
      exact sum_nof
    have callerNe : stv = true → caller ≠ ca := by
      intro transfer
      rcases callShape with ⟨_, caller_eq⟩ | ⟨noTransfer, _⟩
      · rw [caller_eq]
        exact target_ne
      · rw [transfer] at noTransfer
        contradiction
    have valueZero : stv = false → target = ca → value = 0 := by
      intro noTransfer target_eq
      rcases callShape with ⟨transfer, _⟩ | ⟨_, targetParent⟩
      · rw [noTransfer] at transfer
        contradiction
      · exact False.elim (target_ne (targetParent.symm.trans target_eq))
    have msgCallerNe :
        msg.shouldTransferValue = true → msg.caller ≠ ca := by
      simpa only [msg, callMsg, ne_eq] using callerNe
    have msgValueZero : msg.shouldTransferValue = false →
        msg.currentTarget = ca → msg.value = 0 := by
      simpa only [msg, callMsg] using valueZero
    have msgSum : sum msg.benv.state.bal < 2 ^ 256 := by
      change sum d.state.bal < 2 ^ 256
      exact dSum
    have entrySafe : EntryStorageSafe C.storageOwners msg := by
      intro owner observed _ _
      right
      change State.Protected d.state owner
      rw [← hprefix.state]
      exact protection owner observed
    rcases C.processMessage_of_body_observed obs obs_nil process msgCallerNe
        msgValueZero entrySafe msgSum body with ⟨steps, replay, observed⟩
    have postState : post.state = settled.state :=
      Resume.call_state resumeRun
    refine ⟨steps, ?_, observed⟩
    rw [hprefix.state, postState]
    exact replay

end SettlementCarrier

namespace ReplayCarrier

variable {ca : Adr}

/-- `stateGas = none` twin of `ReplayCarrier.xinstForeignSome_observed`, at an
account-local carrier. -/
theorem xinstForeignSome_observed_noStateGas (C : ReplayCarrier ca)
    (V : ReplayObservation C)
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    {cevm : Evm} {raw : Execution} {settled : Devm}
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (frameRun : RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled))
    (resumeRun : resume.run (.ok settled) = .ok post)
    (target_ne : sevm.currentTarget ≠ ca)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (protection : C.readsStorage = true → State.Protected pre.state ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (body : ∀ childCommitted : Execution.commits raw = true, ∃ steps,
      C.Replay (C.frameEntry cevm.sta cevm.dyna.state) steps
        (C.ofState (Execution.committedPost raw childCommitted).state) ∧
      V.obs steps = (Exec.committedFrames child).flatMap V.frameObs) :
    ∃ steps, C.Replay (C.ofState pre.state) steps (C.ofState post.state) ∧
      V.obs steps = (if Frame.settlementCommits frame raw = true
        then (Exec.committedFrames child).flatMap V.frameObs else []) :=
  C.toSettlementCarrier.xinstForeignSome_observed_noStateGas V.obs V.obs_nil spawn
    frameRun resumeRun target_ne hsg (fun owner observed => by
      rw [observed.1]
      exact protection observed.2) sum_nof body

end ReplayCarrier

end ExecutionAccountingReplay

end Blanc
