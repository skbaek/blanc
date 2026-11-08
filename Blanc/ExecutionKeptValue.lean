import Blanc.ExecutionKeptFacts
import Blanc.ExecutionKeptChain
import Blanc.LadderBase

open private resume_callAmsterdam_state from Blanc.LadderBase

/-!
# Kept-frame value: never falls, and covers the kept values (O37 sizing draft)

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

**Status.** Sizing draft written without Lean elaboration under the run's
no-elaboration constraint. Every `sorry` carries a `-- DRAFT:` comment giving
the leaf's route and an estimated line count from a comparable existing proof
that was actually read. The master compiles this file and clears them.

**What this is.** The neutral `Exec` fold O37 needs, over kept (settled) frames
only: nothing here names `rawNodes`, `rawFrames`, a gas amount, or a frame that
did not commit. `Exec.kept_bal_neverFalls` says the account's balance never
falls across one kept run; `Exec.kept_bal_ge_keptPaid` says it additionally
covers the values the kept frames carried in. Both induct over
`Exec.retained_induction` with the code premise threaded down by
`Blanc.Exec.Deriv.ParentStep.codePreserve` and the target premise
`sevm.currentTarget ≠ a` threaded unchanged, exactly as `Exec.keptAt_entry`
does. The target premise is load-bearing: a parent step at `a` running
arbitrary code can debit the account, so without it the statements are
unprovable as drafted. The at-code frame law is a premise, discharged per contract by
`frame_keeps_balances` (`Blanc/Lift/BuilderRequest/Surplus.lean`, W18, merged).
The foreign cases are the new work: balance twins of the storage twins in
`Blanc/ExecutionKeptFrames.lean`.

**Reuse.** `Exec.keptAt`, `Exec.retained_induction`, `Execution.committedPost`,
`Execution.commits`, `Devm.getBal`, `SumNof`, `KeptFork`,
`Blanc.Exec.Deriv.ParentStep.codePreserve`, `Evm.step_spawn_inv`,
`Xinst.step_spawn_form` are reused, not redefined. Nothing here is
contract-specific, so at the green boundary this module is a SHARED candidate
(`scripts/check-layering.py` registration plus a `docs/COMMON_API.md` entry are
left to the compiling run: this run edits no existing file).
-/

namespace Blanc

open Jaune ExecutionTrace

/-- The values the frames kept at `a` carried in, one per kept frame. -/
def Exec.keptPaid (a : Adr) {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : Nat :=
  ((Exec.keptAt a run).map fun f => f.sevm.value.toNat).sum

/-- A childless Amsterdam CALL-family instruction whose actual transfer caller
is distinct from `ca` cannot lower `ca`'s balance. -/
private theorem GenericCallAmsterdam.targetBalanceMono_of_none
    {ca : Adr} {sevm : Sevm} {state : StateGasRules} {pre : Devm} {gas reservoir : Nat}
    {value : B256} {caller target codeAddress : Adr} {stv istat : Bool}
    {ii is oi os : Nat} {code : ByteArray} {dp nac ib : Bool} {post : Devm}
    (run : GenericCallAmsterdam sevm state pre gas reservoir value caller target
      codeAddress stv istat ii is oi os code dp nac ib .none (.ok post))
    (caller_ne : stv = true → caller ≠ ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256) :
    (pre.state.bal ca).toNat ≤ (post.state.bal ca).toNat := by
  unfold GenericCallAmsterdam genericCallAmsterdam.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  · cases run.2
  · rename_i h_push
    apply Nat.le_of_eq
    rw [Except.ok.inj run.2, ← (Devm.push_of_push h_push).state]
    by_cases hnac : nac = true
    · rw [ite_eq_left hnac]
      rfl
    · rw [ite_eq_right hnac]
      rfl
  · obtain ⟨r, hframe, hres⟩ := run
    obtain ⟨childMsg, hframe, hc_state, hc_stv, hc_caller, hc_value, hc_ct,
        hc_ca⟩ :
        ∃ m : Msg, ProcessMessage m .none r ∧
          m.benv.state = pre.state ∧ m.shouldTransferValue = stv ∧
          m.caller = caller ∧ m.value = value ∧ m.currentTarget = target ∧
          m.codeAddress = some codeAddress :=
      ⟨_, hframe, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rcases r with err | child
    · unfold Resume.run liftToExecution at hres
      cases hres
    · have callerNe : childMsg.shouldTransferValue = true → childMsg.caller ≠ ca := by
        rw [hc_stv, hc_caller]
        exact caller_ne
      have sumSeed : sum childMsg.benv.state.bal < 2 ^ 256 := by
        rw [hc_state]
        exact sum_nof
      have childMono := ProcessMessage.targetBalanceMono_of_none
        hframe callerNe sumSeed
      have postState : post.state = child.state :=
        resume_callAmsterdam_state hres.symm
      rw [postState, ← hc_state]
      exact childMono

/-- A childless Amsterdam CREATE-family instruction cannot lower any account's
balance. Its direct exits only touch frame metadata, access lists, state gas,
and the creator nonce. -/
private theorem GenericCreateAmsterdam.targetBalanceMono_of_none
    {ca : Adr} {sevm : Sevm} {state : StateGasRules} {pre : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat} {post : Devm}
    (run : GenericCreateAmsterdam sevm state pre endowment newAddress mi ms
      .none (.ok post))
    (_sum_nof : sum pre.state.bal < 2 ^ 256) :
    (pre.state.bal ca).toNat ≤ (post.state.bal ca).toNat := by
  unfold GenericCreateAmsterdam genericCreateAmsterdam.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  all_goals try cases run.2
  · rename_i hpush
    apply Nat.le_of_eq
    have e1 : (pre.withReturnData []).getBal ca = pre.getBal ca := rfl
    have e2 : (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
        (pre.withReturnData [])).getBal ca = (pre.withReturnData []).getBal ca :=
      (Devm.balReadAccount_instructionFrame sevm.benvStat.rules
        sevm.currentTarget (pre.withReturnData [])).getBal ca
    have e3 : post.getBal ca = (Devm.balReadAccount sevm.benvStat.rules
        sevm.currentTarget (pre.withReturnData [])).getBal ca :=
      Devm.push_getBal_eq hpush ca
    exact congrArg B256.toNat (e3.trans (e2.trans e1)).symm
  · rename_i hpre hnew xcharge v hchg hcollision xpush hpush
    apply Nat.le_of_eq
    have e1 : (pre.withReturnData []).getBal ca = pre.getBal ca := rfl
    have e2 : (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
        (pre.withReturnData [])).getBal ca = (pre.withReturnData []).getBal ca :=
      (Devm.balReadAccount_instructionFrame sevm.benvStat.rules
        sevm.currentTarget (pre.withReturnData [])).getBal ca
    have e3 : (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
        sevm.currentTarget (pre.withReturnData [])) newAddress).getBal ca =
        (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
          (pre.withReturnData [])).getBal ca :=
      (addAccessedAddress_instructionFrame (Devm.balReadAccount
        sevm.benvStat.rules sevm.currentTarget (pre.withReturnData []))
        newAddress).getBal ca
    have e4 : (Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData [])) newAddress)).getBal ca =
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData [])) newAddress).getBal ca :=
      (Devm.balReadAccount_instructionFrame sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData [])) newAddress)).getBal ca
    have e5 : v.getBal ca = (Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData [])) newAddress)).getBal ca :=
      ((chargeStateGas_worldEq_of_ok hchg).getBal ca).symm
    have e6 : (v.withholdCreateGas.2.getBal ca) = v.getBal ca :=
      (Devm.withholdCreateGas_instructionFrame v).getBal ca
    have e7 : ((v.withholdCreateGas.2.incrNonce sevm.currentTarget).getBal ca) =
        (v.withholdCreateGas.2.getBal ca) :=
      congrFun State.incrNonce_bal ca
    have e8 : post.getBal ca =
        ((v.withholdCreateGas.2.incrNonce sevm.currentTarget).getBal ca) :=
      Devm.push_getBal_eq hpush ca
    exact congrArg B256.toNat
      (e8.trans (e7.trans (e6.trans (e5.trans (e4.trans (e3.trans (e2.trans e1))))))).symm
  · exfalso
    obtain ⟨r, hframe, hres⟩ := run
    obtain ⟨childMsg, hframe, hc_ca⟩ :
        ∃ m : Msg, ProcessCreateMessage m .none r ∧ m.codeAddress = .none :=
      ⟨_, hframe, rfl⟩
    obtain ⟨r1, hpm, hset⟩ := ProcessCreateMessage.iff_processMessage.mp hframe
    obtain ⟨r0, hbody, hset1⟩ := ProcessMessage.iff_body.mp hpm
    unfold FrameBody at hbody
    rcases eq_bt : (processCreateMessage.msg childMsg).benvAfterTransfer with
      e | benv <;> rw [eq_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset1
      rw [hset1, processCreateMessage.settle_error] at hset
      rw [hset] at hres
      unfold Resume.run liftToExecution at hres
      cases hres
    · have hca :
          ((processCreateMessage.msg childMsg).withBenv benv).codeAddress =
            .none := hc_ca
      obtain ⟨exn, h_xl, -⟩ := of_executeCode_noneCode hca hbody
      cases h_xl
  · rename_i _ _ _ _ hpush
    apply Nat.le_of_eq
    have e1 : (pre.withReturnData []).getBal ca = pre.getBal ca := rfl
    have e2 : (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
        (pre.withReturnData [])).getBal ca = (pre.withReturnData []).getBal ca :=
      (Devm.balReadAccount_instructionFrame sevm.benvStat.rules
        sevm.currentTarget (pre.withReturnData [])).getBal ca
    have e3 : (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
        sevm.currentTarget (pre.withReturnData [])) newAddress).getBal ca =
        (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
          (pre.withReturnData [])).getBal ca :=
      (addAccessedAddress_instructionFrame (Devm.balReadAccount
        sevm.benvStat.rules sevm.currentTarget (pre.withReturnData []))
        newAddress).getBal ca
    have e4 : (Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData [])) newAddress)).getBal ca =
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData [])) newAddress).getBal ca :=
      (Devm.balReadAccount_instructionFrame sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData [])) newAddress)).getBal ca
    have e6 : ((Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData [])) newAddress)).withholdCreateGas.2.getBal
        ca) = (Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData [])) newAddress)).getBal ca :=
      (Devm.withholdCreateGas_instructionFrame _).getBal ca
    have e7 : (((Devm.balReadAccount sevm.benvStat.rules newAddress
        (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
          sevm.currentTarget (pre.withReturnData []))
          newAddress)).withholdCreateGas.2.incrNonce
        sevm.currentTarget).getBal ca) =
        ((Devm.balReadAccount sevm.benvStat.rules newAddress
          (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
            sevm.currentTarget (pre.withReturnData []))
            newAddress)).withholdCreateGas.2.getBal ca) :=
      congrFun State.incrNonce_bal ca
    have e8 : post.getBal ca =
        (((Devm.balReadAccount sevm.benvStat.rules newAddress
          (addAccessedAddress (Devm.balReadAccount sevm.benvStat.rules
            sevm.currentTarget (pre.withReturnData []))
            newAddress)).withholdCreateGas.2.incrNonce
          sevm.currentTarget).getBal ca) :=
      Devm.push_getBal_eq hpush ca
    exact congrArg B256.toNat
      (e8.trans (e7.trans (e6.trans (e4.trans (e3.trans (e2.trans e1)))))).symm
  · exfalso
    obtain ⟨r, hframe, hres⟩ := run
    obtain ⟨childMsg, hframe, hc_ca⟩ :
        ∃ m : Msg, ProcessCreateMessage m .none r ∧ m.codeAddress = .none :=
      ⟨_, hframe, rfl⟩
    obtain ⟨r1, hpm, hset⟩ := ProcessCreateMessage.iff_processMessage.mp hframe
    obtain ⟨r0, hbody, hset1⟩ := ProcessMessage.iff_body.mp hpm
    unfold FrameBody at hbody
    rcases eq_bt : (processCreateMessage.msg childMsg).benvAfterTransfer with
      e | benv <;> rw [eq_bt] at hbody
    · rw [hbody.2, processMessage.settle_error] at hset1
      rw [hset1, processCreateMessage.settle_error] at hset
      rw [hset] at hres
      unfold Resume.run liftToExecution at hres
      cases hres
    · have hca :
          ((processCreateMessage.msg childMsg).withBenv benv).codeAddress =
            .none := hc_ca
      obtain ⟨exn, h_xl, -⟩ := of_executeCode_noneCode hca hbody
      cases h_xl

/-- Neutral per-account balance monotonicity for childless executable
instructions: no fork premise, at the cost of the two Amsterdam twins above. -/
private theorem Xinst.foreignNone_getBal_mono
    {ca : Adr} {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (run : Xinst.Run sevm pre x .none (.ok post))
    (target_ne : sevm.currentTarget ≠ ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256) :
    (pre.state.bal ca).toNat ≤ (post.state.bal ca).toNat := by
  unfold Xinst.Run at run
  rcases Xinst.step_shape sevm pre x with
    ⟨ex, hs, hframe⟩ |
    ⟨d, endowment, newAddress, mi, ms, framePrefix, hs⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, delegated, framePrefix, _, callerShape,
      _, hs⟩ |
    ⟨d, state, endowment, newAddress, mi, ms, hprefix, hs⟩ |
    ⟨d, d₀, state, gas, reservoir, value, caller, target, codeAddress, stv,
      isStatic, ii, isz, oi, osz, code, dp, nac, ib, hprefix, _, callShape,
      _, hs⟩ <;>
    rw [hs] at run
  · obtain ⟨-, rfl⟩ := run
    exact Nat.le_of_eq
      (congrArg (fun state : State => (state.bal ca).toNat) hframe.state)
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
  · have sumD : sum d.state.bal < 2 ^ 256 := by
      rw [← hprefix.state]
      exact sum_nof
    have mono := GenericCreateAmsterdam.targetBalanceMono_of_none (ca := ca)
      run sumD
    rw [hprefix.state]
    exact mono
  · have sumD : sum d.state.bal < 2 ^ 256 := by
      rw [← hprefix.state]
      exact sum_nof
    have callerNe : stv = true → caller ≠ ca := by
      intro transfer
      rcases callShape with ⟨_, caller_eq⟩ | ⟨no_transfer, _⟩
      · rw [caller_eq]
        exact target_ne
      · rw [transfer] at no_transfer
        contradiction
    have mono := GenericCallAmsterdam.targetBalanceMono_of_none
      run callerNe sumD
    rw [hprefix.state]
    exact mono

/-- Neutral per-account balance monotonicity for childless nonrecursive
instructions: the foreign-call balance twin. -/
private theorem Ninst.foreignNone_getBal_mono
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
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
      exact Xinst.foreignNone_getBal_mono
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

/-- A step that continues the frame, in a frame not at the account, cannot
lower its balance. -/
private theorem Evm.step_cont_getBal_foreign {pc pc' : Nat} {sevm : Sevm}
    {pre post : Devm} {a : Adr}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    (target : sevm.currentTarget ≠ a)
    (sum_nof : sum pre.state.bal < 2 ^ 256) :
    (pre.state.bal a).toNat ≤ (post.state.bal a).toNat := by
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none =>
      unfold Evm.step at step
      rw [decoded] at step
      cases step
  | some instruction =>
      cases instruction with
      | last last =>
          rw [Evm.step_last decoded] at step
          cases step
      | jump jumpInst =>
          rw [Evm.step_jump decoded] at step
          cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
          | error error =>
              rw [jumpEq] at step
              cases step
          | ok pair =>
              rcases pair with ⟨actualPc, actualPost⟩
              rw [jumpEq] at step
              cases step
              have frame := Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ jumpInst
              rw [jumpEq] at frame
              exact Nat.le_of_eq
                (congrArg B256.toNat (Devm.InstructionFrame.getBal frame a))
      | next instruction =>
          have nstep : Ninst.step ⟨pc, sevm, pre⟩ instruction = .cont pc' post := by
            rw [← Evm.step_next decoded]
            exact step
          have pcEq : pc' = pc + instruction.size := Ninst.step_cont_pc nstep
          subst pc'
          have nrun : Ninst.StepRun pc sevm pre instruction .none (.ok post) := by
            unfold Ninst.StepRun
            rw [nstep]
            exact ⟨rfl, rfl⟩
          exact Ninst.foreignNone_getBal_mono nrun target sum_nof

/-! ## The world across a spawn, for the balance -/

/-- An Amsterdam CREATE spawn transfers its endowment from the parent's target. -/
private theorem genericCreateAmsterdam_step_spawn_transfer
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat} {frame : Frame} {resume : Resume}
    (spawn : genericCreateAmsterdam.step sevm state devm endowment newAddress mi ms =
      .spawn frame resume) :
    frame.inner.shouldTransferValue = true := by
  simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at spawn
  all_goals obtain ⟨rfl, -⟩ := spawn
  all_goals rfl

/-- A spawned frame's two messages open on the parent's balances, and its value moves only
from the parent's target, or nothing moves and the child stays at the parent's target. For
every rule record. -/
private theorem Xinst.step_spawn_bal_neutral {sevm : Sevm} {pre : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume} (spawn : Xinst.step sevm pre x = .spawn frame resume) :
    frame.outer.benv.state.bal = pre.state.bal ∧ frame.inner.benv.state.bal = pre.state.bal ∧
      ((frame.inner.shouldTransferValue = true ∧ frame.inner.caller = sevm.currentTarget) ∨
        (frame.inner.shouldTransferValue = false ∧
          frame.inner.currentTarget = sevm.currentTarget)) := by
  rcases Xinst.step_shape sevm pre x with ⟨ex, shape, -⟩ |
      ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
      ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
        ii, isz, oi, osz, code, delegated, hprefix, -, callerShape, -, shape⟩ |
      ⟨d, state, endowment, newAddress, mi, ms, hprefix, shape⟩ |
      ⟨d, d₀, state, gas, reservoir, value, caller, target, codeAddress,
        stv, isSt, ii, isz, oi, osz, code, dp, nac, ib, hprefix, -, callShape, -, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · obtain ⟨rfl, -⟩ := genericCreate_step_spawn_exact spawn
    have outer : (addAccessedAddress (((d.withGasLeft (d.gasLeft - except64th d.gasLeft)).withReturnData
        []).incrNonce sevm.currentTarget) newAddress).state.bal = pre.state.bal := by
      rw [addAccessedAddress_state]
      show (((d.withGasLeft (d.gasLeft - except64th d.gasLeft)).withReturnData []).state.incrNonce
        sevm.currentTarget).bal = _
      rw [State.incrNonce_bal]
      exact congrArg Jaune.State.bal hprefix.state.symm
    refine ⟨outer, ?_, .inl ⟨rfl, rfl⟩⟩
    rw [Frame.ofCreate, processCreateMessage_msg_bal_eq]
    exact outer
  · obtain ⟨rfl, -⟩ := genericCall_step_spawn_exact spawn
    exact ⟨congrArg Jaune.State.bal hprefix.state.symm, congrArg Jaune.State.bal hprefix.state.symm,
      callerShape⟩
  · obtain ⟨m, parent, nacr, hframe, -, hstate, -, -⟩ := genericCreateAmsterdam_step_spawn_form spawn
    have transfer := genericCreateAmsterdam_step_spawn_transfer spawn
    have caller := genericCreateAmsterdam_step_spawn_caller spawn
    subst hframe
    have outer : m.benv.state.bal = pre.state.bal := by
      rw [hstate, State.incrNonce_bal]
      exact congrArg Jaune.State.bal hprefix.state.symm
    refine ⟨outer, ?_, .inl ⟨transfer, caller⟩⟩
    rw [Frame.ofCreate, processCreateMessage_msg_bal_eq]
    exact outer
  · obtain ⟨rfl, -⟩ := genericCallAmsterdam_step_spawn_exact spawn
    exact ⟨congrArg Jaune.State.bal hprefix.state.symm, congrArg Jaune.State.bal hprefix.state.symm,
      callShape⟩

/-- **Entry credit.** A child spawned by a frame not at `a` opens with `a`'s balance plus
the child's value when the child runs at `a`, and with `a`'s balance unchanged otherwise. -/
private theorem Evm.step_spawn_enter_bal {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume} {child : Evm} {a : Adr}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc') (enter : frame.enter = .run child)
    (target : sevm.currentTarget ≠ a) (sum_nof : sum pre.state.bal < 2 ^ 256) :
    (child.dyna.state.bal a).toNat = (pre.state.bal a).toNat +
      if child.sta.currentTarget = a then child.sta.value.toNat else 0 := by
  obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨-, inner, shape⟩ := Xinst.step_spawn_bal_neutral spawn
  obtain ⟨benv, transfer, rfl⟩ := Frame.enter_run_inv enter
  change (benv.state.bal a).toNat = (pre.state.bal a).toNat +
    if frame.inner.currentTarget = a then frame.inner.value.toNat else 0
  have sumInner : sum frame.inner.benv.state.bal < 2 ^ 256 := by
    rw [inner]
    exact sum_nof
  rw [← inner]
  by_cases tr : frame.inner.shouldTransferValue = true ∧ frame.inner.value ≠ 0
  · obtain ⟨debit, sub, rfl⟩ := of_benvAfterTransfer tr.1 tr.2 transfer
    have callerNe : frame.inner.caller ≠ a := by
      rcases shape with ⟨-, caller_eq⟩ | ⟨no_transfer, -⟩
      · rw [caller_eq]
        exact target
      · rw [tr.1] at no_transfer
        cases no_transfer
    by_cases here : frame.inner.currentTarget = a
    · subst a
      rw [ite_eq_left rfl]
      exact of_transfer_bal_target sub callerNe sumInner
    · rw [ite_eq_right here, Nat.add_zero]
      exact congrArg B256.toNat (of_transfer_bal_other sub callerNe here)
  · have entry_eq := benvAfterTransfer_eq_of_not_transfer tr transfer
    subst entry_eq
    by_cases here : frame.inner.currentTarget = a
    · rw [ite_eq_left here]
      have zero : frame.inner.value.toNat = 0 := by
        rcases shape with ⟨transfers, -⟩ | ⟨-, target_eq⟩
        · have value_eq : frame.inner.value = 0 := by
            by_contra nonzero
            exact tr ⟨transfers, nonzero⟩
          rw [value_eq]
          rfl
        · exact absurd (target_eq.symm.trans here) target
      rw [zero, Nat.add_zero]
    · rw [ite_eq_right here, Nat.add_zero]

/-- A spawned child opens on no more balance in total than its parent had. -/
private theorem Evm.step_spawn_enter_balSum {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume} {child : Evm}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc') (enter : frame.enter = .run child) :
    sum child.dyna.state.bal ≤ sum pre.state.bal := by
  obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨-, inner, -⟩ := Xinst.step_spawn_bal_neutral spawn
  obtain ⟨benv, transfer, rfl⟩ := Frame.enter_run_inv enter
  have h := Msg.benvAfterTransfer_balance_effect (out := .ok benv) transfer
  change State.balSum benv.state ≤ State.balSum frame.inner.benv.state at h
  change sum benv.state.bal ≤ _
  rw [← inner]
  exact h

/-- A child whose settlement commits hands its balances to the parent. -/
private theorem Evm.step_spawn_settled_getBal {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {child : Evm} {raw : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc') (enter : frame.enter = .run child)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (settles : Frame.settlementCommits frame raw = true) :
    post.state.bal =
      (Execution.committedPost raw (Frame.raw_commits_of_settlementCommits settles)).state.bal := by
  obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨shape, hstate, -⟩ := Xinst.step_spawn_form spawn
  have committed := Frame.raw_commits_of_settlementCommits settles
  cases settledEq : frame.settle raw with
  | error e =>
      simp only [Frame.settlementCommits, settledEq, Bool.false_eq_true] at settles
  | ok s =>
      rw [settledEq] at resumed
      have clean : s.error.isSome = false := by
        unfold Frame.settlementCommits at settles
        rw [settledEq] at settles
        cases h : s.error <;> simp_all only [Option.isSome_none, Option.isNone_some, Bool.false_eq_true]
      have sState := hstate _ _ resumed
      have process : RunFrame frame (.some ⟨child, raw⟩) (.ok s) := by
        have := RunFrame.of_run (raw := raw) enter
        rwa [settledEq] at this
      rcases shape with ⟨m, rfl, -⟩ | ⟨m, rfl, -, -⟩
      · have := ProcessMessage.ok_state_eq_committedPost (msg := m) (pc := child.pc) (sevm := child.sta)
          (pre := child.dyna) process committed
        exact congrArg Jaune.State.bal (sState.trans this)
      · obtain ⟨inner, innerProcess, -, code, stateEq⟩ :=
          ProcessCreateMessage.ok_setCode_state_of_clean process clean
        have := ProcessMessage.ok_state_eq_committedPost (pc := child.pc) (sevm := child.sta)
          (pre := child.dyna) innerProcess committed
        rw [sState, stateEq, State.setCode_bal, this]

/-- A child whose settlement does not commit leaves the parent's balances, whatever its
subtree did. -/
private theorem Evm.step_spawn_rolled_getBal {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {child : Evm} {raw : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc') (enter : frame.enter = .run child)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (rolled : ¬ Frame.settlementCommits frame raw = true) : post.state.bal = pre.state.bal := by
  obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨shape, hstate, herr⟩ := Xinst.step_spawn_form spawn
  have opens := (Xinst.step_spawn_bal_neutral spawn).1
  cases settledEq : frame.settle raw with
  | error e =>
      rw [settledEq] at resumed
      exact (herr _ _ resumed).elim
  | ok s =>
      rw [settledEq] at resumed
      have dirty : s.error.isSome = true := by
        unfold Frame.settlementCommits at rolled
        rw [settledEq] at rolled
        cases h : s.error <;> simp_all only [Option.isNone_none, not_true_eq_false, Option.isSome_some]
      have sState := hstate _ _ resumed
      have process : RunFrame frame (.some ⟨child, raw⟩) (.ok s) := by
        have := RunFrame.of_run (raw := raw) enter
        rwa [settledEq] at this
      rcases shape with ⟨m, rfl, -⟩ | ⟨m, rfl, -, -⟩
      · have back := (ProcessMessage.rollback_of_error (msg := m) process dirty).1
        rw [sState, back]
        exact opens
      · have back := ProcessCreateMessage.rollback_of_error (msg := m) process dirty
        rw [sState, back]
        exact opens

/-- A world with no more balance in total than a bounded one is bounded. -/
private theorem SumNof.of_le {f g : Adr → B256} (h : sum f ≤ sum g) (bounded : SumNof g) :
    SumNof f := by
  unfold SumNof at bounded ⊢
  exact Nat.lt_of_le_of_lt h bounded

/-! ## The fold -/

/-- **Covers the kept values across one kept run.** At an account holding nondelegating code
`C`, from a world whose balances sum below `2 ^ 256`, and with the at-code frame law, a committed
run of a frame not at the account leaves the account with at least its balance plus every kept
frame's carried value. Each frame entering the account is credited its value by a caller other
than the account: a value-moving spawn's caller is its parent's target, never the account. -/
theorem Exec.kept_bal_ge_keptPaid {C : ByteArray} {a : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) (target : sevm.currentTarget ≠ a)
    (code : pre.getCode a = C)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (sums : SumNof pre.state.bal)
    (at_code : ∀ {s : Sevm} {d e : Devm}, s.currentTarget = a →
      s.code = C → Exec 0 s d (.ok e) → (e.getBal a).toNat = (d.getBal a).toNat) :
    (pre.getBal a).toNat + Exec.keptPaid a run ≤
      ((Execution.committedPost out committed).getBal a).toNat := by
  refine Exec.retained_induction
    (P := fun _ sevm pre out run => sevm.currentTarget ≠ a → pre.getCode a = C →
      SumNof pre.state.bal → ∀ (committed : Execution.commits out = true),
        (pre.getBal a).toNat + Exec.keptPaid a run ≤
          ((Execution.committedPost out committed).getBal a).toNat)
    ?_ ?_ ?_ ?_ ?_ run committed target code sums committed
  · intro pc sevm pre out step target code sum_pre committed
    revert committed
    cases out with
    | error err =>
        intro committed
        simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post =>
        intro committed
        have hpaid : Exec.keptPaid a (Exec.halt step) = 0 := by
          simp only [Exec.keptPaid, Exec.keptAt, List.map_nil, List.sum_nil]
        rw [hpaid, Nat.add_zero]
        cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
        | none =>
            unfold Evm.step at step
            rw [decoded] at step
            cases step
        | some instruction =>
            cases instruction with
            | last last =>
                rw [Evm.step_last decoded] at step
                have run : Linst.Run sevm pre last (.ok post) :=
                  Step.halt.inj step
                exact Linst.targetBalanceMono_of_foreign run target sum_pre
            | next next =>
                rw [Evm.step_next decoded] at step
                exact (Ninst.step_ne_halt_ok step).elim
            | jump jumpInst =>
                rw [Evm.step_jump decoded] at step
                cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
                | error error =>
                    rw [jumpEq] at step
                    cases step
                | ok result =>
                    rw [jumpEq] at step
                    cases step
  · intro pc sevm pre pc' post out step next ih target code sum_pre committed
    have edge := Exec.Deriv.ParentStep.cont step next
    have hmono : (pre.state.bal a).toNat ≤ (post.state.bal a).toNat :=
      Evm.step_cont_getBal_foreign step target sum_pre
    have hnext := Blanc.Exec.Deriv.ParentStep.codePreserve edge a (by rw [code]; exact nonempty)
    have hle_sum := Blanc.Exec.Deriv.ParentStep.balSum_le edge
    dsimp only at hle_sum
    have hsum : SumNof post.state.bal := SumNof.of_le hle_sum sum_pre
    have hpaid : Exec.keptPaid a (Exec.cont step next) = Exec.keptPaid a next := by
      simp only [Exec.keptPaid, Exec.keptAt]
    have hle := ih target (by rw [hnext]; exact code) hsum committed
    rw [hpaid]
    exact Nat.le_trans (Nat.add_le_add_right hmono _) hle
  · intro pc sevm pre frame resume pc' result post out step enter resumed next ih target code sum_pre
      committed
    have edge := Exec.Deriv.ParentStep.doneOk step enter resumed next
    obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
    have runX : Xinst.Run sevm pre x .none (.ok post) := by
      unfold Xinst.Run
      rw [spawn]
      exact ⟨result, RunFrame.of_done enter, resumed.symm⟩
    have hmono : (pre.state.bal a).toNat ≤ (post.state.bal a).toNat :=
      Xinst.foreignNone_getBal_mono runX target sum_pre
    have hnext := Blanc.Exec.Deriv.ParentStep.codePreserve edge a (by rw [code]; exact nonempty)
    have hle_sum := Blanc.Exec.Deriv.ParentStep.balSum_le edge
    dsimp only at hle_sum
    have hsum : SumNof post.state.bal := SumNof.of_le hle_sum sum_pre
    have hpaid : Exec.keptPaid a (Exec.doneOk step enter resumed next) =
        Exec.keptPaid a next := by
      simp only [Exec.keptPaid, Exec.keptAt]
    have hle := ih target (by rw [hnext]; exact code) hsum committed
    rw [hpaid]
    exact Nat.le_trans (Nat.add_le_add_right hmono _) hle
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next settles
      childIH nextIH target code sum_pre committed
    have edge := Exec.Deriv.ParentStep.runOk step enter child resumed next
    have hnext := Blanc.Exec.Deriv.ParentStep.codePreserve edge a (by rw [code]; exact nonempty)
    have hle_sum := Blanc.Exec.Deriv.ParentStep.balSum_le edge
    dsimp only at hle_sum
    have hsum : SumNof post.state.bal := SumNof.of_le hle_sum sum_pre
    have tail := nextIH target (by rw [hnext]; exact code) hsum committed
    have entry := Evm.step_spawn_enter_bal step enter target sum_pre
    have handed := congrFun (Evm.step_spawn_settled_getBal step enter resumed settles) a
    have childCommits := Frame.raw_commits_of_settlementCommits settles
    obtain ⟨pcZero, childCode, source⟩ := Evm.step_spawn_child step enter
    by_cases here : childEvm.sta.currentTarget = a
    · have hpaid : Exec.keptPaid a (Exec.runOk step enter child resumed next) =
          childEvm.sta.value.toNat + Exec.keptPaid a next := by
        unfold Exec.keptPaid
        rw [Exec.keptAt, dite_eq_left settles, ite_eq_left here, List.map_append, List.sum_append,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        rfl
      rw [ite_eq_left here] at entry
      have childRuns : childEvm.sta.code = C := by
        have equal := source (by rw [here]; exact target)
          (by rw [here, code]; intro empty; subst empty; exact nonempty ByteArray.toList_empty)
          (by rw [here, code]; exact nondelegating)
        rw [equal, here, code]
      cases raw with
      | error e => simp only [Execution.commits, Bool.false_eq_true] at childCommits
      | ok e =>
          have child0 : Exec 0 childEvm.sta childEvm.dyna (.ok e) := pcZero ▸ child
          have law := at_code here childRuns child0
          have postBal : (post.getBal a).toNat = (pre.getBal a).toNat + childEvm.sta.value.toNat := by
            change (post.state.bal a).toNat = _
            rw [handed]
            change (e.getBal a).toNat = _
            rw [law]
            exact entry
          rw [hpaid]
          omega
    · have hpaid : Exec.keptPaid a (Exec.runOk step enter child resumed next) =
          Exec.keptPaid a child + Exec.keptPaid a next := by
        unfold Exec.keptPaid
        rw [Exec.keptAt, dite_eq_left settles, ite_eq_right here, List.map_append, List.sum_append]
      rw [ite_eq_right here, Nat.add_zero] at entry
      have childSum : SumNof childEvm.dyna.state.bal :=
        SumNof.of_le (Evm.step_spawn_enter_balSum step enter) sum_pre
      have below := childIH here ((childCode a).trans code) childSum childCommits
      have postBal : (post.getBal a).toNat =
          ((Execution.committedPost raw childCommits).getBal a).toNat := by
        change (post.state.bal a).toNat = _
        rw [handed]
        rfl
      have startBal : (childEvm.dyna.getBal a).toNat = (pre.getBal a).toNat := entry
      rw [hpaid]
      omega
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next rolled
      nextIH target code sum_pre committed
    have edge := Exec.Deriv.ParentStep.runOk step enter child resumed next
    have hnext := Blanc.Exec.Deriv.ParentStep.codePreserve edge a (by rw [code]; exact nonempty)
    have back := Evm.step_spawn_rolled_getBal step enter resumed rolled
    have hsum : SumNof post.state.bal := by
      unfold SumNof
      rw [back]
      exact sum_pre
    have hpaid : Exec.keptPaid a (Exec.runOk step enter child resumed next) =
        Exec.keptPaid a next := by
      unfold Exec.keptPaid
      rw [Exec.keptAt, dite_eq_right rolled, List.nil_append]
    have tail := nextIH target (by rw [hnext]; exact code) hsum committed
    have same : post.getBal a = pre.getBal a := congrFun back a
    rw [hpaid, ← same]
    exact tail

/-- **Never falls across one kept run.** Under the premises of `Exec.kept_bal_ge_keptPaid`, a
committed run of a frame not at the account leaves the account no poorer. -/
theorem Exec.kept_bal_neverFalls {C : ByteArray} {a : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) (target : sevm.currentTarget ≠ a)
    (code : pre.getCode a = C)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (sums : SumNof pre.state.bal)
    (at_code : ∀ {s : Sevm} {d e : Devm}, s.currentTarget = a →
      s.code = C → Exec 0 s d (.ok e) → (e.getBal a).toNat = (d.getBal a).toNat) :
    (pre.getBal a).toNat ≤ ((Execution.committedPost out committed).getBal a).toNat :=
  Nat.le_trans (Nat.le_add_right _ _)
    (Exec.kept_bal_ge_keptPaid run committed target code nonempty nondelegating sums at_code)

end Blanc
