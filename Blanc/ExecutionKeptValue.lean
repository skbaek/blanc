import Blanc.ExecutionKeptFacts
import Blanc.ExecutionKeptChain
import Blanc.LadderBase

open private resume_callAmsterdam_state from Blanc.LadderBase
open private TopRun TopRun.shape TopRun.prepared TopRun.frame TopRun.entered TopRun.settled TopRun.state_eq
  TopRun.top TopRun.commits_eq TopRun.create_ne TopRun.entry_getCode message_top settle_ofCall_committed
  settle_error_rollback settle_inner_clean precomp_post Prepared.caller Prepared.currentTarget Prepared.stat
  Prepared.kept Prepared.code Prepared.codeAt Prepared.codeAddress Prepared.transfer Prepared.value Prepared.bal
  Entered.transfer Entered.pc Entered.sta Entered.state from Blanc.ExecutionKeptTop
open private processTransaction_form transactionMessage_facts PreparedTx PreparedTx.caller PreparedTx.routed
  PreparedTx.deletions PreparedTx.stat PreparedTx.created PreparedTx.debit debit_getCode settleSelfdestructs_get
  withdrawalsPass_getCode from Blanc.ExecutionKeptChain

/-!
# Kept-frame value: never falls, and covers the kept values

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

**What this is.** The neutral `Exec` fold O37 needs, over kept (settled) frames
only: nothing here names `rawNodes`, `rawFrames`, a gas amount, or a frame that
did not commit, and nothing reads a fork. `Exec.kept_bal_ge_keptPaid` says a
committed run of a frame not at `a` leaves `a` with at least its balance plus
every kept frame's carried value (`Exec.keptPaid`); `Exec.kept_bal_neverFalls`
is its corollary. One induction over `Exec.retained_induction`: the code premise
threads down by `Blanc.Exec.Deriv.ParentStep.codePreserve`, the target premise
`sevm.currentTarget ≠ a` unchanged (a parent step at `a` running arbitrary code
could debit the account), and the world-sum bound `SumNof` from the run's start
by balance-total monotonicity. The at-code frame law is a premise, discharged
per contract by `frame_keeps_balances` (`Blanc/Lift/BuilderRequest/Surplus.lean`).

**The spawn facts.** `Xinst.step_spawn_bal_neutral`: a spawned frame's messages
open on the parent's balances, and a value-moving spawn's caller is its parent's
target, while a non-moving one stays at the parent's target. So
`Evm.step_spawn_enter_bal` credits a child entering `a` exactly its value, and
leaves `a` alone otherwise. `Evm.step_spawn_settled_getBal` hands a settled
child's balances to its parent, on the create lane through code deposit;
`Evm.step_spawn_rolled_getBal` restores the parent's balances after a child that
does not commit. These are the balance twins of the storage facts in
`Blanc/ExecutionKeptFrames.lean`, for every rule record.
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
theorem Xinst.step_spawn_bal_neutral {sevm : Sevm} {pre : Devm} {x : Xinst}
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
theorem Evm.step_spawn_enter_bal {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
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
theorem Evm.step_spawn_settled_getBal {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
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
theorem Evm.step_spawn_rolled_getBal {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
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

/-! ## The message level -/

/-- **A message's value transfer, at one account.** With no debit from the account and a world sum
below `2 ^ 256` when it is the target, the account's balance is up by exactly the value when it is
the target, and unchanged otherwise. -/
theorem Msg.transfer_bal_eq {msg : Msg} {benv : Benv} {a : Adr}
    (transfer : msg.benvAfterTransfer = .ok benv)
    (caller : msg.shouldTransferValue = true → msg.caller ≠ a)
    (zero : msg.shouldTransferValue = false → msg.currentTarget = a → msg.value = 0)
    (sum_nof : msg.currentTarget = a → sum msg.benv.state.bal < 2 ^ 256) :
    (benv.state.bal a).toNat = (msg.benv.state.bal a).toNat +
      if msg.currentTarget = a then msg.value.toNat else 0 := by
  by_cases tr : msg.shouldTransferValue = true ∧ msg.value ≠ 0
  · obtain ⟨debit, sub, rfl⟩ := of_benvAfterTransfer tr.1 tr.2 transfer
    have callerNe := caller tr.1
    by_cases here : msg.currentTarget = a
    · have bound := sum_nof here
      subst a
      rw [ite_eq_left rfl]
      exact of_transfer_bal_target sub callerNe bound
    · rw [ite_eq_right here, Nat.add_zero]
      exact congrArg B256.toNat (of_transfer_bal_other sub callerNe here)
  · have entry_eq := benvAfterTransfer_eq_of_not_transfer tr transfer
    subst entry_eq
    by_cases here : msg.currentTarget = a
    · rw [ite_eq_left here]
      have value_eq : msg.value = 0 := by
        cases transfers : msg.shouldTransferValue with
        | true =>
            by_contra nonzero
            exact tr ⟨transfers, nonzero⟩
        | false => exact zero transfers here
      rw [value_eq]
      rfl
    · rw [ite_eq_right here, Nat.add_zero]

/-- The values the frames some roots keep at `a` carried in. -/
def Root.paidAt (a : Adr) (rs : List Root) : Nat :=
  ((rs.flatMap (Root.keptAt a)).map fun f => f.sevm.value.toNat).sum

theorem Root.paidAt_append (a : Adr) (xs ys : List Root) :
    Root.paidAt a (xs ++ ys) = Root.paidAt a xs + Root.paidAt a ys := by
  unfold Root.paidAt
  rw [List.flatMap_append, List.map_append, List.sum_append]

theorem Root.paidAt_nil (a : Adr) : Root.paidAt a [] = 0 := by
  unfold Root.paidAt
  rw [List.flatMap_nil, List.map_nil, List.sum_nil]

/-- **The world-sum bound at a root.** Every root's message opened on a world whose balances sum
below `2 ^ 256`. -/
def RootsFit (rs : List Root) : Prop := ∀ r ∈ rs, SumNof r.frame.outer.benv.state.bal

theorem RootsFit.left {xs ys : List Root} (h : RootsFit (xs ++ ys)) : RootsFit xs :=
  fun r hr => h r (List.mem_append_left _ hr)

theorem RootsFit.right {xs ys : List Root} (h : RootsFit (xs ++ ys)) : RootsFit ys :=
  fun r hr => h r (List.mem_append_right _ hr)

/-- What the value folds ask of the account: nonempty code that is no delegation, and the at-code
law that a committed frame at the account running that code keeps its balance. -/
structure KeptValueAt (a : Adr) (C : ByteArray) : Prop where
  nonempty : C.toList ≠ []
  nondelegating : ¬ isValidDelegation C
  law : ∀ {s : Sevm} {d e : Devm}, s.currentTarget = a → s.code = C → Exec 0 s d (.ok e) →
    (e.getBal a).toNat = (d.getBal a).toNat

/-- `a`'s balance covers its start plus the values the roots kept there carried in. -/
def BalCovers (a : Adr) (st : State) (rs : List Root) (st' : State) : Prop :=
  (st.bal a).toNat + Root.paidAt a rs ≤ (st'.bal a).toNat

theorem BalCovers.append {a : Adr} {s m t : State} {xs ys : List Root} (first : BalCovers a s xs m)
    (second : BalCovers a m ys t) : BalCovers a s (xs ++ ys) t := by
  unfold BalCovers at first second ⊢
  rw [Root.paidAt_append]
  omega

theorem BalCovers.nil {a : Adr} {s t : State} (h : (s.bal a).toNat ≤ (t.bal a).toNat) :
    BalCovers a s [] t := by
  unfold BalCovers
  rw [Root.paidAt_nil, Nat.add_zero]
  exact h

/-- Clean code-deposit settlement of a top-level create hands the constructor's balances on. -/
private theorem settle_ofCreate_committed_bal {m : Msg} {raw : Execution} {s : Devm}
    (settled : (Frame.ofCreate m).settle raw = .ok s) (c : Execution.commits raw = true)
    (clean : s.error.isNone = true) :
    s.state.bal = (Execution.committedPost raw c).state.bal := by
  obtain ⟨inner, hi, hs, -, hn⟩ := settle_inner_clean (m := processCreateMessage.msg m) c
  have run : processCreateMessage.settle m (.ok inner) = .ok s := by
    rw [← hi]
    exact settled
  unfold processCreateMessage.settle at run
  simp only [bind, Except.bind, hn, ↓reduceIte] at run
  cases charge : processCreateMessage.chargeCodeGas m.benv.stat.rules inner with
  | error error =>
      rw [charge] at run
      rcases error with ⟨error, charged⟩
      cases error with
      | halt reason =>
          have eq := Except.ok.inj run
          rw [← eq] at clean
          cases hsg : m.benv.stat.rules.stateGas <;>
            simp only [hsg, Devm.error, processCreateMessage.exceptionalHalt,
              processCreateMessage.exceptionalHaltAmsterdam, Devm.setMeta, Devm.withStorageWrites, Devm.setWorld,
              Option.isNone_some, Bool.false_eq_true] at clean
      | revert => cases run
      | crypto reason => cases run
      | internal reason => cases run
  | ok charged =>
      rw [charge] at run
      have eq := Except.ok.inj run
      subst eq
      have hstate := (chargeCodeGas_state_ok charge).trans hs
      change (charged.state.setCode m.currentTarget ⟨⟨charged.output⟩⟩).bal = _
      rw [State.setCode_bal, hstate]

section TopRunValue

variable {msg m : Msg} {state : State} {out : MsgCallOutput} {f : Frame} {benv : Benv} {e : Evm}
  {raw : Execution} {s : Devm} {a : Adr}

/-- What a top frame's entry does at a code-bearing account: the message's routing and value reach
the machine, and the account is credited the value exactly when it is the target. -/
private theorem topRun_entry (t : TopRun msg m state out f benv e raw s)
    (hc : (msg.benv.state.getCode a).toList ≠ []) (hd : ¬ isValidDelegation (msg.benv.state.getCode a))
    (caller : msg.shouldTransferValue = true → msg.caller ≠ a)
    (zero : msg.shouldTransferValue = false → msg.value = 0)
    (fits : msg.currentTarget = a → SumNof f.outer.benv.state.bal) :
    (e.dyna.state.bal a).toNat = (msg.benv.state.bal a).toNat +
        (if msg.currentTarget = a then msg.value.toNat else 0) ∧
      sum e.dyna.state.bal ≤ sum f.outer.benv.state.bal ∧
      e.sta.currentTarget = msg.currentTarget ∧ e.sta.value = msg.value ∧ e.pc = 0 := by
  have prep := TopRun.prepared t
  have fields : f.inner.caller = msg.caller ∧ f.inner.shouldTransferValue = msg.shouldTransferValue ∧
      f.inner.value = msg.value ∧ f.inner.currentTarget = msg.currentTarget ∧
      f.inner.benv.state.bal a = msg.benv.state.bal a ∧ f.inner.benv.state.bal = f.outer.benv.state.bal := by
    have h1 := Prepared.caller prep
    have h2 := Prepared.transfer prep
    have h3 := Prepared.value prep
    have h4 := Prepared.currentTarget prep
    have h5 := Prepared.bal prep a hc hd
    rcases TopRun.shape t with hf | hf
    · rw [hf]
      exact ⟨h1, h2, h3, h4, h5, rfl⟩
    · rw [hf]
      refine ⟨h1, h2, h3, h4, ?_, processCreateMessage_msg_bal_eq m⟩
      change (processCreateMessage.msg m).benv.state.bal a = _
      rw [processCreateMessage_msg_bal_eq]
      exact h5
  obtain ⟨hcaller, htransfer, hvalue, htarget, hbal, hsum⟩ := fields
  have entered := TopRun.entered t
  have hstate : e.dyna.state = benv.state := Entered.state entered
  have hsta : e.sta = initSevm (f.inner.withBenv benv) := Entered.sta entered
  have transfer := Entered.transfer entered
  have key := Msg.transfer_bal_eq (a := a) transfer
    (by intro tr; rw [hcaller]; exact caller (by rw [← htransfer]; exact tr))
    (by intro tr _; rw [hvalue]; exact zero (by rw [← htransfer]; exact tr))
    (by intro here; rw [hsum]; exact fits (htarget.symm.trans here))
  rw [htarget, hvalue, hbal] at key
  refine ⟨by rw [hstate]; exact key, ?_, by rw [hsta]; exact htarget, by rw [hsta]; exact hvalue,
    Entered.pc entered⟩
  have hb := Msg.benvAfterTransfer_balance_effect (out := .ok benv) transfer
  change State.balSum benv.state ≤ State.balSum f.inner.benv.state at hb
  change sum e.dyna.state.bal ≤ _
  rw [hstate, ← hsum]
  exact hb

/-- A committing top frame leaves the world its run committed, at every balance. -/
private theorem topRun_committed_bal (t : TopRun msg m state out f benv e raw s)
    (c : Execution.commits raw = true) (clean : s.error.isNone = true) :
    state.bal = (Execution.committedPost raw c).state.bal := by
  rw [TopRun.state_eq t]
  rcases TopRun.shape t with hf | hf
  · subst hf
    exact congrArg Jaune.State.bal (settle_ofCall_committed (TopRun.settled t) c).1
  · subst hf
    exact settle_ofCreate_committed_bal (TopRun.settled t) c clean

/-- A top frame that does not commit leaves a code-bearing account's balance as the message found it. -/
private theorem topRun_rolled_bal (t : TopRun msg m state out f benv e raw s)
    (hc : (msg.benv.state.getCode a).toList ≠ []) (hd : ¬ isValidDelegation (msg.benv.state.getCode a))
    (dirty : ¬ s.error.isNone = true) : state.bal a = msg.benv.state.bal a := by
  have some : s.error.isSome = true := by
    cases he : s.error
    · simp only [he, Option.isNone_none, not_true_eq_false] at dirty
    · rfl
  rw [TopRun.state_eq t, settle_error_rollback (TopRun.shape t) (TopRun.settled t) some]
  exact Prepared.bal (TopRun.prepared t) a hc hd

end TopRunValue

/-- **The message level.** A message that neither debits `a` nor carries value it does not move,
routed to its own target, with `a` holding code `C` that is no precompile under its rules: `a`'s
balance covers its start plus the values its roots kept there carried in, provided each root
opened on a world whose balances sum below `2 ^ 256`. -/
theorem MessageRoots.bal_covers {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) {a : Adr} {C : ByteArray} (V : KeptValueAt a C)
    (code : msg.benv.state.getCode a = C) (routed : RoutedMessage msg)
    (precomp : ¬ msg.benv.stat.rules.isPrecomp a)
    (caller : msg.shouldTransferValue = true → msg.caller ≠ a)
    (zero : msg.shouldTransferValue = false → msg.value = 0) (fits : RootsFit rs) :
    BalCovers a msg.benv.state rs state := by
  have hc : (msg.benv.state.getCode a).toList ≠ [] := by rw [code]; exact V.nonempty
  have hd : ¬ isValidDelegation (msg.benv.state.getCode a) := by rw [code]; exact V.nondelegating
  obtain ⟨result, hmap⟩ := h
  rcases message_top result with ⟨hnone, hst, -⟩ | ⟨hnone, m, f, benv, e, adr, s, t⟩ |
      ⟨m, f, benv, e, s, hsome, t⟩
  · rw [hnone] at hmap
    rw [List.map_eq_nil_iff.mp hmap, hst]
    exact BalCovers.nil (Nat.le_refl _)
  · rw [hnone] at hmap
    rw [List.map_eq_nil_iff.mp hmap]
    have prep := TopRun.prepared t
    have away : msg.currentTarget ≠ a := by
      intro here
      rcases TopRun.top t with hsome | ⟨-, adr', -, hca, hp⟩
      · rw [hnone] at hsome
        cases hsome
      · have hstat : benv.stat = msg.benv.stat := by
          have := Jaune.benvAfterTransfer_stat (Entered.transfer (TopRun.entered t))
          have hs := Prepared.stat prep
          rcases TopRun.shape t with hf | hf <;> rw [hf] at this <;> exact this.trans hs
        rcases TopRun.frame t with ⟨hcall, hf⟩ | ⟨hcreate, hf, -⟩
        · subst hf
          have kept := (Prepared.kept prep a hc hd).1
          have hat := Prepared.codeAt prep hcall (routed.1 hcall).1 (routed.1 hcall).2
            (by rw [here, kept]; exact hd)
          have same : adr' = a := by
            have h1 : m.codeAddress = some adr' := hca
            rw [hat, here] at h1
            exact (Option.some.inj h1).symm
          subst same
          have flag := of_decide_eq_true ((Bool.and_eq_true _ _).mp hp).2
          change benv.stat.rules.isPrecomp adr' at flag
          rw [hstat] at flag
          exact precomp flag
        · subst hf
          have h1 : m.codeAddress = some adr' := hca
          rw [Prepared.codeAddress prep hcreate, routed.2 hcreate] at h1
          cases h1
    by_cases clean : s.error.isNone = true
    · have c : Execution.commits (executePrecomp e adr) = true :=
        Frame.raw_commits_of_settlementCommits ((TopRun.commits_eq t).trans clean)
      obtain ⟨entry, -⟩ := topRun_entry (a := a) t hc hd caller zero (fun here => absurd here away)
      rw [ite_eq_right away, Nat.add_zero] at entry
      apply BalCovers.nil
      rw [topRun_committed_bal t c clean, (precomp_post e adr c).1, entry]
    · exact BalCovers.nil (Nat.le_of_eq (congrArg B256.toNat (topRun_rolled_bal t hc hd clean).symm))
  · rw [hsome] at hmap
    cases rs with
    | nil => cases hmap
    | cons r tail =>
        simp only [Option.toList_some, List.map_cons, List.cons.injEq, Prod.mk.injEq,
          List.map_eq_nil_iff] at hmap
        obtain ⟨⟨hf, he⟩, rfl⟩ := hmap
        have fitsR := fits r List.mem_cons_self
        obtain ⟨frame, evm, raw, run⟩ := r
        dsimp only at hf he fitsR
        subst hf he
        have hraw : exec evm = raw := (exec_iff_exec_eq _ _ _ _).mp ⟨run⟩
        subst hraw
        have prep := TopRun.prepared t
        obtain ⟨entry, hsum, htarget, hvalue, hpc⟩ :=
          topRun_entry (a := a) t hc hd caller zero (fun _ => fitsR)
        unfold BalCovers Root.paidAt
        rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        by_cases clean : s.error.isNone = true
        · have settles : Frame.settlementCommits frame (exec evm) = true := (TopRun.commits_eq t).trans clean
          have c := Frame.raw_commits_of_settlementCommits settles
          have handed := congrFun (topRun_committed_bal t c clean) a
          rw [Root.keptAt, dite_eq_left settles]
          dsimp only
          by_cases here : evm.sta.currentTarget = a
          · rw [ite_eq_left here, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
            have target : msg.currentTarget = a := htarget.symm.trans here
            rw [ite_eq_left target] at entry
            have runsC : evm.sta.code = C := by
              rcases TopRun.frame t with ⟨hcall, hf⟩ | ⟨hcreate, hf, -⟩
              · have hsta : evm.sta = initSevm (frame.inner.withBenv benv) := Entered.sta (TopRun.entered t)
                have kept := (Prepared.kept prep a hc hd).1
                have hm := Prepared.code prep hcall (routed.1 hcall).1 (routed.1 hcall).2
                  (by rw [target, kept]; exact hd)
                rw [hsta, hf]
                change m.code = C
                rw [hm, target, kept, code]
              · exact absurd target (TopRun.create_ne t hc hd (by rw [hf]; rfl))
            obtain ⟨post, hpost⟩ : ∃ post, exec evm = .ok post := by
              cases hx : exec evm with
              | error err =>
                  rw [hx] at c
                  simp only [Execution.commits, Bool.false_eq_true] at c
              | ok post => exact ⟨post, rfl⟩
            have run0 : Exec 0 evm.sta evm.dyna (.ok post) := by
              rw [← hpc, ← hpost]
              exact run
            have law := V.law here runsC run0
            have postEq : (Execution.committedPost (exec evm) c).state.bal a = post.state.bal a := by
              have key : ∀ (x : Execution) (hx : x = .ok post) (cx : Execution.commits x = true),
                  Execution.committedPost x cx = post := by
                intro x hx cx
                subst hx
                rfl
              rw [key _ hpost c]
            change (msg.benv.state.bal a).toNat + (Exec.Frame.ofRun run c).sevm.value.toNat ≤ _
            change (msg.benv.state.bal a).toNat + evm.sta.value.toNat ≤ _
            rw [handed, postEq, hvalue]
            change _ ≤ (post.getBal a).toNat
            rw [law]
            change _ ≤ (evm.dyna.state.bal a).toNat
            rw [entry]
          · rw [ite_eq_right here]
            have target : msg.currentTarget ≠ a := fun same => here (htarget.trans same)
            rw [ite_eq_right target, Nat.add_zero] at entry
            have entryCode : evm.dyna.getCode a = C :=
              (TopRun.entry_getCode t a).trans ((Prepared.kept prep a hc hd).1.trans code)
            have sumsE : SumNof evm.dyna.state.bal := by
              unfold SumNof at fitsR ⊢
              exact Nat.lt_of_le_of_lt hsum fitsR
            have fold := Exec.kept_bal_ge_keptPaid run c here entryCode V.nonempty V.nondelegating sumsE V.law
            unfold Exec.keptPaid at fold
            rw [handed]
            change (evm.dyna.state.bal a).toNat + _ ≤ _ at fold
            rw [entry] at fold
            exact fold
        · have rolled : ¬ Frame.settlementCommits frame (exec evm) = true := by
            rw [TopRun.commits_eq t]
            exact clean
          rw [Root.keptAt, dite_eq_right rolled, List.map_nil, List.sum_nil, Nat.add_zero]
          exact Nat.le_of_eq (congrArg B256.toNat (topRun_rolled_bal t hc hd clean).symm)

/-! ## The transaction level -/

/-- A credit that does not wrap at `a` leaves `a` no poorer. -/
private theorem addBal_bal_mono {st : State} {x a : Adr} {v : B256}
    (fit : x = a → (st.bal a).toNat + v.toNat < 2 ^ 256) :
    (st.bal a).toNat ≤ ((st.addBal x v).bal a).toNat := by
  by_cases same : x = a
  · subst same
    have nof := fit rfl
    change (st.bal x).toNat ≤ (((st.setBal x (st.bal x + v)).get x).bal).toNat
    rw [State.setBal_get_self, Acct.clearIfEmpty_bal]
    change (st.bal x).toNat ≤ (st.bal x + v).toNat
    rw [B256.toNat_add_eq_of_nof _ _ nof]
    exact Nat.le_add_right _ _
  · apply Nat.le_of_eq
    change (st.bal a).toNat = (((st.setBal x (st.bal x + v)).get a).bal).toNat
    rw [State.setBal_get_ne same]
    rfl

/-- **No wrap at the tip.** When a transaction's settlement credits its fee recipient `a`, `a`'s
balance plus the tip stays below `2 ^ 256`. A virtual certainty: no pinned read answers it today. -/
def TipFits (a : Adr) (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) : Prop :=
  ∀ (sender : Adr) (msg : Msg) (messageState : State) (messageOut : MsgCallOutput) (refund tip : B256)
    (state : State) (bout' : BlockOutput),
    processTransaction benv bout tx index = .ok (state, bout') →
    transactionMessage benv bout tx index = .ok (sender, msg) →
    processMessageCall msg = .ok (messageState, messageOut) →
    state = sweepTouchedAccounts benv.stat.rules messageOut.touchedAccounts.toList
      (settleSelfdestructs benv.stat.rules messageOut.accountsToDelete.toList
        ((messageState.addBal sender refund).addBal benv.stat.coinbase tip)) →
    benv.stat.coinbase = a → ((messageState.addBal sender refund).bal a).toNat + tip.toNat < 2 ^ 256

/-- A transaction's prepared message moves its value. -/
private theorem transactionMessage_transfers {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {sender : Adr} {msg : Msg} (h : transactionMessage benv bout tx index = .ok (sender, msg)) :
    msg.shouldTransferValue = true := by
  unfold transactionMessage at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨intrinsic, floor⟩, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨sender', price, hashes, blob⟩, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨debit, -, h⟩ := Except.bind_eq_ok h
  obtain ⟨msg', hprepared, h⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  unfold prepareMessage at hprepared
  split at hprepared
  all_goals
    dsimp only at hprepared
    obtain rfl := Except.ok.inj hprepared
    rfl

/-- **The transaction level.** With `a` holding code `C` that is no precompile, created in no
earlier transaction of the block and not the sender: `a`'s balance covers its start plus the values
the transaction's roots kept there, given the world-sum bound at each root and no wrap at the tip. -/
theorem TransactionRoots.bal_covers {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {sender : Adr} {rs : List Root}
    (h : TransactionRoots benv bout tx index state bout' sender rs) (rules : KeptRules benv.stat.rules)
    {a : Adr} {C : ByteArray} (V : KeptValueAt a C) (code : benv.state.getCode a = C)
    (precomp : ¬ benv.stat.rules.isPrecomp a) (created : a ∉ benv.createdAccounts)
    (notSender : sender ≠ a) (fits : RootsFit rs) (tip : TipFits a benv bout tx index) :
    BalCovers a benv.state rs state := by
  obtain ⟨result, msg₀, state₀, out₀, hm₀, roots⟩ := h
  obtain ⟨sender', msg, messageState, messageOut, refund, tipAmount, hm, hmessage, final, -⟩ :=
    processTransaction_form result
  have same := Except.ok.inj (hm₀.symm.trans hm)
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  have sameOut := Except.ok.inj (roots.1.symm.trans hmessage)
  simp only [Prod.mk.injEq] at sameOut
  obtain ⟨rfl, rfl⟩ := sameOut
  have facts := transactionMessage_facts hm
  obtain ⟨v, hdebit⟩ := PreparedTx.debit facts
  have hcode := debit_getCode hdebit a
  have debitBal : msg₀.benv.state.bal a = benv.state.bal a := by
    obtain ⟨-, hmid⟩ := State.of_subBal hdebit
    rw [hmid]
    change (((benv.state.incrNonce sender).setBal sender _).get a).bal = _
    rw [State.setBal_get_ne notSender]
    exact congrFun State.incrNonce_bal a
  have hc' : (msg₀.benv.state.getCode a).toList ≠ [] := by rw [hcode, code]; exact V.nonempty
  have hd' : ¬ isValidDelegation (msg₀.benv.state.getCode a) := by rw [hcode, code]; exact V.nondelegating
  have message := roots.bal_covers V (hcode.trans code) (PreparedTx.routed facts)
    (by rw [PreparedTx.stat facts]; exact precomp)
    (fun _ => by rw [PreparedTx.caller facts]; exact notSender)
    (fun stays => by rw [transactionMessage_transfers hm] at stays; cases stays) fits
  have notDeleted := roots.not_deleted hc' hd'
    (by rw [PreparedTx.deletions facts]; exact AdrSet.not_mem_empty)
    (by rw [PreparedTx.created facts]; exact created) (by rw [PreparedTx.stat facts]; exact rules.selfdestruct)
  have notList : ∀ x ∈ out₀.accountsToDelete.toList, x ≠ a :=
    fun x member same => notDeleted (same ▸ Std.HashSet.mem_toList.mp member)
  have fit := tip sender msg₀ state₀ out₀ refund tipAmount state bout' result hm hmessage final
  rw [sweepTouchedAccounts_of_not_touchedSweep rules.noSweep] at final
  have hget := settleSelfdestructs_get notList benv.stat.rules
    ((state₀.addBal sender refund).addBal benv.stat.coinbase tipAmount)
  have finalBal : state.bal a =
      ((state₀.addBal sender refund).addBal benv.stat.coinbase tipAmount).bal a := by
    rw [final]
    exact congrArg Acct.bal hget
  have refundBal : (state₀.addBal sender refund).bal a = state₀.bal a := by
    change ((state₀.setBal sender _).get a).bal = _
    rw [State.setBal_get_ne notSender]
    rfl
  have tipMono := addBal_bal_mono (st := state₀.addBal sender refund) (x := benv.stat.coinbase)
    (a := a) (v := tipAmount) (fun same => fit same)
  unfold BalCovers at message ⊢
  rw [debitBal] at message
  rw [finalBal]
  rw [refundBal] at tipMono
  omega

/-- No wrap at any tip of a transaction list, along its run. -/
def TipsFit (a : Adr) : List (Nat × Tx) → Benv → BlockOutput → Prop
  | [], _, _ => True
  | (i, tx) :: rest, benv, bout => TipFits a benv bout tx i ∧
      ∀ st bout', processTransaction benv bout tx i = .ok (st, bout') → TipsFit a rest (benv.withState st) bout'

/-- **The transaction-list level.** -/
theorem TransactionsRoots.bal_covers {txis : List (Nat × Tx)} {benv final : Benv} {bout finalOut : BlockOutput}
    {txs : List (Adr × Tx)} {rs : List Root} (h : TransactionsRoots txis benv bout final finalOut txs rs)
    {a : Adr} {C : ByteArray} (V : KeptValueAt a C) :
    KeptRules benv.stat.rules → benv.state.getCode a = C → ¬ benv.stat.rules.isPrecomp a →
      a ∉ benv.createdAccounts → NoSenderAt a txs → RootsFit rs → TipsFit a txis benv bout →
      BalCovers a benv.state rs final.state := by
  induction h with
  | nil benv bout =>
      intro _ _ _ _ _ _ _
      exact BalCovers.nil (Nat.le_refl _)
  | cons head tail ih =>
      intro rules code precomp created senders fits tips
      have hc : (_ : State).getCode a = C := code
      obtain ⟨tipHead, tipRest⟩ := tips
      have first := head.bal_covers rules V code precomp created (senders _ List.mem_cons_self)
        fits.left tipHead
      have code₁ := (head.chain rules (by rw [code]; exact V.nonempty) (by rw [code]; exact V.nondelegating)
        created).2
      have second := ih rules (by simpa only [Benv.withState, code₁] using code) precomp created
        (fun p hp => senders p (List.mem_cons_of_mem _ hp)) fits.right (tipRest _ _ head.1)
      exact first.append second

/-! ## The block level -/

/-- A system message's roots, at a code-bearing account that is no precompile. -/
private theorem systemRoots_bal_covers {benv : Benv} {target : Adr} {data : Bytes} {st : State}
    {out : MsgCallOutput} {rs : List Root} (roots : MessageRoots (systemTransactionMessage benv target data) st out rs)
    {a : Adr} {C : ByteArray} (V : KeptValueAt a C) (code : benv.state.getCode a = C)
    (precomp : ¬ benv.stat.rules.isPrecomp a) (fits : RootsFit rs) :
    BalCovers a benv.state rs st ∧ st.getCode a = benv.state.getCode a := by
  obtain ⟨hnone, htarget, hca, hcode, -, -, hstate⟩ := systemTransactionMessage_shape benv target data
  have codeM : (systemTransactionMessage benv target data).benv.state.getCode a = C := by
    rw [hstate]; exact code
  have covers := roots.bal_covers V codeM ⟨fun _ => ⟨hca, hcode⟩, fun h => by rw [hnone] at h; cases h⟩
    precomp (fun h => by cases h) (fun _ => rfl) fits
  rw [hstate] at covers
  refine ⟨covers, ?_⟩
  have chain := (roots.chain (a := a) (by rw [codeM]; exact V.nonempty) (by rw [codeM]; exact V.nondelegating)).2
  rw [hstate] at chain
  exact chain

private theorem PreCall.bal_covers {on : Bool} {benv : Benv} {target : Adr} {data : Bytes} {st : State}
    {rs : List Root} (h : PreCall on benv target data st rs) {a : Adr} {C : ByteArray} (V : KeptValueAt a C)
    (code : benv.state.getCode a = C) (precomp : ¬ benv.stat.rules.isPrecomp a) (fits : RootsFit rs) :
    BalCovers a benv.state rs st ∧ st.getCode a = benv.state.getCode a := by
  unfold PreCall at h
  split at h
  · obtain ⟨out, roots⟩ := h
    exact systemRoots_bal_covers roots V code precomp fits
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨BalCovers.nil (Nat.le_refl _), rfl⟩

private theorem PreRoots.bal_covers {benv : Benv} {st : State} {bal : BalBuilder} {rs : List Root}
    (h : PreRoots benv st bal rs) {a : Adr} {C : ByteArray} (V : KeptValueAt a C)
    (code : benv.state.getCode a = C) (precomp : ¬ benv.stat.rules.isPrecomp a) (fits : RootsFit rs) :
    BalCovers a benv.state rs st ∧ st.getCode a = benv.state.getCode a := by
  obtain ⟨beacon, -, beaconRoots, historyRoots, -, first, -, second, rfl⟩ := h
  obtain ⟨covers₁, code₁⟩ := first.bal_covers V code precomp fits.left
  obtain ⟨covers₂, code₂⟩ := second.bal_covers (a := a) V (by simpa only [Benv.withState, code₁] using code)
    precomp fits.right
  exact ⟨covers₁.append covers₂, code₂.trans code₁⟩

private theorem RequestRoots.bal_covers {idx : Nat} {contracts : List (UInt8 × Adr)} {benv : Benv}
    {acc acc' : List Bytes} {bal bal' : BalBuilder} {final : State} {steps : List RequestStep}
    (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) {a : Adr} {C : ByteArray}
    (V : KeptValueAt a C) :
    benv.state.getCode a = C → ¬ benv.stat.rules.isPrecomp a → RootsFit (requestRootsOf steps) →
      BalCovers a benv.state (requestRootsOf steps) final := by
  induction h with
  | nil benv acc bal =>
      intro _ _ _
      exact BalCovers.nil (Nat.le_refl _)
  | cons hcall roots tail ih =>
      intro code precomp fits
      unfold requestRootsOf at fits ⊢
      rw [List.flatMap_cons] at fits ⊢
      obtain ⟨covers₁, code₁⟩ := systemRoots_bal_covers roots V code precomp fits.left
      have covers₂ := ih (by simpa only [Benv.withState, code₁] using code) precomp fits.right
      exact covers₁.append covers₂

private theorem RequestPass.bal_covers {benv : Benv} {bout : BlockOutput} {st : State} {out : BlockOutput}
    {steps : List RequestStep} (h : RequestPass benv bout st out steps) {a : Adr} {C : ByteArray}
    (V : KeptValueAt a C) (code : benv.state.getCode a = C) (precomp : ¬ benv.stat.rules.isPrecomp a)
    (fits : RootsFit (requestRootsOf steps)) : BalCovers a benv.state (requestRootsOf steps) st := by
  unfold RequestPass at h
  split at h
  · obtain ⟨deposits, acc, bal, -, roots, -⟩ := h
    exact roots.bal_covers V code precomp fits
  · obtain ⟨rfl, -, rfl⟩ := h
    exact BalCovers.nil (Nat.le_refl _)

/-- **No wrap at a withdrawal credit.** Along the block's withdrawals, every credit to `a` keeps `a`'s
balance below `2 ^ 256`. A virtual certainty: no pinned read answers it today. -/
def WdsFit (a : Adr) : State → List Withdrawal → Prop
  | _, [] => True
  | st, wd :: rest => (wd.recipient = a → (st.bal a).toNat + (wd.amount * (10 ^ 9).toB256).toNat < 2 ^ 256) ∧
      WdsFit a (st.addBal wd.recipient (wd.amount * (10 ^ 9).toB256)) rest

private theorem processWithdrawalsState_bal_mono {a : Adr} :
    ∀ (wds : List Withdrawal) (st : State), WdsFit a st wds →
      (st.bal a).toNat ≤ ((processWithdrawalsState st wds).bal a).toNat
  | [], _, _ => Nat.le_refl _
  | wd :: rest, st, ⟨head, tail⟩ => by
      unfold processWithdrawalsState
      rw [List.foldl_cons]
      exact Nat.le_trans (addBal_bal_mono head) (processWithdrawalsState_bal_mono rest _ tail)

private theorem withdrawalsPass_bal_mono {a : Adr} (rules : ForkRules) (benv : Benv) (bout : BlockOutput)
    (wds : List Withdrawal) (fit : WdsFit a benv.state wds) :
    (benv.state.bal a).toNat ≤ ((withdrawalsPass rules benv bout wds).1.bal a).toNat := by
  unfold withdrawalsPass
  split
  · exact processWithdrawalsState_bal_mono wds benv.state fit
  · exact Nat.le_refl _

/-- **The block level.** -/
theorem BodyRoots.bal_covers {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput} {run : BodyRun}
    (h : BodyRoots benv txs ommers wds state bout run) (rules : KeptRules benv.stat.rules) {a : Adr}
    {C : ByteArray} (V : KeptValueAt a C) (code : benv.state.getCode a = C)
    (precomp : ¬ benv.stat.rules.isPrecomp a) (created : a ∉ benv.createdAccounts)
    (senders : NoSenderAt a run.senders) (fits : RootsFit run.roots)
    (tips : ∀ decoded, txs.mapM (decodeTx benv.stat.rules) = .ok decoded →
      TipsFit a decoded.putIndex (benv.withState run.preState) {BlockOutput.init with bal := run.preBal})
    (withdrawals : WdsFit a run.txEnv.state wds) :
    BalCovers a benv.state run.roots state := by
  obtain ⟨st, out, pass, final, -⟩ := h.stages
  obtain ⟨decoded, hdecoded, roots⟩ := h.transactions
  unfold BodyRun.roots at fits ⊢
  obtain ⟨covers₁, code₁⟩ := h.pre.bal_covers V code precomp fits.left.left
  have covers₂ := roots.bal_covers V rules (by simpa only [Benv.withState, code₁] using code) precomp created
    senders fits.left.right (tips decoded hdecoded)
  have code₂ := (roots.chain rules (a := a) (by simpa only [Benv.withState, code₁, code] using V.nonempty)
    (by simpa only [Benv.withState, code₁, code] using V.nondelegating) created).2
  simp only [Benv.withState] at covers₂ code₂
  have codeT : run.txEnv.state.getCode a = C := code₂.trans (code₁.trans code)
  have wdsMono := withdrawalsPass_bal_mono (a := a) benv.stat.rules run.txEnv run.txOut wds withdrawals
  have hcodeW := withdrawalsPass_getCode benv.stat.rules run.txEnv run.txOut wds a
  have covers₃ := pass.bal_covers V (by simpa only [Benv.withState, hcodeW] using codeT)
    (by simpa only [Benv.withState, h.txEnv_stat] using precomp) fits.right
  simp only [Benv.withState] at covers₃
  rw [final rules.noRewards]
  have joined := covers₁.append covers₂
  unfold BalCovers at joined covers₃ ⊢
  simp only [Root.paidAt_append] at joined ⊢
  omega

end Blanc
