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

/-- **Never falls across one kept run.** At an account holding nondelegating
code, with the world-sum bound at every derivation and the at-code frame law,
a committed run leaves the account no poorer. The sum premise is universal on
purpose: the compiling run weakens it to endpoint-plus-preservation. -/
theorem Exec.kept_bal_neverFalls {C : ByteArray} {a : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) (target : sevm.currentTarget ≠ a)
    (code : pre.getCode a = C)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (sums : ∀ {q : Nat} {s : Sevm} {d : Devm} {o : Execution},
      Exec q s d o → SumNof d.state.bal)
    (at_code : ∀ {s : Sevm} {d e : Devm}, s.currentTarget = a →
      s.code = C → Exec 0 s d (.ok e) → (e.getBal a).toNat = (d.getBal a).toNat) :
    (pre.getBal a).toNat ≤ ((Execution.committedPost out committed).getBal a).toNat := by
  refine Exec.retained_induction
    (P := fun _ sevm pre out run => sevm.currentTarget ≠ a → pre.getCode a = C →
      ∀ (committed : Execution.commits out = true),
        (pre.getBal a).toNat ≤ ((Execution.committedPost out committed).getBal a).toNat)
    ?_ ?_ ?_ ?_ ?_ run committed target code committed
  · intro pc sevm pre out step target code committed
    revert committed
    cases out with
    | error err =>
        intro committed
        simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post =>
        intro committed
        have sum_pre : sum pre.state.bal < 2 ^ 256 :=
          sums (Exec.halt step)
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
  · intro pc sevm pre pc' post out step next ih target code committed
    have sum_pre : sum pre.state.bal < 2 ^ 256 := sums (Exec.cont step next)
    have hmono : (pre.state.bal a).toNat ≤ (post.state.bal a).toNat :=
      Evm.step_cont_getBal_foreign step target sum_pre
    have hne : (pre.getCode a).toList ≠ [] := by
      rw [code]
      exact nonempty
    have hnext := Blanc.Exec.Deriv.ParentStep.codePreserve
      (Exec.Deriv.ParentStep.cont step next) a hne
    have hle := ih target (by rw [hnext]; exact code) committed
    exact Nat.le_trans hmono hle
  · intro pc sevm pre frame resume pc' result post out step enter resumed next ih target code committed
    obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
    obtain ⟨shape, hstate, -⟩ := Xinst.step_spawn_form spawn
    have runX : Xinst.Run sevm pre x .none (.ok post) := by
      unfold Xinst.Run
      rw [spawn]
      exact ⟨result, RunFrame.of_done enter, resumed.symm⟩
    have sum_pre : sum pre.state.bal < 2 ^ 256 :=
      sums (Exec.doneOk step enter resumed next)
    have hmono : (pre.state.bal a).toNat ≤ (post.state.bal a).toNat :=
      Xinst.foreignNone_getBal_mono runX target sum_pre
    have hne : (pre.getCode a).toList ≠ [] := by
      rw [code]
      exact nonempty
    have hnext := Blanc.Exec.Deriv.ParentStep.codePreserve
      (Exec.Deriv.ParentStep.doneOk step enter resumed next) a hne
    have hle := ih target (by rw [hnext]; exact code) committed
    exact Nat.le_trans hmono hle
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next settles childIH nextIH target code committed
    -- DRAFT: entry analysis resists. Needs a lane-aware entry-credit helper:
    -- from `Xinst.step_shape` (5 arms) get caller/value identities per arm
    -- (`callerShape`/`callShape` give caller = currentTarget or no-transfer,
    -- but staticcall-value-0 and delegatecall-target-preservation are
    -- unwritten), then `of_transfer_bal_target/other` under `sums` for the
    -- here case and `of_transfer_bal_other` for the far case; the no-transfer
    -- subcase at `a` needs the staticcall value-0 fact. At-`a` child via
    -- `at_code` (pc 0 by `step_spawn_child`), far child via `childIH`,
    -- resume via `ok_state_eq_committedPost`, then `nextIH`. Estimated 60-100
    -- lines with the helper.
    sorry
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next rolled nextIH target code committed
    -- DRAFT: needs a lane-aware rolled-entry helper
    -- `Evm.step_spawn_rolled_getBal`: call lane gives `post.state =
    -- pre.state` via `rollback_of_error` (names verified in
    -- `step_spawn_rolled_getStor`); create lane needs `m.benv.state.bal a =
    -- pre.state.bal a` through the creation prefix, i.e. a balance version of
    -- `create_access_getStor`/`create_collision_getStor` (Amsterdam prefix
    -- facts exist as instructionFrames; the per-lane assembly is unwritten).
    -- Then code via `codePreserve`, callers/`keptPaid` via the `keptAt`
    -- rewrite, close by the continuation IH. Estimated 30-50 lines.
    sorry

/-- **Covers the kept values.** Under the never-falls premises, with every kept
frame's caller away from the account, the post balance covers the pre balance
plus every kept frame's carried value. The caller premise excludes self-calls,
whose value moves from the account to itself. -/
theorem Exec.kept_bal_ge_keptPaid {C : ByteArray} {a : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) (target : sevm.currentTarget ≠ a)
    (code : pre.getCode a = C)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (sums : ∀ {q : Nat} {s : Sevm} {d : Devm} {o : Execution},
      Exec q s d o → SumNof d.state.bal)
    (at_code : ∀ {s : Sevm} {d e : Devm}, s.currentTarget = a →
      s.code = C → Exec 0 s d (.ok e) → (e.getBal a).toNat = (d.getBal a).toNat)
    (callers : ∀ f ∈ Exec.keptAt a run, f.sevm.caller ≠ a) :
    (pre.getBal a).toNat + Exec.keptPaid a run ≤
      ((Execution.committedPost out committed).getBal a).toNat := by
  refine Exec.retained_induction
    (P := fun _ sevm pre out run => sevm.currentTarget ≠ a → pre.getCode a = C →
      (∀ f ∈ Exec.keptAt a run, f.sevm.caller ≠ a) →
      ∀ (committed : Execution.commits out = true),
        (pre.getBal a).toNat + Exec.keptPaid a run ≤
          ((Execution.committedPost out committed).getBal a).toNat)
    ?_ ?_ ?_ ?_ ?_ run committed target code callers committed
  · intro pc sevm pre out step target code callers committed
    revert committed
    cases out with
    | error err =>
        intro committed
        simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post =>
        intro committed
        have sum_pre : sum pre.state.bal < 2 ^ 256 :=
          sums (Exec.halt step)
        have hpaid : Exec.keptPaid a (Exec.halt step) = 0 := by
          simp only [Exec.keptPaid, Exec.keptAt, List.map_nil, List.sum_nil]
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
                have hmono := Linst.targetBalanceMono_of_foreign run target sum_pre
                rw [hpaid, Nat.add_zero]
                exact hmono
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
  · intro pc sevm pre pc' post out step next ih target code callers committed
    have sum_pre : sum pre.state.bal < 2 ^ 256 :=
      sums (Exec.cont step next)
    have hmono : (pre.state.bal a).toNat ≤ (post.state.bal a).toNat :=
      Evm.step_cont_getBal_foreign step target sum_pre
    have hne : (pre.getCode a).toList ≠ [] := by
      rw [code]
      exact nonempty
    have hnext := Blanc.Exec.Deriv.ParentStep.codePreserve
      (Exec.Deriv.ParentStep.cont step next) a hne
    have hpaid : Exec.keptPaid a (Exec.cont step next) = Exec.keptPaid a next := by
      simp only [Exec.keptPaid, Exec.keptAt]
    have hcall : ∀ f ∈ Exec.keptAt a next, f.sevm.caller ≠ a := by
      rw [Exec.keptAt] at callers
      exact callers
    have hle := ih target (by rw [hnext]; exact code) hcall committed
    rw [hpaid]
    exact Nat.le_trans (Nat.add_le_add_right hmono _) hle
  · intro pc sevm pre frame resume pc' result post out step enter resumed next ih target code callers committed
    obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
    obtain ⟨shape, hstate, -⟩ := Xinst.step_spawn_form spawn
    have runX : Xinst.Run sevm pre x .none (.ok post) := by
      unfold Xinst.Run
      rw [spawn]
      exact ⟨result, RunFrame.of_done enter, resumed.symm⟩
    have sum_pre : sum pre.state.bal < 2 ^ 256 :=
      sums (Exec.doneOk step enter resumed next)
    have hmono : (pre.state.bal a).toNat ≤ (post.state.bal a).toNat :=
      Xinst.foreignNone_getBal_mono runX target sum_pre
    have hne : (pre.getCode a).toList ≠ [] := by
      rw [code]
      exact nonempty
    have hnext := Blanc.Exec.Deriv.ParentStep.codePreserve
      (Exec.Deriv.ParentStep.doneOk step enter resumed next) a hne
    have hpaid : Exec.keptPaid a (Exec.doneOk step enter resumed next) =
        Exec.keptPaid a next := by
      simp only [Exec.keptPaid, Exec.keptAt]
    have hcall : ∀ f ∈ Exec.keptAt a next, f.sevm.caller ≠ a := by
      rw [Exec.keptAt] at callers
      exact callers
    have hle := ih target (by rw [hnext]; exact code) hcall committed
    rw [hpaid]
    exact Nat.le_trans (Nat.add_le_add_right hmono _) hle
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next settles childIH nextIH target code callers committed
    -- DRAFT: same entry-analysis blocker as the never-falls committed-spawn
    -- leaf above (lane-aware caller/value identities, staticcall value-0,
    -- exact credit via `of_transfer_bal_target` under `sums`), plus `keptPaid`
    -- over the append and the `callers` split. At-`a` child via `at_code`,
    -- far child via `childIH`, resume via `ok_state_eq_committedPost`, then
    -- `nextIH` and omega. Estimated 60-100 lines with the helper.
    sorry
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next rolled nextIH target code callers committed
    -- DRAFT: same rolled-entry blocker as the never-falls rolled leaf above
    -- (`Evm.step_spawn_rolled_getBal`, call lane exact, create lane via a
    -- balance `create_access/collision` assembly), plus `keptPaid` over the
    -- `[] ++ rest` reduction and the `callers` transport. Estimated 30-50
    -- lines with the helper.
    sorry

end Blanc
