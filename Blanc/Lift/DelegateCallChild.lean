import Blanc.Lift.SpawnExact
import Blanc.Lift.StepMemory
import Blanc.Lift.InvWalk
import Blanc.MessageExecutionInversion

/-!
# A `DELEGATECALL` step, inverted to its child frame (contract-neutral)

`ri_delegatecall_child`: a successful `DELEGATECALL` step from the walk state
`St b (g :: w :: ii :: is :: oi :: os :: S) M G`, on a covered fork, whose code-address operand
names an undelegated account outside the precompile range, leaves a flag above `S`; a set flag
comes from a successful child derivation `Exec 0 csevm cpre (.ok x)` that runs `w`'s code on the
input window as calldata, from an empty machine over `b`'s code, under the frame's block statics,
and the step writes the prefix of the child's output into the output window.
-/

namespace Blanc.Lift

open Jaune Blanc

/-- A successful `DELEGATECALL` step is a `genericCall` step over the operand-free machine (stack
`S`, the step's memory) with its memory extended over the two windows. -/
theorem delegatecall_generic {sevm : Sevm} {d d' : Devm} {xl : Xlot}
    {g w ii is oi os : B256} {S : List B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hs : d.stack = g :: w :: ii :: is :: oi :: os :: S)
    (undelegated : getDelegatedCodeAddress (d.getCode w.toAdr) = none)
    (xrun : XStep.Run (Xinst.step sevm d .delegatecall) xl (.ok d')) :
    ∃ (v : Devm) (gas : Nat), v.stack = S ∧ v.memory = d.memory ∧ v.state = d.state ∧
      XStep.Run (genericCall.step sevm (v.memExtends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)])
        gas sevm.value sevm.caller sevm.currentTarget w.toAdr false false ii.toNat is.toNat oi.toNat
        os.toNat (d.getCode w.toAdr) false) xl (.ok d') := by
  have hacc : sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress (d.withStack S) w.toAdr)
      w.toAdr = ⟨false, w.toAdr, d.getCode w.toAdr, 0, addAccessedAddress (d.withStack S) w.toAdr⟩ := by
    dsimp only [GasSchedule.accessDelegation]
    rw [show (addAccessedAddress (d.withStack S) w.toAdr).state.getCode w.toAdr =
      d.getCode w.toAdr from rfl, undelegated]
  simp only [Xinst.step, hfork.rules_stateGas_none, Bind.bind, Except.bind,
    Devm.pop_cons hs, Devm.withStack_popToNat, Devm.withStack_popToAdr, hacc] at xrun
  split at xrun
  · cases XStep.run_ofExcept_error xrun
  rename_i v hc
  simp only [XStep.ofExcept, Pure.pure, Except.pure] at xrun
  have hb := Devm.burn_of_chargeGas hc
  refine ⟨v, _, ?_, ?_, ?_, xrun⟩
  · rw [← hb.stack]
    rfl
  · rw [← hb.memory]
    rfl
  · rw [← hb.state]
    rfl

/-- A call frame that moves no value into a non-precompile code address is entered. -/
theorem Frame.ofCall_enter_not_done {m : Msg} {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : (Frame.ofCall m).enter = .done r) (hstv : m.shouldTransferValue = false)
    (hdp : m.disablePrecompiles = false) {a : Adr} (hca : m.codeAddress = some a)
    (hnp : ¬ m.benv.stat.rules.isPrecomp a) : False := by
  simp only [Frame.enter, Frame.ofCall, Msg.benvAfterTransfer, hstv, Bool.false_eq_true,
    false_and, ↓reduceIte, executeCode.enter, Msg.withBenv, hca, hdp, Bool.not_false, Bool.true_and,
    decide_eq_true_eq, hnp, reduceCtorEq] at h

/-- **`DELEGATECALL`, inverted to its child.**  A successful step leaves a flag above `S`; a set
flag comes from a successful child derivation running `w`'s code on the input window, from an
empty machine over `b`'s code and the frame's block statics, and the output window holds the
prefix of the child's output. -/
theorem ri_delegatecall_child {sevm : Sevm} {b d : Devm} {g w ii is oi os : B256}
    {S : List B256} {M : Mem} {G : Nat} (hfork : CoveredFork sevm.benvStat.fork)
    (undelegated : getDelegatedCodeAddress (b.getCode w.toAdr) = none)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp w.toAdr)
    (run : Ninst.Run sevm (St b (g :: w :: ii :: is :: oi :: os :: S) M G) (.exec .delegatecall) d) :
    ∃ flag, d.stack = flag :: S ∧ (flag = 0 ∨ ∃ (csevm : Sevm) (cpre x : Devm),
      Nonempty (Exec 0 csevm cpre (.ok x)) ∧ csevm.code = b.getCode w.toAdr ∧
      csevm.data = (M.read ii.toNat is.toNat).1 ∧ csevm.benvStat = sevm.benvStat ∧
      cpre.memory = Mem.empty ∧ cpre.stack = [] ∧ (∀ a, cpre.getCode a = b.getCode a) ∧
      d.memory = (M.extends [(ii.toNat, is.toNat), (oi.toNat, os.toNat)]).write oi.toNat
        (x.output.take os.toNat)) := by
  obtain ⟨xl, filled, pc, stepRun⟩ := run
  have xrun : XStep.Run (Xinst.step sevm (St b (g :: w :: ii :: is :: oi :: os :: S) M G)
      .delegatecall) xl (.ok d) := by
    simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] using stepRun
  obtain ⟨v, gas, hvs, hvm, hvst, h⟩ := delegatecall_generic (d := St b (g :: w :: ii :: is :: oi :: os :: S) M G)
    hfork rfl undelegated xrun
  unfold genericCall.step at h
  split at h
  · simp only [Bind.bind, Except.bind] at h
    split at h
    · cases XStep.run_ofExcept_error h
    rename_i d1 hp
    obtain ⟨-, hd⟩ := h
    cases hd
    refine ⟨0, ?_, .inl rfl⟩
    have hps := (Devm.push_of_push hp).stack
    simp only [Stack.Push, Split, List.nil_append, List.cons_append] at hps
    rw [hps]
    exact congrArg _ hvs
  · obtain ⟨r, frun, hr⟩ := h
    rcases r with e | child
    · exact (Resume.call_run_error hr.symm).elim
    have hstk := Resume.call_stack_flag hr.symm
    have hmem := Resume.call_memory hr.symm
    by_cases herr : child.error.isSome
    · refine ⟨0, ?_, .inl rfl⟩
      rw [hstk, ite_eq_left herr]
      exact congrArg _ hvs
    refine ⟨1, ?_, .inr ?_⟩
    · rw [hstk, ite_eq_right herr]
      exact congrArg _ hvs
    cases xl with
    | none =>
      exfalso
      unfold RunFrame at frun
      split at frun
      · rename_i heq
        exact Frame.ofCall_enter_not_done heq rfl rfl rfl notPre
      · obtain ⟨_, h, _⟩ := frun
        cases h
    | some p =>
      obtain ⟨⟨cpc, csevm, cpre⟩, raw⟩ := p
      have clean : child.error.isSome = false := by
        simpa only [Bool.not_eq_true] using herr
      obtain ⟨x, hraw, -, -, hout⟩ := MessageExecution.processMessage_clean_rawPost frun clean
      obtain ⟨hpc, hcode, -, -, hdata, -, -⟩ :=
        MessageExecution.processMessage_entry_frame_facts frun
      have hst := MessageExecution.processMessage_entry_stack frun
      have hmm := MessageExecution.processMessage_entry_memory frun
      have hstat := RunFrame.benvStat_eq frun
      obtain ⟨benv, transfer, evmEq⟩ := Frame.enter_run_inv (RunFrame.some_inv frun).1
      have hcst := congrArg (fun e : Evm => e.dyna.state) evmEq
      subst hpc hraw
      obtain ⟨ex⟩ := filled
      refine ⟨csevm, cpre, x, ⟨ex⟩, hcode, ?_, hstat, hmm, hst, fun a => ?_, ?_⟩
      · rw [hdata]
        show Array.sliceD (v.memory.extends _).data _ _ 0 = _
        rw [hvm]
        rfl
      · dsimp only at hcst
        show cpre.state.getCode a = b.state.getCode a
        rw [hcst]
        show benv.state.getCode a = _
        rw [benvAfterTransfer_ok_getCode transfer a]
        show v.state.getCode a = _
        rw [hvst]
        rfl
      · rw [hmem, ← hout]
        show (v.memory.extends _).write _ _ = _
        rw [hvm]
        rfl

end Blanc.Lift
