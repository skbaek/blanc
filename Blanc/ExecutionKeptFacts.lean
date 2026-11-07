import Blanc.ExecutionKeptFrames
import Blanc.ExecutionCallerExclusion
import Blanc.ExecutionTraceCalldata

/-!
# What every kept frame enters with, and what a committing run leaves at the account

Rule-neutral companions of `ExecutionKeptFrames`. Nothing here reads `stateGas`, and no statement names a frame that
did not commit. The single rule premise, on `Exec.keptAccount`, is `selfdestructOnlyCreated`.
-/

namespace Blanc

open Jaune

/-! ## Entry facts of kept frames -/

/-- A spawned child has word-sized calldata in either lane: CALL-family inputs are memory slices sized by a popped word,
and CREATE-family inputs are empty. -/
theorem Xinst.step_spawn_inner_data_length_lt_neutral {sevm : Sevm} {pre : Devm} {x : Xinst} {frame : Frame}
    {resume : Resume} (spawn : Xinst.step sevm pre x = .spawn frame resume) : frame.inner.data.length < 2 ^ 256 := by
  have bound : ∀ {d d' : Devm} {n : Nat}, Devm.popToNat d = .ok ⟨n, d'⟩ → n < 2 ^ 256 := by
    intro d d' n pop
    obtain ⟨w, -, rfl⟩ := Devm.pop_of_popToNat_val pop
    exact B256.toNat_lt _
  have create : ∀ {d : Devm} {endowment : B256} {newAddress : Adr} {mi ms : Nat},
      genericCreate.step sevm d endowment newAddress mi ms = .spawn frame resume →
      frame.inner.data.length < 2 ^ 256 := by
    intro d endowment newAddress mi ms hs
    obtain ⟨rfl, -⟩ := genericCreate_step_spawn_exact hs
    change ([] : Bytes).length < 2 ^ 256
    decide
  have createAmsterdam : ∀ {state : StateGasRules} {d : Devm} {endowment : B256} {newAddress : Adr} {mi ms : Nat},
      genericCreateAmsterdam.step sevm state d endowment newAddress mi ms = .spawn frame resume →
      frame.inner.data.length < 2 ^ 256 := by
    intro state d endowment newAddress mi ms hs
    simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at hs
    repeat' split at hs
    all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
    all_goals obtain ⟨rfl, -⟩ := hs
    all_goals change ([] : Bytes).length < 2 ^ 256
    all_goals decide
  have call : ∀ {d : Devm} {gas : Nat} {value : B256} {caller target codeAddress : Adr} {stv isSt : Bool}
      {ii isz oi osz : Nat} {code : ByteArray} {dp : Bool},
      genericCall.step sevm d gas value caller target codeAddress stv isSt ii isz oi osz code dp =
        .spawn frame resume → isz < 2 ^ 256 → frame.inner.data.length < 2 ^ 256 := by
    intro d gas value caller target codeAddress stv isSt ii isz oi osz code dp hs size
    obtain ⟨rfl, -⟩ := genericCall_step_spawn_exact hs
    change (Array.sliceD _ ii isz 0).length < 2 ^ 256
    rw [ExecutionTrace.Array.sliceD_length]
    exact size
  have callAmsterdam : ∀ {state : StateGasRules} {d : Devm} {gas reservoir : Nat} {value : B256}
      {caller target codeAddress : Adr} {stv isSt : Bool} {ii isz oi osz : Nat} {code : ByteArray} {dp nac ib : Bool},
      genericCallAmsterdam.step sevm state d gas reservoir value caller target codeAddress stv isSt ii isz oi osz code
        dp nac ib = .spawn frame resume → isz < 2 ^ 256 → frame.inner.data.length < 2 ^ 256 := by
    intro state d gas reservoir value caller target codeAddress stv isSt ii isz oi osz code dp nac ib hs size
    obtain ⟨rfl, -⟩ := genericCallAmsterdam_step_spawn_exact hs
    change (Array.sliceD _ ii isz 0).length < 2 ^ 256
    rw [ExecutionTrace.Array.sliceD_length]
    exact size
  cases x <;> simp only [Xinst.step, Bind.bind, Except.bind, Except.assert, Pure.pure, Except.pure] at spawn
  all_goals repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | solve | cases spawn
    | exact create spawn
    | exact createAmsterdam spawn
    | exact call spawn (by solve_by_elim [bound])
    | exact callAmsterdam spawn (by solve_by_elim [bound])

/-- What a frame kept at `a` enters with: from the start of the account's code, with fresh machine state and the
environment of the run it was kept from. -/
structure Exec.Frame.EntryAt (a : Adr) (C : ByteArray) (base : BenvStat) (f : Exec.Frame) : Prop where
  pc : f.pc = 0
  target : f.sevm.currentTarget = a
  code : f.sevm.code = C
  stack : f.pre.stack = []
  memorySize : f.pre.memory.size % 32 = 0
  memoryWf : Mem.Wf f.pre.memory
  benvStat : f.sevm.benvStat = base
  dataLength : f.sevm.data.length < 2 ^ 256

/-- **Entry facts.** Over a committing run of a frame not at `a`, where `a` holds nondelegating code `C`, every kept
frame at `a` runs `C` from its start on fresh machine state, under the run's own environment. -/
theorem Exec.keptAt_entry {a : Adr} {C : ByteArray} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) (target : sevm.currentTarget ≠ a)
    (code : pre.getCode a = C) (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C) :
    ∀ f ∈ Exec.keptAt a run, Exec.Frame.EntryAt a C sevm.benvStat f := by
  revert target code
  refine Exec.retained_induction
    (P := fun _ sevm pre _ run => sevm.currentTarget ≠ a → pre.getCode a = C →
      ∀ f ∈ Exec.keptAt a run, Exec.Frame.EntryAt a C sevm.benvStat f)
    ?_ ?_ ?_ ?_ ?_ run committed
  · intro pc sevm pre out step _ _ f member
    simp only [Exec.keptAt, List.not_mem_nil] at member
  · intro pc sevm pre pc' post out step next ih target code f member
    rw [Exec.keptAt] at member
    have keep := Blanc.Exec.Deriv.ParentStep.codePreserve (Exec.Deriv.ParentStep.cont step next) a
      (by change (pre.getCode a).toList ≠ []; rw [code]; exact nonempty)
    exact ih target (Eq.trans keep code) f member
  · intro pc sevm pre frame resume pc' result post out step enter resumed next ih target code f member
    rw [Exec.keptAt] at member
    have keep := Blanc.Exec.Deriv.ParentStep.codePreserve (Exec.Deriv.ParentStep.doneOk step enter resumed next) a
      (by change (pre.getCode a).toList ≠ []; rw [code]; exact nonempty)
    exact ih target (Eq.trans keep code) f member
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next settles childIH nextIH
      target code f member
    have keep := Blanc.Exec.Deriv.ParentStep.codePreserve (Exec.Deriv.ParentStep.runOk step enter child resumed next) a
      (by change (pre.getCode a).toList ≠ []; rw [code]; exact nonempty)
    obtain ⟨pcZero, childCode, source⟩ := Evm.step_spawn_child step enter
    have stat := Evm.step_spawn_child_benvStat step enter
    rw [Exec.keptAt, dite_eq_left settles, List.mem_append] at member
    rcases member with member | member
    · by_cases here : childEvm.sta.currentTarget = a
      · rw [ite_eq_left here, List.mem_singleton] at member
        subst member
        have fresh := Frame.enter_run_fresh enter
        refine ⟨pcZero, here, ?_, fresh.1, ?_, ?_, stat, ?_⟩
        · have equal := source (by rw [here]; exact target)
            (by rw [here, code]; intro empty; subst empty; exact nonempty ByteArray.toList_empty)
            (by rw [here, code]; exact nondelegating)
          change childEvm.sta.code = C
          rw [equal, here, code]
        · change childEvm.dyna.memory.size % 32 = 0
          rw [fresh.2]
          rfl
        · change Mem.Wf childEvm.dyna.memory
          rw [fresh.2]
          exact Mem.wf_empty
        · obtain ⟨x, -, instruction, -⟩ := Evm.step_spawn_inv step
          change childEvm.sta.data.length < 2 ^ 256
          rw [ExecutionTrace.Frame.enter_data_eq enter]
          exact Xinst.step_spawn_inner_data_length_lt_neutral instruction
      · rw [ite_eq_right here] at member
        have below := childIH here ((childCode a).trans code) f member
        rw [stat] at below
        exact below
    · exact nextIH target (Eq.trans keep code) f member
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next rolled nextIH
      target code f member
    have keep := Blanc.Exec.Deriv.ParentStep.codePreserve (Exec.Deriv.ParentStep.runOk step enter child resumed next) a
      (by change (pre.getCode a).toList ≠ []; rw [code]; exact nonempty)
    rw [Exec.keptAt, dite_eq_right rolled, List.nil_append] at member
    exact nextIH target (Eq.trans keep code) f member

/-- Every kept frame is a retained descendant of the run it was kept from. -/
theorem Exec.mem_descendantFrames_of_mem_keptAt {a : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) {f : Exec.Frame} (member : f ∈ Exec.keptAt a run) :
    f ∈ Exec.descendantFrames run := by
  induction run with
  | halt step => simp only [Exec.keptAt, List.not_mem_nil] at member
  | cont step next ih =>
      rw [Exec.keptAt] at member
      rw [Exec.descendantFrames]
      exact ih member
  | doneErr step enter resumed => simp only [Exec.keptAt, List.not_mem_nil] at member
  | doneOk step enter resumed next ih =>
      rw [Exec.keptAt] at member
      rw [Exec.descendantFrames]
      exact ih member
  | runErr step enter child resumed ih => simp only [Exec.keptAt, List.not_mem_nil] at member
  | @runOk pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next childIH nextIH =>
      by_cases settles : Frame.settlementCommits frame raw = true
      · rw [Exec.keptAt, dite_eq_left settles, List.mem_append] at member
        rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resumed next settles, List.mem_append,
          List.mem_cons]
        rcases member with member | member
        · by_cases here : childEvm.sta.currentTarget = a
          · rw [ite_eq_left here, List.mem_singleton] at member
            exact Or.inl (Or.inl member)
          · rw [ite_eq_right here] at member
            exact Or.inl (Or.inr (childIH member))
        · exact Or.inr (nextIH member)
      · rw [Exec.keptAt, dite_eq_right settles, List.nil_append] at member
        rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resumed next settles]
        exact nextIH member

/-! ## The account stays out of both sets, for every rule record -/

/-- The Amsterdam CALL return path keeps the account out of both sets. -/
theorem Resume.callAmsterdam_noDel {wa : Adr} {state : StateGasRules} {parent : Devm} {oi os : Nat} {nac : Bool}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} (hnd : Devm.NoDel wa parent) (h : MsgResult.NoDel wa r) :
    Execution.NoDel wa ((Resume.callAmsterdam state parent oi os nac).run r) := by
  have key : ∀ {d : Devm} (v : B256) (o : Bytes), Devm.NoDel wa d →
      Execution.NoDel wa (d.push v >>= fun d' => .ok (d'.memWrite oi o)) := by
    intro d v o hd
    rcases hp : d.push v with e | pushed
    · exact Devm.push_noDel hp hd
    · have below : Devm.NoDel wa pushed := Devm.push_noDel hp hd
      exact Devm.NoDel.of_instructionFrame (Devm.memWrite_instructionFrame pushed oi o) below
  unfold Resume.run liftToExecution
  rcases r with ⟨err, st, created, tra⟩ | child <;> dsimp only [bind, Except.bind, Except.assert]
  · rcases h with ⟨hca, hcode⟩
    exact ⟨hnd.atd, hca, hcode⟩
  · have hChild : Devm.NoDel wa child := h
    have failed : Devm.NoDel wa (incorporateChildAmsterdamOnError parent child child.output) :=
      ⟨hnd.atd, hChild.ca, hChild.code⟩
    have clean : Devm.NoDel wa (incorporateChildAmsterdamOnSuccess parent child child.output) :=
      ⟨AdrSet.not_mem_union hnd.atd hChild.atd, hChild.ca, hChild.code⟩
    split
    · by_cases hP : child.AmsterdamFailedChildSettled
      · rw [ite_eq_left hP]
        dsimp only
        by_cases hnac : nac = true
        · rw [ite_eq_left hnac]
          exact key 0 _ ⟨failed.atd, failed.ca, failed.code⟩
        · rw [ite_eq_right hnac]
          exact key 0 _ failed
      · rw [ite_eq_right hP]
        exact hChild
    · by_cases hP : child.AmsterdamChildUncommitted
      · rw [ite_eq_left hP]
        exact key 1 _ clean
      · rw [ite_eq_right hP]
        exact hChild

/-- The Amsterdam CREATE return path keeps the account out of both sets. -/
theorem Resume.createAmsterdam_noDel {wa : Adr} {state : StateGasRules} {parent : Devm} {newAddress : Adr} {nac : Bool}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} (hnd : Devm.NoDel wa parent) (h : MsgResult.NoDel wa r) :
    Execution.NoDel wa ((Resume.createAmsterdam state parent newAddress nac).run r) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, st, created, tra⟩ | child <;> dsimp only [bind, Except.bind, Except.assert]
  · rcases h with ⟨hca, hcode⟩
    exact ⟨hnd.atd, hca, hcode⟩
  · have hChild : Devm.NoDel wa child := h
    have failed : Devm.NoDel wa (incorporateChildAmsterdamOnError parent child child.output) :=
      ⟨hnd.atd, hChild.ca, hChild.code⟩
    have clean : Devm.NoDel wa (incorporateChildAmsterdamOnSuccess parent child []) :=
      ⟨AdrSet.not_mem_union hnd.atd hChild.atd, hChild.ca, hChild.code⟩
    split
    · by_cases hP : child.AmsterdamFailedChildSettled
      · rw [ite_eq_left hP]
        dsimp only
        by_cases hnac : nac = true
        · rw [ite_eq_left hnac]
          exact Devm.push_noDel rfl ⟨failed.atd, failed.ca, failed.code⟩
        · rw [ite_eq_right hnac]
          exact Devm.push_noDel rfl failed
      · rw [ite_eq_right hP]
        exact hChild
    · by_cases hP : child.AmsterdamChildUncommitted
      · rw [ite_eq_left hP]
        exact Devm.push_noDel rfl clean
      · rw [ite_eq_right hP]
        exact hChild

/-- The Amsterdam CALL family keeps the account out of both sets, given that its child does. -/
theorem GenericCallAmsterdam.inv_noDel {wa : Adr} {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {gas reservoir : Nat} {value : B256} {caller target codeAddress : Adr} {stv isSt : Bool} {ii isz oi osz : Nat}
    {code : ByteArray} {dp nac ib : Bool} {xl : Xlot} {exn : Execution} (inv : Xlot.InvNoDel wa xl)
    (run : GenericCallAmsterdam sevm state devm gas reservoir value caller target codeAddress stv isSt ii isz oi osz
      code dp nac ib xl exn)
    (hnd : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  unfold GenericCallAmsterdam genericCallAmsterdam.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    by_cases hnac : nac = true
    · rw [ite_eq_left hnac] at heq
      exact Devm.push_noDel heq ⟨hnd.atd, hnd.ca, hnd.code⟩
    · rw [ite_eq_right hnac] at heq
      exact Devm.push_noDel heq ⟨hnd.atd, hnd.ca, hnd.code⟩
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    by_cases hnac : nac = true
    · rw [ite_eq_left hnac] at heq
      exact Devm.push_noDel heq ⟨hnd.atd, hnd.ca, hnd.code⟩
    · rw [ite_eq_right hnac] at heq
      exact Devm.push_noDel heq ⟨hnd.atd, hnd.ca, hnd.code⟩
  · obtain ⟨r, hframe, rfl⟩ := run
    exact Resume.callAmsterdam_noDel ⟨hnd.atd, hnd.ca, hnd.code⟩
      (ProcessMessage.inv_noDel inv hframe ⟨hnd.ca, hnd.code⟩ (by
        dsimp only [callMsg]
        split
        · exact AdrSet.not_mem_empty
        · exact hnd.atd))

/-- The Amsterdam CREATE family keeps the account out of both sets, given that its child does. Its target is never
the account: the collision check runs on the account's actual code. -/
theorem GenericCreateAmsterdam.inv_noDel {wa : Adr} {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat} {xl : Xlot} {exn : Execution} (inv : Xlot.InvNoDel wa xl)
    (run : GenericCreateAmsterdam sevm state devm endowment newAddress mi ms xl exn)
    (hnd : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  have h1 : Devm.NoDel wa (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (devm.withReturnData [])) :=
    Devm.NoDel.of_instructionFrame (Devm.balReadAccount_instructionFrame _ _ _) ⟨hnd.atd, hnd.ca, hnd.code⟩
  have h2 : Devm.NoDel wa (Devm.balReadAccount sevm.benvStat.rules newAddress (addAccessedAddress
      (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (devm.withReturnData [])) newAddress)) :=
    Devm.NoDel.of_instructionFrame (Devm.balReadAccount_instructionFrame _ _ _) (Devm.NoDel.addAccessedAddress h1)
  have after : ∀ {v : Devm}, Devm.NoDel wa v →
      Devm.NoDel wa (v.withholdCreateGas.2.incrNonce sevm.currentTarget) ∧
      Devm.NoDel wa (v.withholdCreateGas.2.drainStateGasReservoir.2.incrNonce sevm.currentTarget) := by
    intro v hv
    refine ⟨Devm.NoDel.of_eqs (d := v) rfl ?_ hv, Devm.NoDel.of_eqs (d := v) rfl ?_ hv⟩
    · rw [Devm.incrNonce_getCode, Devm.withholdCreateGas_getCode]
    · rw [Devm.incrNonce_getCode, Devm.drainStateGasReservoir_getCode, Devm.withholdCreateGas_getCode]
  have enterChild : ∀ {v : Devm} (g r : Nat) {calldata : Bytes} {nacd : Bool} {result}, Devm.NoDel wa v →
      (Xlot.InvNoDel wa xl) →
      ¬ ((v.withholdCreateGas.2.state.get newAddress).nonce ≠ (0 : UInt64) ∨
        (v.withholdCreateGas.2.state.get newAddress).code.size ≠ 0) →
      ProcessCreateMessage { createMsg sevm (v.withholdCreateGas.2.drainStateGasReservoir.2.incrNonce sevm.currentTarget)
        g endowment newAddress calldata with stateGasGrant := r } xl result →
      Execution.NoDel wa ((Resume.createAmsterdam state
        (v.withholdCreateGas.2.drainStateGasReservoir.2.incrNonce sevm.currentTarget) newAddress nacd).run result) := by
    intro v g r calldata nacd result hv hinv hnc hframe
    have hp := (after hv).2
    have hw : Devm.NoDel wa v.withholdCreateGas.2 :=
      Devm.NoDel.of_eqs (d := v) rfl Devm.withholdCreateGas_getCode.symm hv
    have hct : newAddress ≠ wa := by
      push Not at hnc
      exact ne_wa_of_code_size_zero hw.code hnc.2
    exact Resume.createAmsterdam_noDel hp
      (ProcessCreateMessage.inv_noDel hinv hframe hct ⟨hp.ca, hp.code⟩ (by
        dsimp only [createMsg]
        split
        · exact AdrSet.not_mem_empty
        · exact hp.atd))
  unfold GenericCreateAmsterdam genericCreateAmsterdam.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  all_goals first
    | obtain ⟨-, rfl⟩ := run
      rename_i heq
      exact Devm.push_noDel heq h1
    | obtain ⟨-, rfl⟩ := run
      rename_i heq
      exact Devm.NoDel.of_eqs (chargeStateGas_delSets_err heq).symm
        ((chargeStateGas_worldEq_of_error heq).getCode wa) h2
    | obtain ⟨-, rfl⟩ := run
      rename_i v hchg _ _ _ hpush
      exact Devm.push_noDel hpush (after (Devm.NoDel.of_eqs (chargeStateGas_delSets_eq hchg).symm
        ((chargeStateGas_worldEq_of_ok hchg).getCode wa) h2)).1
    | obtain ⟨-, rfl⟩ := run
      rename_i hpush
      exact Devm.push_noDel hpush (after h2).1
    | refine Exists.elim run (fun r hr => ?_)
      obtain ⟨hframe, rfl⟩ := hr
      rename_i v hchg hnc
      exact enterChild _ _ (Devm.NoDel.of_eqs (chargeStateGas_delSets_eq hchg).symm
        ((chargeStateGas_worldEq_of_ok hchg).getCode wa) h2) inv hnc hframe
    | refine Exists.elim run (fun r hr => ?_)
      obtain ⟨hframe, rfl⟩ := hr
      rename_i hnc
      exact enterChild _ _ h2 inv hnc hframe

/-- A call-type instruction keeps the account out of both sets, given that its child does. -/
theorem Xinst.inv_noDel_neutral {wa : Adr} {sevm : Sevm} {pre : Devm} {x : Xinst} {xl : Xlot} {exn : Execution}
    (inv : Xlot.InvNoDel wa xl) (run : Xinst.Run sevm pre x xl exn) (hnd : Devm.NoDel wa pre) :
    Execution.NoDel wa exn := by
  unfold Xinst.Run at run
  rcases Xinst.step_shape sevm pre x with ⟨ex, shape, hframe⟩ |
      ⟨d, endowment, newAddress, mi, ms, hf, shape⟩ |
      ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
        ii, isz, oi, osz, code, delegated, hf, -, -, -, shape⟩ |
      ⟨d, state, endowment, newAddress, mi, ms, hf, shape⟩ |
      ⟨d, d₀, state, gas, reservoir, value, caller, target, codeAddress,
        stv, isSt, ii, isz, oi, osz, code, dp, nac, ib, hf, -, -, -, shape⟩ <;>
    rw [shape] at run
  · obtain ⟨-, rfl⟩ := run
    exact Execution.NoDel.of_instructionFrame hframe hnd
  · exact GenericCreate.inv_noDel inv run (Devm.NoDel.of_instructionFrame hf hnd)
  · exact GenericCall.inv_noDel inv run (Devm.NoDel.of_instructionFrame hf hnd)
  · exact GenericCreateAmsterdam.inv_noDel inv run (Devm.NoDel.of_instructionFrame hf hnd)
  · exact GenericCallAmsterdam.inv_noDel inv run (Devm.NoDel.of_instructionFrame hf hnd)

/-- One interpreter step keeps the account out of both sets, given that its child does. -/
theorem Evm.step_noDel_neutral {wa : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {slot : Xlot} {out : Execution}
    (flag : sevm.benvStat.rules.settle.selfdestructOnlyCreated = true) (hnd : Devm.NoDel wa pre)
    (inv : Xlot.InvNoDel wa slot) (run : Step.Run (Evm.step ⟨pc, sevm, pre⟩) slot out) :
    Execution.NoDel wa out := by
  have hIR : ∀ ⦃d d' : Devm⦄, Devm.InstructionFrame d d' → Devm.NoDelCode wa d d' :=
    fun _ _ frame h => Devm.NoDel.of_instructionFrame frame h
  have ofRel : ∀ {o : Execution}, Execution.Rel (Devm.NoDelCode wa) pre o → Execution.NoDel wa o := by
    intro o rel
    cases o with
    | error e => exact rel hnd
    | ok d => exact rel hnd
  rcases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with _ | instruction
  · rw [Evm.step_invOp decoded] at run
    obtain ⟨-, rfl⟩ := run
    exact hnd
  · cases instruction with
    | next n =>
      rw [Evm.step_next (n := n) decoded] at run
      cases n with
      | reg regular =>
        simp only [Ninst.step_reg, Step.run_ofExecution] at run
        obtain ⟨-, rfl⟩ := run
        cases result : Rinst.run ⟨pc, sevm, pre⟩ regular with
        | error err =>
          exact Devm.NoDel.of_eqs (Rinst.inv_delSets_err result).symm (Rinst.preserves_getCode_err result wa).symm hnd
        | ok d => exact Devm.NoDel.of_eqs (Rinst.inv_delSets result) (Rinst.preserves_getCode result wa).symm hnd
      | exec executable =>
        simp only [Ninst.step_exec, XStep.run_toStep] at run
        exact Xinst.inv_noDel_neutral inv run hnd
      | push bytes bound =>
        have empty : slot = .none := by
          simp only [Ninst.step_push] at run
          split at run <;> simp only [Step.run_ofExecution] at run <;> exact run.1
        subst empty
        exact Execution.NoDel.of_instructionFrame
          (Ninst.push_instructionFrame_effectRec (hxs := bound) (xl := .none) trivial run) hnd
      | dupn imm =>
        have empty : slot = .none := by
          simp only [Ninst.step_dupn, Step.run_ofExecution] at run
          exact run.1
        subst empty
        exact Execution.NoDel.of_instructionFrame (Ninst.dupn_instructionFrame_effectRec (xl := .none) trivial run) hnd
      | swapn imm =>
        have empty : slot = .none := by
          simp only [Ninst.step_swapn, Step.run_ofExecution] at run
          exact run.1
        subst empty
        exact Execution.NoDel.of_instructionFrame (Ninst.swapn_instructionFrame_effectRec (xl := .none) trivial run) hnd
      | exchange imm =>
        have empty : slot = .none := by
          simp only [Ninst.step_exchange, Step.run_ofExecution] at run
          exact run.1
        subst empty
        exact Execution.NoDel.of_instructionFrame
          (Ninst.exchange_instructionFrame_effectRec (xl := .none) trivial run) hnd
    | jump j =>
      rw [Evm.step_jump (j := j) decoded] at run
      obtain ⟨-, hcase⟩ := Step.run_ofJump run
      have effect := Jinst.noDelCode_effect wa j (evm := ⟨pc, sevm, pre⟩) (out := j.run ⟨pc, sevm, pre⟩) rfl
      rcases hcase with ⟨e, hje, rfl⟩ | ⟨pc', d, hje, rfl⟩ <;> rw [hje] at effect <;> exact effect hnd
    | last l =>
      rw [Evm.step_last (l := l) decoded] at run
      obtain ⟨-, rfl⟩ := run
      exact Linst.inv_noDel rfl hnd flag

/-- **A run under EIP-6780 keeps a code-bearing account out of both sets, on either outcome.** This covers every child
below it, committed or not: a rolled-back child has run under the same invariant, since no CREATE reaches a code-bearing
account and SELFDESTRUCT schedules only a created one. -/
theorem Exec.inv_noDel_neutral {wa : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (flag : sevm.benvStat.rules.settle.selfdestructOnlyCreated = true)
    (hnd : Devm.NoDel wa pre) : Execution.NoDel wa out := by
  revert flag hnd
  induction run with
  | halt step =>
      intro flag hnd
      exact Evm.step_noDel_neutral (slot := .none) flag hnd trivial (by rw [step]; exact ⟨rfl, rfl⟩)
  | cont step next ih =>
      intro flag hnd
      exact ih flag (Evm.step_noDel_neutral (slot := .none) (out := .ok _) flag hnd trivial
        (by rw [step]; exact ⟨rfl, rfl⟩))
  | doneErr step enter resumed =>
      intro flag hnd
      exact Evm.step_noDel_neutral (slot := .none) flag hnd trivial
        (by rw [step]; exact ⟨_, RunFrame.of_done enter, resumed.symm⟩)
  | doneOk step enter resumed next ih =>
      intro flag hnd
      exact ih flag (Evm.step_noDel_neutral (slot := .none) (out := .ok _) flag hnd trivial
        (by rw [step]; exact ⟨_, RunFrame.of_done enter, resumed.symm⟩))
  | runErr step enter child resumed childIH =>
      intro flag hnd
      exact Evm.step_noDel_neutral (slot := .some ⟨_, _⟩) flag hnd
        (childIH (by rw [Evm.step_spawn_child_benvStat step enter]; exact flag))
        (by rw [step]; exact ⟨_, RunFrame.of_run enter, resumed.symm⟩)
  | runOk step enter child resumed next childIH nextIH =>
      intro flag hnd
      exact nextIH flag (Evm.step_noDel_neutral (slot := .some ⟨_, _⟩) (out := .ok _) flag hnd
        (childIH (by rw [Evm.step_spawn_child_benvStat step enter]; exact flag))
        (by rw [step]; exact ⟨_, RunFrame.of_run enter, resumed.symm⟩))

/-- **Not deleted.** A committing run under EIP-6780 leaves a code-bearing account, neither created nor scheduled when
it starts, out of both sets. -/
theorem Exec.keptAccount {a : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) (code : (pre.getCode a).toList ≠ [])
    (notCreated : a ∉ pre.createdAccounts) (notDeleted : a ∉ pre.accountsToDelete)
    (flag : sevm.benvStat.rules.settle.selfdestructOnlyCreated = true) :
    a ∉ (Execution.committedPost out committed).createdAccounts ∧
      a ∉ (Execution.committedPost out committed).accountsToDelete := by
  have invariant := Exec.inv_noDel_neutral run flag ⟨notDeleted, notCreated, code⟩
  cases out with
  | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
      have kept : Devm.NoDel a post := invariant
      exact ⟨kept.ca, kept.atd⟩

/-! ## Caller exclusion, for every rule record -/

/-- CREATE and CREATE2 enter a frame with no code address, in either lane. -/
theorem Xinst.step_create_spawn_codeAddress_neutral {sevm : Sevm} {pre : Devm} {x : Xinst} {frame : Frame}
    {resume : Resume} (create : x = .create ∨ x = .create2) (spawn : Xinst.step sevm pre x = .spawn frame resume) :
    frame.inner.codeAddress = none := by
  have amsterdam : ∀ {state : StateGasRules} {d : Devm} {endowment : B256} {newAddress : Adr} {mi ms : Nat},
      genericCreateAmsterdam.step sevm state d endowment newAddress mi ms = .spawn frame resume →
      frame.inner.codeAddress = none := by
    intro state d endowment newAddress mi ms hs
    simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at hs
    repeat' split at hs
    all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
    all_goals obtain ⟨rfl, -⟩ := hs
    all_goals rfl
  rcases create with rfl | rfl <;>
    simp only [Xinst.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at spawn
  all_goals repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | solve | cases spawn
    | exact genericCreate.step_spawn_codeAddress spawn
    | exact amsterdam spawn

/-- A frame flagged as a creation has no code address, in either lane. -/
theorem Xinst.step_spawn_create_codeAddress_neutral {sevm : Sevm} {pre : Devm} {x : Xinst} {frame : Frame}
    {resume : Resume} (spawn : Xinst.step sevm pre x = .spawn frame resume) (isCreate : frame.isCreate = true) :
    frame.inner.codeAddress = none := by
  rcases Xinst.step_shape sevm pre x with ⟨ex, shape, -⟩ |
      ⟨d, endowment, newAddress, mi, ms, -, shape⟩ |
      ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
        ii, isz, oi, osz, code, delegated, -, -, -, -, shape⟩ |
      ⟨d, state, endowment, newAddress, mi, ms, -, shape⟩ |
      ⟨d, d₀, state, gas, reservoir, value, caller, target, codeAddress,
        stv, isSt, ii, isz, oi, osz, code, dp, nac, ib, -, -, -, -, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · exact genericCreate.step_spawn_codeAddress spawn
  · exact absurd (genericCall.step_spawn_isCreate_false spawn ▸ isCreate) Bool.false_ne_true
  · simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at spawn
    repeat' split at spawn
    all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at spawn
    all_goals obtain ⟨rfl, -⟩ := spawn
    all_goals rfl
  · obtain ⟨rfl, -⟩ := genericCallAmsterdam_step_spawn_exact spawn
    exact absurd isCreate Bool.false_ne_true

/-- One entered child keeps the caller away from `a`, and empty code at `a`. -/
theorem Evm.step_spawn_caller_excluded_neutral {a : Adr} {pc nextPc : Nat} {sevm : Sevm} {pre : Devm} {frame : Frame}
    {resume : Resume} {child : Evm} (spawn : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume nextPc)
    (enter : frame.enter = .run child) (caller : sevm.caller ≠ a)
    (targetCode : sevm.currentTarget = a → sevm.code = ByteArray.empty)
    (childEmpty : child.dyna.getCode a = ByteArray.empty)
    (avoid : child.sta.codeAddress = none → child.sta.currentTarget ≠ a) :
    child.sta.caller ≠ a ∧ (child.sta.currentTarget = a → child.sta.code = ByteArray.empty) := by
  have parentTarget : sevm.currentTarget ≠ a := fun eq => Evm.step_empty_code_not_spawn (targetCode eq) spawn
  obtain ⟨x, _, instruction, _⟩ := Evm.step_spawn_inv spawn
  have childCaller : child.sta.caller ≠ a := by
    rw [Frame.enter_run_caller enter]
    rcases Xinst.step_spawn_caller_parent_or_inherited instruction with parent | inherited
    · rw [parent]
      exact parentTarget
    · rw [inherited]
      exact caller
  refine ⟨childCaller, fun target => ?_⟩
  have emptyAt : pre.getCode a = ByteArray.empty := by
    rw [← (Evm.step_spawn_child spawn enter).2.1 a]
    exact childEmpty
  have frameTarget : frame.inner.currentTarget = a := (Frame.enter_run_currentTarget enter).symm.trans target
  cases x with
  | create =>
    exact False.elim (avoid (by
      rw [Frame.enter_run_codeAddress enter]
      exact Xinst.step_create_spawn_codeAddress_neutral (Or.inl rfl) instruction) target)
  | create2 =>
    exact False.elim (avoid (by
      rw [Frame.enter_run_codeAddress enter]
      exact Xinst.step_create_spawn_codeAddress_neutral (Or.inr rfl) instruction) target)
  | call =>
    rw [Frame.enter_run_code enter,
      Xinst.step_directCall_spawn_code (Or.inl rfl) instruction (by
        rw [frameTarget, emptyAt]
        decide), frameTarget, emptyAt]
  | staticcall =>
    rw [Frame.enter_run_code enter,
      Xinst.step_directCall_spawn_code (Or.inr rfl) instruction (by
        rw [frameTarget, emptyAt]
        decide), frameTarget, emptyAt]
  | callcode =>
    exact False.elim (parentTarget ((Xinst.step_spawn_context_target (Or.inl rfl) instruction).symm.trans frameTarget))
  | delegatecall =>
    exact False.elim (parentTarget ((Xinst.step_spawn_context_target (Or.inr rfl) instruction).symm.trans frameTarget))

/-- The Amsterdam CALL family keeps the code at `a`, given that its child does. -/
theorem GenericCallAmsterdam.codeAt {a : Adr} {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {gas reservoir : Nat} {value : B256} {caller target codeAddress : Adr} {stv isSt : Bool} {ii isz oi osz : Nat}
    {code : ByteArray} {dp nac ib : Bool} {xl : Xlot} {exn : Execution} (inv : Xlot.InvAt a xl)
    (run : GenericCallAmsterdam sevm state devm gas reservoir value caller target codeAddress stv isSt ii isz oi osz
      code dp nac ib xl exn) :
    Execution.getCode exn a = devm.getCode a := by
  unfold GenericCallAmsterdam genericCallAmsterdam.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    by_cases hnac : nac = true
    · rw [ite_eq_left hnac] at heq
      rw [Devm.push_getCode_gen heq a, Devm.creditStateGasRefund_getCode, Devm.restoreChildGas_getCode]
      rfl
    · rw [ite_eq_right hnac] at heq
      rw [Devm.push_getCode_gen heq a, Devm.restoreChildGas_getCode]
      rfl
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    by_cases hnac : nac = true
    · rw [ite_eq_left hnac] at heq
      rw [Devm.push_getCode_gen heq a, Devm.creditStateGasRefund_getCode, Devm.restoreChildGas_getCode]
      rfl
    · rw [ite_eq_right hnac] at heq
      rw [Devm.push_getCode_gen heq a, Devm.restoreChildGas_getCode]
      rfl
  · obtain ⟨r, hframe, rfl⟩ := run
    have result := ProcessMessage.codeAt inv hframe
    rw [callMsgAmsterdam_benv_state_getCode] at result
    exact (Resume.callAmsterdam_accountPreserve (track := false) result (by
      intro impossible
      cases impossible)).1

/-- The Amsterdam CREATE family keeps the code at `a`, given that its child does and that the frame it enters does not
target `a`. -/
theorem GenericCreateAmsterdam.codeAt {a : Adr} {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat} {xl : Xlot} {exn : Execution}
    (hne : ∀ f rsm cevm, genericCreateAmsterdam.step sevm state devm endowment newAddress mi ms = .spawn f rsm →
      f.enter = .run cevm → a ≠ newAddress)
    (inv : Xlot.InvAt a xl)
    (run : GenericCreateAmsterdam sevm state devm endowment newAddress mi ms xl exn) :
    Execution.getCode exn a = devm.getCode a := by
  have parentCode : ∀ {v : Devm}, v.getCode a = devm.getCode a →
      (v.withholdCreateGas.2.drainStateGasReservoir.2.incrNonce sevm.currentTarget).getCode a = devm.getCode a := by
    intro v hv
    rw [Devm.incrNonce_getCode, Devm.drainStateGasReservoir_getCode, Devm.withholdCreateGas_getCode, hv]
  have read : (Devm.balReadAccount sevm.benvStat.rules newAddress (addAccessedAddress
      (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget (devm.withReturnData [])) newAddress)).getCode a =
      devm.getCode a := by
    rw [Devm.balReadAccount_getCode, addAccessedAddress_getCode, Devm.balReadAccount_getCode]
    rfl
  have result : ∀ {m : Msg} {nacd : Bool} {parent : Devm}, parent.getCode a = devm.getCode a →
      m.codeAddress = none → m.currentTarget = newAddress → m.benv.state = parent.state →
      (∀ cevm, (Frame.ofCreate m).enter = .run cevm → a ≠ newAddress) →
      ∀ {r}, ProcessCreateMessage m xl r →
      Execution.getCode ((Resume.createAmsterdam state parent newAddress nacd).run r) a = devm.getCode a := by
    intro m nacd parent hparent hca htarget hstate target r hframe
    have message : MsgResult.getCode r a = m.benv.state.getCode a := by
      rcases xl with _ | ⟨cevm, raw⟩
      · exact ProcessCreateMessage.codeAt_none hca hframe
      · exact ProcessCreateMessage.codeAt (by rw [htarget]; exact target cevm (RunFrame.some_inv hframe).1) inv hframe
    rw [hstate] at message
    exact (Resume.createAmsterdam_accountPreserve (track := false) message (by
      intro impossible
      cases impossible)).1.trans hparent
  unfold GenericCreateAmsterdam at run
  cases hstep : genericCreateAmsterdam.step sevm state devm endowment newAddress mi ms with
  | done out =>
      rw [hstep] at run
      obtain ⟨-, rfl⟩ := run
      simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at hstep
      repeat' split at hstep
      all_goals simp only [XStep.ofExcept, XStep.done.injEq, reduceCtorEq] at hstep
      all_goals subst hstep
      all_goals first
        | rename_i heq
          rw [Devm.push_getCode_gen heq a, Devm.balReadAccount_getCode]
          rfl
        | rename_i heq
          exact ((chargeStateGas_worldEq_of_error heq).getCode a).symm.trans read
        | rename_i v hchg _ _ _ hpush
          rw [Devm.push_getCode_gen hpush a, Devm.incrNonce_getCode, Devm.withholdCreateGas_getCode]
          exact ((chargeStateGas_worldEq_of_ok hchg).getCode a).symm.trans read
        | rename_i hpush
          rw [Devm.push_getCode_gen hpush a, Devm.incrNonce_getCode, Devm.withholdCreateGas_getCode]
          exact read
  | spawn frame resume =>
      rw [hstep] at run
      obtain ⟨r, hframe, rfl⟩ := run
      have target : ∀ cevm, frame.enter = .run cevm → a ≠ newAddress := fun cevm => hne frame resume cevm hstep
      simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at hstep
      repeat' split at hstep
      all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hstep
      all_goals obtain ⟨rfl, rfl⟩ := hstep
      all_goals first
        | rename_i v hchg hnc
          exact result (parentCode (((chargeStateGas_worldEq_of_ok hchg).getCode a).symm.trans read))
            rfl rfl rfl target hframe
        | rename_i hnc
          exact result (parentCode read) rfl rfl rfl target hframe

/-- A call-type instruction keeps the code at `a`, given that its child does and that it enters no CREATE frame at
`a`. -/
theorem Xinst.codeAt_neutral {a : Adr} {sevm : Sevm} {pre : Devm} {x : Xinst} {xl : Xlot} {out : Execution}
    (avoid : Xinst.AvoidsAt a sevm pre x) (hxl : Xlot.Rel (Devm.CodeAt a) xl) (run : Xinst.Run sevm pre x xl out) :
    Execution.Rel (Devm.CodeAt a) pre out := by
  have inv := Xlot.invAt_of_rel hxl
  unfold Xinst.Run at run
  have lift : ∀ {d : Devm}, Devm.InstructionFrame pre d →
      Execution.getCode out a = d.getCode a → Execution.Rel (Devm.CodeAt a) pre out := by
    intro d hf h
    cases out with
    | error e => exact h.trans (hf.getCode a).symm
    | ok d' => exact h.trans (hf.getCode a).symm
  rcases Xinst.step_shape sevm pre x with ⟨ex, shape, hframe⟩ |
      ⟨d, endowment, newAddress, mi, ms, hf, shape⟩ |
      ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
        ii, isz, oi, osz, code, delegated, hf, -, -, -, shape⟩ |
      ⟨d, state, endowment, newAddress, mi, ms, hf, shape⟩ |
      ⟨d, d₀, state, gas, reservoir, value, caller, target, codeAddress,
        stv, isSt, ii, isz, oi, osz, code, dp, nac, ib, hf, -, -, -, shape⟩ <;>
    rw [shape] at run
  · obtain ⟨-, rfl⟩ := run
    cases out with
    | error e => exact (hframe.getCode a).symm
    | ok d' => exact (hframe.getCode a).symm
  · refine lift hf (GenericCreate.codeAt ?_ inv run)
    intro f rsm cevm spawn enter same
    exact avoid f rsm cevm (shape.trans spawn) enter (genericCreate.step_spawn_isCreate spawn)
      ((genericCreate.step_spawn_frame spawn).2.1.trans same.symm)
  · exact lift hf (GenericCall.codeAt inv run)
  · refine lift hf (GenericCreateAmsterdam.codeAt ?_ inv run)
    intro f rsm cevm spawn enter same
    obtain ⟨m, parent, nacd, rfl, -, -, -, -⟩ := genericCreateAmsterdam_step_spawn_form spawn
    exact avoid _ rsm cevm (shape.trans spawn) enter rfl
      ((genericCreateAmsterdam.step_spawn_frame spawn).2.1.trans same.symm)
  · exact lift hf (GenericCallAmsterdam.codeAt inv run)

/-- One interpreter step keeps the code at `a`, given that its child does and that it enters no CREATE frame at
`a`. -/
theorem Evm.step_codeAt_neutral {a : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {xl : Xlot} {out : Execution}
    (avoid : ∀ x, Xinst.At sevm.code pc x → Xinst.AvoidsAt a sevm pre x) (hxl : Xlot.Rel (Devm.CodeAt a) xl)
    (run : Step.Run (Evm.step ⟨pc, sevm, pre⟩) xl out) : Execution.Rel (Devm.CodeAt a) pre out := by
  have hIR : ∀ ⦃d d' : Devm⦄, Devm.InstructionFrame d d' → Devm.CodeAt a d d' := fun _ _ hf => (hf.getCode a).symm
  rcases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with _ | instruction
  · rw [Evm.step_invOp decoded] at run
    obtain ⟨-, rfl⟩ := run
    exact Devm.codeAt_refl a _
  · cases instruction with
    | next n =>
      rw [Evm.step_next (n := n) decoded] at run
      cases n with
      | reg regular => exact Ninst.effectRec_reg (Rinst.codeAt_effect a regular) hxl run
      | exec x =>
        simp only [Ninst.step_exec] at run
        exact Xinst.codeAt_neutral (avoid x decoded) hxl (XStep.run_toStep.mp run)
      | push bytes bound => exact Ninst.push_effectRec_of_instructionFrame hIR hxl run
      | dupn imm => exact Ninst.dupn_effectRec_of_instructionFrame hIR hxl run
      | swapn imm => exact Ninst.swapn_effectRec_of_instructionFrame hIR hxl run
      | exchange imm => exact Ninst.exchange_effectRec_of_instructionFrame hIR hxl run
    | jump j =>
      rw [Evm.step_jump (j := j) decoded] at run
      obtain ⟨-, hcase⟩ := Step.run_ofJump run
      have effect := Jinst.codeAt_effect a j (evm := ⟨pc, sevm, pre⟩) (out := j.run ⟨pc, sevm, pre⟩) rfl
      rcases hcase with ⟨e, hje, rfl⟩ | ⟨pc', d, hje, rfl⟩ <;> rw [hje] at effect <;> exact effect
    | last l =>
      rw [Evm.step_last (l := l) decoded] at run
      obtain ⟨-, rfl⟩ := run
      exact Linst.codeAt_effect a l rfl

/-- One entered, committing child keeps the code at `a` across its spawning step. -/
theorem Evm.step_spawn_settled_codeAt_neutral {a : Adr} {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {frame : Frame}
    {resume : Resume} {childEvm : Evm} {raw : Execution} (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run childEvm) (child : Execution.Rel (Devm.CodeAt a) childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (avoid : childEvm.sta.codeAddress = none → childEvm.sta.currentTarget ≠ a) : Devm.CodeAt a pre post := by
  have codeAddress : childEvm.sta.codeAddress = frame.inner.codeAddress := Frame.enter_run_codeAddress enter
  obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
  exact Evm.step_codeAt_neutral (xl := .some ⟨_, _⟩) (out := .ok _)
    (Xinst.avoidsAt_of_step (fun f' rsm' pc'' cevm' h hen hcr => by
      rw [step] at h
      cases h
      rw [enter] at hen
      cases hen
      rw [← Frame.enter_run_currentTarget enter]
      exact avoid (codeAddress.trans (Xinst.step_spawn_create_codeAddress_neutral spawn hcr))))
    child (by rw [step]; exact ⟨_, RunFrame.of_run enter, resumed.symm⟩)

/-- A child whose settlement does not commit leaves the parent's code at every address, whatever its subtree did. -/
theorem Evm.step_spawn_rolled_codeAt_neutral {a : Adr} {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {frame : Frame}
    {resume : Resume} {childEvm : Evm} {raw : Execution} (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run childEvm) (resumed : resume.run (frame.settle raw) = .ok post)
    (rolled : ¬ Frame.settlementCommits frame raw = true) : Devm.CodeAt a pre post := by
  obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨shape, hstate, herr⟩ := Xinst.step_spawn_form spawn
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
      have process : RunFrame frame (.some ⟨childEvm, raw⟩) (.ok s) := by
        have := RunFrame.of_run (raw := raw) enter
        rwa [settledEq] at this
      rcases shape with ⟨m, rfl, hopen⟩ | ⟨m, rfl, hget, -⟩
      · have back := (ProcessMessage.rollback_of_error (msg := m) process dirty).1
        exact congrArg (fun st : State => st.getCode a) (sState.trans (back.trans hopen))
      · have back := ProcessCreateMessage.rollback_of_error (msg := m) process dirty
        exact (congrArg (fun st : State => st.getCode a) (sState.trans back)).trans (hget a)

/-- A committing run keeps the code at `a` when no retained frame below it is a CREATE at `a`. CREATE frames in
rolled-back subtrees are unconstrained. -/
theorem Exec.codeAt_retained_neutral {a : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (avoid : ∀ f ∈ Exec.descendantFrames run, f.sevm.codeAddress = none → f.sevm.currentTarget ≠ a) :
    Execution.Rel (Devm.CodeAt a) pre out := by
  revert avoid
  refine Exec.retained_induction
    (P := fun _ _ pre out run =>
      (∀ f ∈ Exec.descendantFrames run, f.sevm.codeAddress = none → f.sevm.currentTarget ≠ a) →
      Execution.Rel (Devm.CodeAt a) pre out)
    ?_ ?_ ?_ ?_ ?_ run committed
  · intro pc sevm pre out step _
    exact Evm.step_codeAt_neutral (a := a) (xl := .none)
      (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [step] at h; cases h))
      trivial (by rw [step]; exact ⟨rfl, rfl⟩)
  · intro pc sevm pre pc' post out step next ih avoid
    have here : Devm.CodeAt a _ _ := Evm.step_codeAt_neutral (xl := .none) (out := .ok _)
      (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [step] at h; cases h))
      trivial (by rw [step]; exact ⟨rfl, rfl⟩)
    exact Execution.Rel.trans_left (Devm.codeAt_trans a) here (ih (by rwa [Exec.descendantFrames] at avoid))
  · intro pc sevm pre frame resume pc' result post out step enter resumed next ih avoid
    have here : Devm.CodeAt a _ _ := Evm.step_codeAt_neutral (xl := .none) (out := .ok _)
      (Xinst.avoidsAt_of_step (fun f' rsm' pc' cevm h hen => by
        rw [step] at h
        cases h
        rw [enter] at hen
        cases hen))
      trivial (by rw [step]; exact ⟨_, RunFrame.of_done enter, resumed.symm⟩)
    exact Execution.Rel.trans_left (Devm.codeAt_trans a) here (ih (by rwa [Exec.descendantFrames] at avoid))
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next settles childIH nextIH avoid
    rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resumed next settles] at avoid
    have here := Evm.step_spawn_settled_codeAt_neutral step enter
      (childIH (fun f member => avoid f (List.mem_append_left _ (List.mem_cons_of_mem _ member)))) resumed
      (avoid _ (List.mem_append_left _ List.mem_cons_self))
    exact Execution.Rel.trans_left (Devm.codeAt_trans a) here
      (nextIH (fun f member => avoid f (List.mem_append_right _ member)))
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next rolled nextIH avoid
    rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resumed next rolled] at avoid
    exact Execution.Rel.trans_left (Devm.codeAt_trans a) (Evm.step_spawn_rolled_codeAt_neutral step enter resumed rolled)
      (nextIH avoid)

/-- **Caller exclusion.** Below a committing run whose caller is not `S`, which runs empty code if it is at `S`, with
empty code at `S` and no retained CREATE there: every retained frame has a caller other than `S` and runs empty code if
it is at `S`, and the run leaves the code at `S` empty. -/
theorem Exec.descendantFrames_caller_excluded_neutral {S : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) (caller : sevm.caller ≠ S)
    (targetCode : sevm.currentTarget = S → sevm.code = ByteArray.empty) (empty : pre.getCode S = ByteArray.empty)
    (avoid : ∀ f ∈ Exec.descendantFrames run, f.sevm.codeAddress = none → f.sevm.currentTarget ≠ S) :
    (∀ f ∈ Exec.descendantFrames run,
      f.sevm.caller ≠ S ∧ (f.sevm.currentTarget = S → f.sevm.code = ByteArray.empty)) ∧
      (Execution.committedPost out committed).getCode S = ByteArray.empty := by
  have code : (Execution.committedPost out committed).getCode S = ByteArray.empty := by
    have rel := Exec.codeAt_retained_neutral run committed avoid
    cases out with
    | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post =>
        have same : Devm.CodeAt S pre post := rel
        exact same.trans empty
  refine ⟨?_, code⟩
  revert caller targetCode empty avoid
  refine Exec.retained_induction
    (P := fun _ sevm pre _ run => sevm.caller ≠ S → (sevm.currentTarget = S → sevm.code = ByteArray.empty) →
      pre.getCode S = ByteArray.empty →
      (∀ f ∈ Exec.descendantFrames run, f.sevm.codeAddress = none → f.sevm.currentTarget ≠ S) →
      ∀ f ∈ Exec.descendantFrames run,
        f.sevm.caller ≠ S ∧ (f.sevm.currentTarget = S → f.sevm.code = ByteArray.empty))
    ?_ ?_ ?_ ?_ ?_ run committed
  · intro pc sevm pre out step _ _ _ _ f member
    simp only [Exec.descendantFrames, List.not_mem_nil] at member
  · intro pc sevm pre pc' post out step next ih caller targetCode empty avoid
    have here : Devm.CodeAt S _ _ := Evm.step_codeAt_neutral (xl := .none) (out := .ok _)
      (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [step] at h; cases h))
      trivial (by rw [step]; exact ⟨rfl, rfl⟩)
    rw [Exec.descendantFrames] at avoid ⊢
    exact ih caller targetCode (here.trans empty) avoid
  · intro pc sevm pre frame resume pc' result post out step enter resumed next ih caller targetCode empty avoid
    have here : Devm.CodeAt S _ _ := Evm.step_codeAt_neutral (xl := .none) (out := .ok _)
      (Xinst.avoidsAt_of_step (fun f' rsm' pc' cevm h hen => by
        rw [step] at h
        cases h
        rw [enter] at hen
        cases hen))
      trivial (by rw [step]; exact ⟨_, RunFrame.of_done enter, resumed.symm⟩)
    rw [Exec.descendantFrames] at avoid ⊢
    exact ih caller targetCode (here.trans empty) avoid
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next settles childIH nextIH
      caller targetCode empty avoid
    rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resumed next settles] at avoid ⊢
    have childAvoid : ∀ f ∈ Exec.descendantFrames child, f.sevm.codeAddress = none → f.sevm.currentTarget ≠ S :=
      fun f member => avoid f (List.mem_append_left _ (List.mem_cons_of_mem _ member))
    have rootAvoid := avoid _ (List.mem_append_left _ List.mem_cons_self)
    have childEmpty : childEvm.dyna.getCode S = ByteArray.empty := ((Evm.step_spawn_child step enter).2.1 S).trans empty
    obtain ⟨childCaller, childCode⟩ := Evm.step_spawn_caller_excluded_neutral step enter caller targetCode childEmpty
      rootAvoid
    have here := Evm.step_spawn_settled_codeAt_neutral step enter
      (Exec.codeAt_retained_neutral child (Frame.raw_commits_of_settlementCommits settles) childAvoid) resumed rootAvoid
    have below := childIH childCaller childCode childEmpty childAvoid
    have after := nextIH caller targetCode (here.trans empty) (fun f member =>
      avoid f (List.mem_append_right _ member))
    intro f member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_cons.mp member with rfl | member
      · exact ⟨childCaller, childCode⟩
      · exact below f member
    · exact after f member
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next rolled nextIH
      caller targetCode empty avoid
    rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resumed next rolled] at avoid ⊢
    exact nextIH caller targetCode ((Evm.step_spawn_rolled_codeAt_neutral step enter resumed rolled).trans empty) avoid

end Blanc
