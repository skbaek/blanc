import Batteries.Tactic.OpenPrivate
import Blanc.LockExclusion

/-!
# Kept frames at one account, by recursion on the run

Rule-neutral: nothing here reads `stateGas` or a fork. A child whose settlement does not commit contributes
nothing. A child at the account contributes itself, as a black box; any other committing child contributes what
its own run keeps. No statement here mentions a frame that did not commit.
-/

namespace Blanc

open Jaune

open private resume_callAmsterdam_state from Blanc.LadderBase

/-! ## The world across a spawn, for every rule record -/

private theorem resume_createAmsterdam_state
    {state : StateGasRules} {parent child sf : Devm} {na : Adr} {nac : Bool}
    (h : (Resume.createAmsterdam state parent na nac).run (.ok child) = .ok sf) :
    sf.state = child.state := by
  have key : ∀ d : Devm, d.state = child.state → ∀ v : B256, Devm.push v d = .ok sf → sf.state = child.state := by
    intro d hd v hh
    have hframe := Devm.push_instructionFrame v d
    rw [hh] at hframe
    have hframe' : Devm.InstructionFrame d sf := hframe
    rw [← hframe'.state, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind, Except.assert] at h
  split at h
  · by_cases hP : child.AmsterdamFailedChildSettled
    · rw [ite_eq_left hP] at h
      dsimp only at h
      by_cases hnac : nac = true
      · rw [ite_eq_left hnac] at h
        exact key (Devm.creditStateGasRefund state.newAccount
          (incorporateChildAmsterdamOnError parent child child.output)) rfl 0 h
      · rw [ite_eq_right hnac] at h
        exact key (incorporateChildAmsterdamOnError parent child child.output) rfl 0 h
    · rw [ite_eq_right hP] at h
      cases h
  · by_cases hP : child.AmsterdamChildUncommitted
    · rw [ite_eq_left hP] at h
      dsimp only at h
      exact key (incorporateChildAmsterdamOnSuccess parent child []) rfl _ h
    · rw [ite_eq_right hP] at h
      cases h

/-- What an Amsterdam CREATE spawn leaves its parent with: the creator's nonce one up, on a target with no code. -/
theorem genericCreateAmsterdam_step_spawn_form
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    {frame : Frame} {resume : Resume}
    (spawn : genericCreateAmsterdam.step sevm state devm endowment newAddress mi ms = .spawn frame resume) :
    ∃ (m : Msg) (parent : Devm) (nac : Bool), frame = Frame.ofCreate m ∧
      resume = .createAmsterdam state parent newAddress nac ∧
      m.benv.state = devm.state.incrNonce sevm.currentTarget ∧ m.currentTarget = newAddress ∧
      (devm.state.get newAddress).code.size = 0 := by
  simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at spawn
  all_goals obtain ⟨rfl, rfl⟩ := spawn
  · rename_i _ _ _ v hchg hcollision
    have hs : v.state = devm.state := (Devm.chargeStateGas_state hchg).trans rfl
    refine ⟨_, _, _, rfl, rfl, ?_, rfl, ?_⟩
    · show v.state.incrNonce sevm.currentTarget = _
      rw [hs]
    · have h := (not_or.mp hcollision).2
      rw [← hs]
      exact not_ne_iff.mp h
  · rename_i _ _ hcollision
    refine ⟨_, _, _, rfl, rfl, rfl, rfl, ?_⟩
    exact not_ne_iff.mp (not_or.mp hcollision).2

/-- The two shapes a spawn has. A call's message opens on the parent's world. A create's opens with every account's
code as it was, away from every code-bearing account and with that account's storage. A resumption of an erroring
settlement fails; any other ends on the child's world. -/
theorem Xinst.step_spawn_form {sevm : Sevm} {pre : Devm} {x : Xinst} {frame : Frame} {resume : Resume}
    (spawn : Xinst.step sevm pre x = .spawn frame resume) :
    ((∃ m : Msg, frame = Frame.ofCall m ∧ m.benv.state = pre.state) ∨
      (∃ m : Msg, frame = Frame.ofCreate m ∧ (∀ o, m.benv.state.getCode o = pre.getCode o) ∧
        ∀ o, (pre.getCode o).toList ≠ [] →
          m.currentTarget ≠ o ∧ m.benv.state.getStor o = pre.state.getStor o)) ∧
      (∀ child post, resume.run (.ok child) = .ok post → post.state = child.state) ∧
      ∀ e post, resume.run (.error e) ≠ .ok post := by
  rcases Xinst.step_shape sevm pre x with ⟨ex, shape, -⟩ |
      ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
      ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
        ii, isz, oi, osz, code, delegated, hprefix, -, -, -, shape⟩ |
      ⟨d, state, endowment, newAddress, mi, ms, hprefix, shape⟩ |
      ⟨d, d₀, state, gas, reservoir, value, caller, target, codeAddress,
        stv, isSt, ii, isz, oi, osz, code, dp, nac, ib, hprefix, -, -, -, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · have nonce := UInt64.add_one_ne_zero_of_ne_max (genericCreate_step_spawn_nonce_ne_max spawn)
    have unprotected := genericCreate_step_spawn_target_unprotected spawn
    rcases genericCreate_step_spawn_exact spawn with ⟨rfl, rfl⟩
    refine ⟨.inr ⟨_, rfl, fun o => ?_, fun o hcode => ⟨?_, ?_⟩⟩, fun child post h => Resume.create_state h, ?_⟩
    · show ((d.state.incrNonce sevm.currentTarget).get o).code = pre.getCode o
      rw [State.incrNonce_get_code]
      exact (hprefix.getCode o).symm
    · intro same
      apply unprotected
      have same' : newAddress = o := same
      rw [same', ← hprefix.state]
      exact State.Protected.of_code_ne_nil hcode
    · exact (congrFun (genericCreate_prepared_getStor sevm d newAddress nonce) o).trans
        ((hprefix.getStor o).symm)
    · intro e post
      simp only [Resume.run, liftToExecution, Except.bind_error, ne_eq, reduceCtorEq, not_false_eq_true,
        ExceptT.stM_eq]
  · rcases genericCall_step_spawn_exact spawn with ⟨rfl, rfl⟩
    refine ⟨.inl ⟨_, rfl, hprefix.state.symm⟩, fun child post h => Resume.call_state h, ?_⟩
    intro e post
    simp only [Resume.run, liftToExecution, Except.bind_error, ne_eq, reduceCtorEq, not_false_eq_true,
      ExceptT.stM_eq]
  · obtain ⟨m, parent, nacr, rfl, rfl, hstate, htarget, hempty⟩ := genericCreateAmsterdam_step_spawn_form spawn
    refine ⟨.inr ⟨m, rfl, fun o => ?_, fun o hcode => ?_⟩, fun child post h => resume_createAmsterdam_state h, ?_⟩
    · rw [hstate]
      show ((d.state.incrNonce sevm.currentTarget).get o).code = pre.getCode o
      rw [State.incrNonce_get_code]
      exact (hprefix.getCode o).symm
    · have hd : (d.state.getCode o).toList ≠ [] := by
        have := hprefix.getCode o
        rw [show d.state.getCode o = pre.getCode o from this.symm]
        exact hcode
      refine ⟨?_, ?_⟩
      · rw [htarget]
        intro same
        subst same
        exact ne_wa_of_code_size_zero hd hempty rfl
      · rw [hstate]
        show ((d.state.incrNonce sevm.currentTarget).get o).stor = _
        rw [State.incrNonce_get_stor, ite_eq_right (by
          rintro ⟨equal, empty⟩
          subst o
          exact (ne_wa_of_code_size_zero hd empty.1) rfl)]
        exact hprefix.getStor o |>.symm
    · intro e post
      simp only [Resume.run, liftToExecution, Except.bind_error, ne_eq, reduceCtorEq, not_false_eq_true,
        ExceptT.stM_eq]
  · rcases genericCallAmsterdam_step_spawn_exact spawn with ⟨rfl, rfl⟩
    refine ⟨.inl ⟨_, rfl, hprefix.state.symm⟩, fun child post h => resume_callAmsterdam_state h, ?_⟩
    intro e post
    simp only [Resume.run, liftToExecution, Except.bind_error, ne_eq, reduceCtorEq, not_false_eq_true,
      ExceptT.stM_eq]

/-! ## The kept account across one step -/

theorem Ninst.foreignNone_getStor_eq_neutral
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (run : Ninst.StepRun pc sevm pre n .none (.ok post))
    (target_ne : sevm.currentTarget ≠ ca) (hp : State.Protected pre.state ca) :
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
      exact (Ninst.push_instructionFrame_effectRec (hxs := bound) (xl := .none) trivial run |>.getStor ca).symm
  | dupn imm => exact (Ninst.dupn_instructionFrame_effectRec (xl := .none) trivial run |>.getStor ca).symm
  | swapn imm => exact (Ninst.swapn_instructionFrame_effectRec (xl := .none) trivial run |>.getStor ca).symm
  | exchange imm => exact (Ninst.exchange_instructionFrame_effectRec (xl := .none) trivial run |>.getStor ca).symm

/-- A step that continues the frame, in a frame not at the account, leaves its storage. -/
theorem Evm.step_cont_getStor_foreign {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {a : Adr}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post) (target : sevm.currentTarget ≠ a)
    (hcode : (pre.getCode a).toList ≠ []) : Devm.getStor post a = Devm.getStor pre a := by
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
              exact (Devm.InstructionFrame.getStor frame a).symm
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
          exact Ninst.foreignNone_getStor_eq_neutral nrun target (State.Protected.of_code_ne_nil hcode)

/-- A committing halt leaves the storage of a code-bearing account. -/
theorem Evm.step_halt_getStor {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .halt out) (committed : Execution.commits out = true)
    (hcode : (pre.getCode a).toList ≠ []) :
    Devm.getStor (Execution.committedPost out committed) a = Devm.getStor pre a := by
  cases out with
  | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
      cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
      | none =>
          unfold Evm.step at step
          rw [decoded] at step
          cases step
      | some instruction =>
          cases instruction with
          | last last =>
              rw [Evm.step_last decoded] at step
              have run : Linst.Run sevm pre last (.ok post) := Step.halt.inj step
              exact Linst.getStor_eq run a (State.Protected.of_code_ne_nil hcode)
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

/-- A spawned child opens with the storage of a code-bearing account. -/
theorem Evm.step_spawn_enter_getStor_neutral {pc pc' : Nat} {sevm : Sevm} {pre : Devm} {frame : Frame}
    {resume : Resume} {child : Evm} {a : Adr}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc') (enter : frame.enter = .run child)
    (hcode : (pre.getCode a).toList ≠ []) : Devm.getStor child.dyna a = Devm.getStor pre a := by
  obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
  have facts : frame.inner.benv.state.getStor a = pre.state.getStor a ∧
      State.Protected frame.inner.benv.state a := by
    rcases (Xinst.step_spawn_form spawn).1 with ⟨m, rfl, hstate⟩ | ⟨m, rfl, hget, hkeep⟩
    · change m.benv.state.getStor a = _ ∧ State.Protected m.benv.state a
      rw [hstate]
      exact ⟨rfl, State.Protected.of_code_ne_nil hcode⟩
    · obtain ⟨hne, hstor⟩ := hkeep a hcode
      refine ⟨?_, State.Protected.of_code_ne_nil ?_⟩
      · refine Eq.trans ?_ hstor
        change (processCreateMessage.msg m).benv.state.getStor a = _
        dsimp only [processCreateMessage.msg, Msg.withBenv, Benv.incrNonce,
          Benv.clearStorageWritesIfEmpty, addCreatedAccount, Benv.setStor, State.getStor]
        rw [State.incrNonce_get_stor, ite_eq_right (fun h => hne h.1), State.setStor_get_stor_ne hne]
      · change ((processCreateMessage.msg m).benv.state.getCode a).toList ≠ []
        rw [processCreateMessage.msg_getCode, hget]
        exact hcode
  rcases Frame.enter_run_inv enter with ⟨benv, transfer, rfl⟩
  exact (benvAfterTransfer_ok_getStor transfer a (Or.inr facts.2)).trans facts.1

/-- A child whose settlement commits hands its storage at a code-bearing account to the parent. -/
theorem Evm.step_spawn_settled_getStor {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {frame : Frame}
    {resume : Resume} {child : Evm} {raw : Execution} {a : Adr}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc') (enter : frame.enter = .run child)
    (resumed : resume.run (frame.settle raw) = .ok post) (settles : Frame.settlementCommits frame raw = true)
    (hcode : (pre.getCode a).toList ≠ []) :
    Devm.getStor post a =
      Devm.getStor (Execution.committedPost raw (Frame.raw_commits_of_settlementCommits settles)) a := by
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
      rcases shape with ⟨m, rfl, -⟩ | ⟨m, rfl, -, hkeep⟩
      · have := ProcessMessage.ok_state_eq_committedPost (msg := m) (pc := child.pc) (sevm := child.sta)
          (pre := child.dyna) process committed
        exact congrArg (fun st : State => st.getStor a) (sState.trans this)
      · obtain ⟨inner, innerProcess, postEq, -⟩ := ProcessCreateMessage.ok_getStor_eq_inner_of_clean process clean
        have := ProcessMessage.ok_state_eq_committedPost (pc := child.pc) (sevm := child.sta)
          (pre := child.dyna) innerProcess committed
        calc Devm.getStor post a = Devm.getStor s a := congrArg (fun st : State => st.getStor a) sState
          _ = Devm.getStor inner a := (postEq a (hkeep a hcode).1).2
          _ = _ := congrArg (fun st : State => st.getStor a) this

/-- **A child whose settlement does not commit leaves the parent's storage and code at a code-bearing account,
whatever its subtree did.** -/
theorem Evm.step_spawn_rolled_getStor {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {frame : Frame}
    {resume : Resume} {child : Evm} {raw : Execution} {a : Adr}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc') (enter : frame.enter = .run child)
    (resumed : resume.run (frame.settle raw) = .ok post) (rolled : ¬ Frame.settlementCommits frame raw = true)
    (hcode : (pre.getCode a).toList ≠ []) : Devm.getStor post a = Devm.getStor pre a := by
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
      have process : RunFrame frame (.some ⟨child, raw⟩) (.ok s) := by
        have := RunFrame.of_run (raw := raw) enter
        rwa [settledEq] at this
      rcases shape with ⟨m, rfl, hopen⟩ | ⟨m, rfl, -, hkeep⟩
      · have back := (ProcessMessage.rollback_of_error (msg := m) process dirty).1
        exact congrArg (fun st : State => st.getStor a) (sState.trans (back.trans hopen))
      · have back := ProcessCreateMessage.rollback_of_error (msg := m) process dirty
        calc Devm.getStor post a = m.benv.state.getStor a :=
              congrArg (fun st : State => st.getStor a) (sState.trans back)
          _ = _ := (hkeep a hcode).2

/-! ## The recursion on committing runs -/

/-- The induction on committing executions: a rolled-back child contributes nothing but its parent's resumption,
and the two failing constructors cannot occur. -/
theorem Exec.retained_induction
    {P : (pc : Nat) → (sevm : Sevm) → (pre : Devm) → (out : Execution) → Exec pc sevm pre out → Prop}
    (halt : ∀ {pc sevm pre out} (step : Evm.step ⟨pc, sevm, pre⟩ = .halt out), P pc sevm pre out (.halt step))
    (cont : ∀ {pc sevm pre pc' post out} (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
      (next : Exec pc' sevm post out), P pc' sevm post out next → P pc sevm pre out (.cont step next))
    (doneOk : ∀ {pc sevm pre frame resume pc' result post out}
      (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (enter : frame.enter = .done result) (resumed : resume.run result = .ok post)
      (next : Exec pc' sevm post out), P pc' sevm post out next →
        P pc sevm pre out (.doneOk step enter resumed next))
    (settled : ∀ {pc sevm pre frame resume pc' childEvm raw post out}
      (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (enter : frame.enter = .run childEvm)
      (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (resumed : resume.run (frame.settle raw) = .ok post)
      (next : Exec pc' sevm post out),
      Frame.settlementCommits frame raw = true →
      P childEvm.pc childEvm.sta childEvm.dyna raw child → P pc' sevm post out next →
        P pc sevm pre out (.runOk step enter child resumed next))
    (rolled : ∀ {pc sevm pre frame resume pc' childEvm raw post out}
      (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (enter : frame.enter = .run childEvm)
      (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (resumed : resume.run (frame.settle raw) = .ok post)
      (next : Exec pc' sevm post out),
      ¬ Frame.settlementCommits frame raw = true → P pc' sevm post out next →
        P pc sevm pre out (.runOk step enter child resumed next))
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    P pc sevm pre out run := by
  induction run with
  | halt step => exact halt step
  | cont step next ih => exact cont step next (ih committed)
  | doneErr step enter resumed => simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step enter resumed next ih => exact doneOk step enter resumed next (ih committed)
  | runErr step enter child resumed ih => simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next childIH nextIH =>
    by_cases settles : Frame.settlementCommits frame raw = true
    · exact settled step enter child resumed next settles
        (childIH (Frame.raw_commits_of_settlementCommits settles)) (nextIH committed)
    · exact rolled step enter child resumed next settles (nextIH committed)

/-- **The frames a run keeps at `a`.** A child that does not commit contributes nothing. A committing child at `a`
contributes itself. Any other committing child contributes what its own run keeps. -/
def Exec.keptAt (a : Adr) {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out) :
    List Exec.Frame :=
  match run with
  | .halt _ => []
  | .cont _ next => Exec.keptAt a next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next => Exec.keptAt a next
  | .runErr _ _ _ _ => []
  | .runOk (f := frame) (cevm := childEvm) (raw := raw) _ _ child _ next =>
      (if h : Frame.settlementCommits frame raw = true then
        if childEvm.sta.currentTarget = a then
          [Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits h)]
        else Exec.keptAt a child
      else []) ++ Exec.keptAt a next
termination_by sizeOf run

/-- Frames that each ran on the storage at `a` the one before left. -/
inductive KeptChain (a : Adr) : Stor → List Exec.Frame → Stor → Prop where
  | nil (s : Stor) : KeptChain a s [] s
  | cons {s t : Stor} {f : Exec.Frame} {rest : List Exec.Frame} (starts : Devm.getStor f.pre a = s)
      (tail : KeptChain a (Devm.getStor f.post a) rest t) : KeptChain a s (f :: rest) t

theorem KeptChain.append {a : Adr} {s m t : Stor} {xs ys : List Exec.Frame} (first : KeptChain a s xs m)
    (second : KeptChain a m ys t) : KeptChain a s (xs ++ ys) t := by
  induction first with
  | nil s => exact second
  | cons starts tail ih => exact .cons starts (ih second)

/-- **The fold.** Over a committing run of a frame not at `a`, with code at `a`, the kept frames at `a` form a chain
from the storage at `a` when the run starts to the storage at `a` when it ends. So nothing else writes it, and no
frame outside the list does. -/
theorem Exec.keptAt_chain {a : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) (target : sevm.currentTarget ≠ a)
    (hcode : (pre.getCode a).toList ≠ []) :
    KeptChain a (Devm.getStor pre a) (Exec.keptAt a run) (Devm.getStor (Execution.committedPost out committed) a) := by
  revert committed target hcode
  have goal : ∀ committed : Execution.commits out = true, sevm.currentTarget ≠ a → (pre.getCode a).toList ≠ [] →
      KeptChain a (Devm.getStor pre a) (Exec.keptAt a run) (Devm.getStor (Execution.committedPost out committed) a) := by
    intro committed
    refine Exec.retained_induction
      (P := fun _ sevm pre out run => ∀ committed : Execution.commits out = true, sevm.currentTarget ≠ a →
        (pre.getCode a).toList ≠ [] →
        KeptChain a (Devm.getStor pre a) (Exec.keptAt a run) (Devm.getStor (Execution.committedPost out committed) a))
      ?_ ?_ ?_ ?_ ?_ run committed committed
    · intro pc sevm pre out step committed _ hcode
      rw [Exec.keptAt, Evm.step_halt_getStor step committed hcode]
      exact .nil _
    · intro pc sevm pre pc' post out step next ih committed target hcode
      have hstor := Evm.step_cont_getStor_foreign step target hcode
      have hnext := Blanc.Exec.Deriv.ParentStep.codePreserve (Exec.Deriv.ParentStep.cont step next) a hcode
      rw [Exec.keptAt, ← hstor]
      exact ih committed target (by rw [hnext]; exact hcode)
    · intro pc sevm pre frame resume pc' result post out step enter resumed next ih committed target hcode
      obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv step
      have run : Xinst.Run sevm pre x .none (.ok post) := by
        unfold Xinst.Run XStep.Run
        rw [spawn]
        exact ⟨result, RunFrame.of_done enter, resumed.symm⟩
      have hstor := Xinst.none_getStor_eq run a (State.Protected.of_code_ne_nil hcode)
      have hnext := Blanc.Exec.Deriv.ParentStep.codePreserve (Exec.Deriv.ParentStep.doneOk step enter resumed next) a hcode
      rw [Exec.keptAt, ← hstor]
      exact ih committed target (by rw [hnext]; exact hcode)
    · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next settles childIH nextIH
        committed target hcode
      have hraw := Frame.raw_commits_of_settlementCommits settles
      have hnext := Blanc.Exec.Deriv.ParentStep.codePreserve
        (Exec.Deriv.ParentStep.runOk step enter child resumed next) a hcode
      have tail := nextIH committed target (by rw [hnext]; exact hcode)
      rw [Evm.step_spawn_settled_getStor step enter resumed settles hcode] at tail
      have entry := Evm.step_spawn_enter_getStor_neutral step enter hcode
      rw [Exec.keptAt, dite_eq_left settles]
      by_cases here : childEvm.sta.currentTarget = a
      · rw [ite_eq_left here]
        exact .cons entry tail
      · rw [ite_eq_right here]
        have below := childIH hraw here (by rw [(Evm.step_spawn_child step enter).2.1 a]; exact hcode)
        rw [entry] at below
        exact below.append tail
    · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next rolled nextIH
        committed target hcode
      have hnext := Blanc.Exec.Deriv.ParentStep.codePreserve
        (Exec.Deriv.ParentStep.runOk step enter child resumed next) a hcode
      have tail := nextIH committed target (by rw [hnext]; exact hcode)
      rw [Evm.step_spawn_rolled_getStor step enter resumed rolled hcode] at tail
      rw [Exec.keptAt, dite_eq_right rolled, List.nil_append]
      exact tail
  exact goal

/-- **A rolled-back child contributes nothing.** Whatever ran under a child whose settlement does not commit, among
it any call into `a`: the run's kept frames at `a` are those of its continuation, and the child's parent resumes
with the storage at `a` it had. -/
theorem Exec.keptAt_rolled {a : Adr} {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {frame : Frame} {resume : Resume}
    {childEvm : Evm} {raw out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc') (enter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok post) (next : Exec pc' sevm post out)
    (rolled : ¬ Frame.settlementCommits frame raw = true) (hcode : (pre.getCode a).toList ≠ []) :
    Exec.keptAt a (.runOk step enter child resumed next) = Exec.keptAt a next ∧
      Devm.getStor post a = Devm.getStor pre a := by
  refine ⟨?_, Evm.step_spawn_rolled_getStor step enter resumed rolled hcode⟩
  rw [Exec.keptAt, dite_eq_right rolled, List.nil_append]

/-- A committing child at `a` is kept, first in what its parent keeps from there on. -/
theorem Exec.keptAt_settled_here {a : Adr} {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {frame : Frame}
    {resume : Resume} {childEvm : Evm} {raw out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc') (enter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok post) (next : Exec pc' sevm post out)
    (settles : Frame.settlementCommits frame raw = true) (here : childEvm.sta.currentTarget = a) :
    Exec.keptAt a (.runOk step enter child resumed next) =
      Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits settles) :: Exec.keptAt a next := by
  rw [Exec.keptAt, dite_eq_left settles, ite_eq_left here]
  rfl

end Blanc
