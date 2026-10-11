import Blanc.ExecutionOccurrence

/-!
# Persistent-storage silence of static execution

`STATICCALL` may enter arbitrary interpreted code, including further calls.
The EVM static flag nevertheless propagates to every reached child frame, and
an `SSTORE` instruction cannot complete successfully in such a frame. Safe
call transfers also exclude account-normalization storage deletion. The direct
argument below supplies the storage boundaries used by read-only contracts.
-/

namespace Blanc

open Jaune

/-- The extensional persistent-storage observation used by contract
invariants.  `Stor` is a tree representation whose raw equality can distinguish
redundant zero entries; EVM storage semantics observes only `Stor.get`. -/
def Devm.storageView (state : Devm) : Adr → B256 → B256 :=
  fun owner key => (Devm.getStor state owner).get key

instance : PopBurn.Inv Devm.storageView := ⟨by
  intro words before after run
  funext owner
  funext key
  exact congrArg (fun storage : Stor => storage.get key)
    (Devm.PopBurn.getStor run owner).symm
⟩

instance : Burn.Inv Devm.storageView := ⟨by
  intro before after run
  funext owner
  funext key
  exact congrArg (fun storage : Stor => storage.get key)
    (Devm.Burn.getStor run owner).symm
⟩

instance storageView_linstHinv {terminal : Linst}
    [base : Linst.Hinv Devm.getStor Devm.getStor terminal] :
    Linst.Hinv Devm.storageView Devm.storageView terminal := ⟨by
  intro sevm before after run
  have equal := base.inv run
  funext owner
  funext key
  exact congrArg (fun storage : Stor => storage.get key)
    (congrFun equal owner)
⟩

instance storageView_ninstHinv {instruction : Ninst}
    [base : Ninst.Hinv Devm.getStor instruction] :
    Ninst.Hinv Devm.storageView instruction := ⟨by
  intro sevm before after run
  have equal := base.inv run
  funext owner
  funext key
  exact congrArg (fun storage : Stor => storage.get key)
    (congrFun equal owner)
⟩

/-- Every raw driver node below a static frame is itself static. -/
theorem Exec.rawNodes_isStatic_of_static
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hstatic : sevm.isStatic = true) :
    ∀ node ∈ Exec.rawNodes run, node.sevm.isStatic = true := by
  induction run with
  | halt _ =>
      intro node member
      simp only [Exec.rawNodes, List.mem_singleton] at member
      subst node
      exact hstatic
  | cont _ _ ih =>
      intro node member
      simp only [Exec.rawNodes, List.mem_cons] at member
      rcases member with rfl | member
      · exact hstatic
      · exact ih hstatic node member
  | doneErr _ _ _ =>
      intro node member
      simp only [Exec.rawNodes, List.mem_singleton] at member
      subst node
      exact hstatic
  | doneOk _ _ _ _ ih =>
      intro node member
      simp only [Exec.rawNodes, List.mem_cons] at member
      rcases member with rfl | member
      · exact hstatic
      · exact ih hstatic node member
  | runErr step enter child _ ih =>
      intro node member
      simp only [Exec.rawNodes, List.mem_cons] at member
      rcases member with rfl | member
      · exact hstatic
      · exact ih (Evm.step_run_isStatic step enter hstatic) node member
  | runOk step enter child _ next childIH nextIH =>
      intro node member
      simp only [Exec.rawNodes, List.mem_cons, List.mem_append] at member
      rcases member with rfl | member
      · exact hstatic
      · rcases member with member | member
        · exact childIH (Evm.step_run_isStatic step enter hstatic) node member
        · exact nextIH hstatic node member

/-- A static execution contains no successful persistent-storage write, so
its settlement-retained write chronology is empty.  Failed attempted writes
may still occur in the raw tree; they are correctly irrelevant here. -/
theorem Exec.retainedStorageWrites_eq_nil_of_static
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hstatic : sevm.isStatic = true) :
    Exec.retainedStorageWrites run = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro event member
  rcases Exec.exists_successfulSstore_of_mem_retainedStorageWrites
      (root := (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv))
      (event := event) member with ⟨write, _retained, _event⟩
  have nodeStatic : write.occurrence.node.sevm.isStatic = true :=
    Exec.rawNodes_isStatic_of_static run hstatic
      write.occurrence.node write.occurrence.reached
  have storeRun : Ninst.Run write.occurrence.node.sevm
      write.occurrence.node.devm (.reg .sstore) write.stepPost := by
    refine ⟨write.occurrence.slot, write.occurrence.filled,
      write.occurrence.node.pc, ?_⟩
    simpa only [write.instruction_eq, write.stepSuccess] using
      write.occurrence.stepRun
  have nonstatic := of_run_sstore_not_static storeRun
  rw [nodeStatic] at nonstatic
  exact Bool.noConfusion nonstatic

/-- Balance transfer preserves every account's structural protection. -/
theorem Msg.protected_of_benvAfterTransfer {msg : Msg} {entry : Benv}
    (transfer : msg.benvAfterTransfer = .ok entry)
    (owner : Adr) (hp : State.Protected msg.benv.state owner) :
    State.Protected entry.state owner := by
  by_cases nz : msg.value = 0
  · rw [Msg.benvAfterTransfer_of_value_zero nz] at transfer
    cases transfer
    exact hp
  by_cases enabled : msg.shouldTransferValue = true
  · obtain ⟨mid, sub, rfl⟩ := of_benvAfterTransfer enabled nz transfer
    apply State.Protected.setBal
    have eq := (State.of_subBal sub).2
    rw [eq]
    exact hp.setBal _ _
  · rw [of_benvAfterTransfer_no enabled transfer]
    exact hp

/-- Transfer storage frame under the actual static-call transfer alternatives. -/
theorem Msg.getStor_eq_of_safeTransfer {msg : Msg} {entry : Benv}
    (transfer : msg.benvAfterTransfer = .ok entry)
    (safe : msg.shouldTransferValue = false ∨ msg.value = 0 ∨
      (msg.caller = msg.currentTarget ∧ State.Protected msg.benv.state msg.caller)) :
    entry.state.getStor = msg.benv.state.getStor := by
  rcases safe with off | zero | ⟨self, hp⟩
  · rw [of_benvAfterTransfer_no (by rw [off]; exact Bool.noConfusion) transfer]
  · rw [Msg.benvAfterTransfer_of_value_zero zero] at transfer
    cases transfer
    rfl
  · funext owner
    by_cases same : msg.caller = owner
    · subst owner
      exact benvAfterTransfer_ok_getStor transfer msg.caller (Or.inr hp)
    · by_cases zero : msg.value = 0
      · exact benvAfterTransfer_ok_getStor transfer owner (Or.inl zero)
      by_cases enabled : msg.shouldTransferValue = true
      · obtain ⟨mid, sub, rfl⟩ := of_benvAfterTransfer enabled zero transfer
        change ((mid.addBal msg.currentTarget msg.value).get owner).stor = _
        rw [(State.of_subBal sub).2]
        unfold State.addBal
        rw [State.setBal_get_ne (self ▸ same), State.setBal_get_ne same]
        rfl
      · rw [of_benvAfterTransfer_no enabled transfer]

/-- Static CALL transfers zero; CALLCODE transfers only to its current target. -/
private theorem Xinst.step_spawn_static_transfer {sevm : Sevm} {pre : Devm} {x : Xinst}
    {f : Jaune.Frame} {r : Resume}
    (spawn : Xinst.step sevm pre x = .spawn f r)
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = true) :
    f.inner.shouldTransferValue = false ∨ f.inner.value = 0 ∨
      (f.inner.caller = sevm.currentTarget ∧
        f.inner.currentTarget = sevm.currentTarget) := by
  cases x <;>
    simp only [Xinst.step, fork.rules_stateGas_none, Bind.bind, Except.bind,
      Except.assert, Pure.pure, Except.pure] at spawn <;>
    repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | exact absurd static (by
        rw [genericCreate.step_spawn_not_static spawn]
        exact Bool.noConfusion)
    | obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
      simp_all only [Frame.ofCall, callMsg, Bool.not_true,
        Bool.false_eq_true, false_or, true_or, or_true, and_self, true_and, and_true,
        Bool.true_eq_false, ↓reduceIte, reduceCtorEq, not_true_eq_false]

private theorem GasSchedule.accessDelegation_protected_or_code_empty (gas : GasSchedule) (d : Devm) (target : Adr) :
    State.Protected d.state target ∨ (gas.accessDelegation d target).2.2.1.size = 0 := by
  by_cases hp : State.Protected d.state target
  · exact Or.inl hp
  · right
    have hc : (d.state.get target).code.size = 0 := by
      exact not_not.mp (fun hn => hp (Or.inr hn))
    have hnd : ¬ isValidDelegation (d.getCode target) := by
      intro hd
      exact Nat.noConfusion (hc.symm.trans hd.1)
    rw [GasSchedule.accessDelegation_of_not_delegation hnd]
    exact hc

/-- Actual STATICCALL routing protects a nonempty interpreted target. -/
private theorem Xinst.step_staticcall_spawn_ready {sevm : Sevm} {pre : Devm}
    {f : Jaune.Frame} {r : Resume}
    (spawn : Xinst.step sevm pre .staticcall = .spawn f r)
    (fork : CoveredFork sevm.benvStat.fork) :
    State.Protected f.inner.benv.state f.inner.currentTarget ∨ f.inner.code.size = 0 := by
  simp only [Xinst.step, fork.rules_stateGas_none, Bind.bind, Except.bind,
    Pure.pure, Except.pure] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn

  all_goals
    rename_i d charged
    have frame := chargeGas_worldEq_of_ok charged
    obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
    simp only [Frame.ofCall, callMsg]
    change State.Protected d.state _ ∨ _
    rw [← frame.1]
    rw [GasSchedule.accessDelegation_state]
    exact GasSchedule.accessDelegation_protected_or_code_empty _ _ _

private theorem GenericCall.none_state_transfer {sevm : Sevm} {devm inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    (run : GenericCall sevm devm gas value caller target codeAddress stv
      isStatic ii is oi os code dp .none (.ok inter)) :
    inter.state = devm.state ∨ ∃ f r entry,
      genericCall.step sevm devm gas value caller target codeAddress stv
        isStatic ii is oi os code dp = .spawn f r ∧
      f.inner.benvAfterTransfer = .ok entry ∧ inter.state = entry.state := by
  unfold GenericCall at run
  unfold genericCall.step at run ⊢
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run ⊢
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  · cases run.2
  · rename_i push
    left
    rw [Except.ok.inj run.2, ← (Devm.push_of_push push).state]
    rfl
  · obtain ⟨result, frameRun, resumed⟩ := run
    rcases result with error | child
    · cases Resume.call_run_error resumed.symm
    have state := Resume.call_state resumed.symm
    obtain ⟨raw, body, settled⟩ := ProcessMessage.iff_body.mp frameRun
    unfold FrameBody at body
    rcases transfer : (callMsg sevm (devm.withReturnData []) gas value caller target codeAddress stv isStatic ((devm.withReturnData []).memory.data.sliceD ii is 0) code dp).benvAfterTransfer with error | entry <;>
      rw [transfer] at body
    · rw [body.2, processMessage.settle_error] at settled
      cases settled
    obtain ⟨final, rawEq, settle⟩ := processMessage.settle_ok_cases settled.symm
    subst rawEq
    rcases settle with ⟨bad, childEq⟩ | ⟨clean, childEq⟩
    · left
      rw [state, ← childEq]
      rfl
    · right
      subst childEq
      rcases of_executeCode_someCode rfl body with
        ⟨_, _, handled⟩ | ⟨_, _, impossible, _⟩
      · refine ⟨Frame.ofCall (callMsg sevm (devm.withReturnData []) gas value caller target codeAddress stv isStatic ((devm.withReturnData []).memory.data.sliceD ii is 0) code dp), .call (devm.withReturnData []) oi os, entry, ?_, transfer, ?_⟩
        · simp only [ite_eq_right (show ¬ sevm.depth = 0 from by assumption)]
        · rw [state, state_of_executePrecomp_ok handled clean]
          rfl
      · cases impossible
private theorem Xinst.none_state_transfer_static {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (run : Xinst.Run sevm pre x .none (.ok post))
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = true) :
    post.state = pre.state ∨ ∃ f r entry,
      Xinst.step sevm pre x = .spawn f r ∧
      f.inner.benv.state = pre.state ∧
      f.inner.benvAfterTransfer = .ok entry ∧ post.state = entry.state := by
  unfold Xinst.Run at run
  rcases Xinst.step_shapeCovered sevm pre x fork with
    ⟨ex, shape, hprefix⟩ |
    ⟨d, value, target, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, ca, stv, isSt, ii, isz, oi, osz,
      code, dp, hprefix, _, _, _, shape⟩ <;> rw [shape] at run
  · obtain ⟨_, eq⟩ := run
    rw [← eq] at hprefix
    exact Or.inl hprefix.state.symm
  · unfold genericCreate.step at run
    simp only [assertDynamic, static, Except.assert, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind] at run
    repeat' split at run
    all_goals simp only [XStep.ofExcept, XStep.Run] at run
    all_goals cases run.2
  · rcases GenericCall.none_state_transfer run with eq | ⟨f, r, entry, spawn, transfer, eq⟩
    · exact Or.inl (eq.trans hprefix.state.symm)
    · right
      refine ⟨f, r, entry, shape.trans spawn, ?_, transfer, eq⟩
      obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
      change d.state = pre.state
      exact hprefix.state.symm
private theorem Xinst.none_protected_of_static {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (run : Xinst.Run sevm pre x .none (.ok post))
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = true)
    (owner : Adr) (hp : State.Protected pre.state owner) :
    State.Protected post.state owner := by
  rcases Xinst.none_state_transfer_static run fork static with eq |
    ⟨f, r, entry, spawn, state, transfer, eq⟩
  · rw [eq]; exact hp
  · rw [eq]
    exact Msg.protected_of_benvAfterTransfer transfer owner (state ▸ hp)

private theorem Xinst.none_getStor_eq_of_static_protectedTarget
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (run : Xinst.Run sevm pre x .none (.ok post))
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = true)
    (hp : State.Protected pre.state sevm.currentTarget) :
    Devm.getStor post = Devm.getStor pre := by
  rcases Xinst.none_state_transfer_static run fork static with eq |
    ⟨f, r, entry, spawn, state, transfer, eq⟩
  · funext owner; change post.state.getStor owner = _; rw [eq]; rfl
  · have safe : f.inner.shouldTransferValue = false ∨ f.inner.value = 0 ∨
        (f.inner.caller = f.inner.currentTarget ∧
          State.Protected f.inner.benv.state f.inner.caller) := by
      rcases Xinst.step_spawn_static_transfer spawn fork static with off | zero | ⟨caller, target⟩
      · exact Or.inl off
      · exact Or.inr (Or.inl zero)
      · exact Or.inr (Or.inr ⟨caller.trans target.symm, by rw [state, caller]; exact hp⟩)
    funext owner
    change post.state.getStor owner = _
    rw [eq, Msg.getStor_eq_of_safeTransfer transfer safe, state]
    rfl

/-- Protection and raw storage compose together; all-owner equality additionally
requires protection of the interpreter target. -/
private structure StaticStorageFrame (target : Adr) (pre post : State) : Prop where
  protects : ∀ owner, State.Protected pre owner → State.Protected post owner
  getStor : ∀ owner, State.Protected pre owner → post.getStor owner = pre.getStor owner
  getStor_all : State.Protected pre target → post.getStor = pre.getStor

private theorem StaticStorageFrame.of_eq {target : Adr} {pre post : State}
    (eq : post = pre) : StaticStorageFrame target pre post := by
  cases eq
  exact ⟨fun _ hp => hp, fun _ _ => rfl, fun _ => rfl⟩

private theorem StaticStorageFrame.trans {target : Adr} {pre mid post : State}
    (a : StaticStorageFrame target pre mid) (b : StaticStorageFrame target mid post) :
    StaticStorageFrame target pre post := by
  exact ⟨fun owner hp => b.protects owner (a.protects owner hp),
    fun owner hp => (b.getStor owner (a.protects owner hp)).trans (a.getStor owner hp),
    fun hp => (b.getStor_all (a.protects target hp)).trans (a.getStor_all hp)⟩

private theorem Xinst.none_staticStorageFrame {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (run : Xinst.Run sevm pre x .none (.ok post))
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = true) :
    StaticStorageFrame sevm.currentTarget pre.state post.state := by
  exact ⟨Xinst.none_protected_of_static run fork static, Xinst.none_getStor_eq run,
    Xinst.none_getStor_eq_of_static_protectedTarget run fork static⟩

private theorem Ninst.none_staticStorageFrame {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (run : Ninst.StepRun pc sevm pre n .none (.ok post))
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = true) :
    StaticStorageFrame sevm.currentTarget pre.state post.state := by
  cases n with
  | exec x => exact Xinst.none_staticStorageFrame (XStep.run_toStep.mp run) fork static
  | push bytes bound =>
      exact StaticStorageFrame.of_eq
        (Ninst.push_instructionFrame_effectRec (hxs := bound) (xl := .none) trivial run).state.symm
  | dupn imm =>
      exact StaticStorageFrame.of_eq
        (Ninst.dupn_instructionFrame_effectRec (xl := .none) trivial run).state.symm
  | swapn imm =>
      exact StaticStorageFrame.of_eq
        (Ninst.swapn_instructionFrame_effectRec (xl := .none) trivial run).state.symm
  | exchange imm =>
      exact StaticStorageFrame.of_eq
        (Ninst.exchange_instructionFrame_effectRec (xl := .none) trivial run).state.symm
  | reg r =>
      have regularRun : Rinst.run ⟨pc, sevm, pre⟩ r = .ok post :=
        ((Step.run_ofExecution (xl := (.none : Xlot))).mp run).2.symm
      by_cases store : r = .sstore
      · subst r
        have nonstatic := of_run_sstore_not_static
          (show Ninst.Run sevm pre Ninst.sstore post from ⟨.none, trivial, pc, run⟩)
        rw [static] at nonstatic
        exact Bool.noConfusion nonstatic
      by_cases transient : r = .tstore
      · subst r
        have frame := Rinst.tstore_run_transientWriteFrame pc pre sevm
        rw [regularRun] at frame
        exact StaticStorageFrame.of_eq frame.state.symm
      · have frame := Rinst.run_instructionFrame pc sevm pre r store transient
        rw [regularRun] at frame
        exact StaticStorageFrame.of_eq frame.state.symm

private theorem Linst.static_state_eq {sevm : Sevm} {pre post : Devm} {l : Linst}
    (run : Linst.run sevm pre l = .ok post)
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = true) :
    post.state = pre.state := by
  by_cases self : l = .selfdestruct
  · subst l
    simp only [Linst.run, fork.rules_stateGas_none] at run
    rcases Except.bind_eq_ok run with ⟨_, _, run₁⟩
    rcases Except.bind_eq_ok run₁ with ⟨_, _, run₂⟩
    rcases Except.bind_eq_ok run₂ with ⟨_, _, run₃⟩
    rcases Except.bind_eq_ok run₃ with ⟨_, _, run₄⟩
    rcases Except.bind_eq_ok run₄ with ⟨_, _, run₅⟩
    rcases Except.bind_eq_ok run₅ with ⟨_, failed, _⟩
    simp only [assertDynamic, Except.assert, static, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq] at failed
  · have frame := Linst.run_instructionFrame sevm pre l self
    rw [run] at frame
    exact frame.state.symm

private theorem Exec.committedPost_state_eq_of_emptyCode {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (empty : sevm.code.size = 0)
    (committed : Execution.commits out = true) :
    (Execution.committedPost out committed).state = pre.state := by
  have step : Evm.step ⟨pc, sevm, pre⟩ = .halt (.ok pre) := by
    simp only [Evm.step, Evm.getInst, ByteArray.getInst, empty, not_lt_zero, ↓reduceDIte, Linst.run]
  cases run with
  | halt actual => rw [step] at actual; cases actual; rfl
  | cont actual _ => rw [step] at actual; cases actual
  | doneErr actual _ _ => rw [step] at actual; cases actual
  | doneOk actual _ _ _ => rw [step] at actual; cases actual
  | runErr actual _ _ _ => rw [step] at actual; cases actual
  | runOk actual _ _ _ _ => rw [step] at actual; cases actual

private theorem staticStep_cont_frame
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    (static : sevm.isStatic = true) (fork : CoveredFork sevm.benvStat.fork) :
    StaticStorageFrame sevm.currentTarget pre.state post.state := by
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
              have frame :=
                Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ jumpInst
              rw [jumpEq] at frame
              exact StaticStorageFrame.of_eq frame.state.symm
      | next instruction =>
          have nstep : Ninst.step ⟨pc, sevm, pre⟩ instruction =
              .cont pc' post := by
            rw [← Evm.step_next decoded]
            exact step
          have pcEq : pc' = pc + instruction.size :=
            Ninst.step_cont_pc nstep
          subst pc'
          have nrun : Ninst.StepRun pc sevm pre instruction .none (.ok post) := by
            unfold Ninst.StepRun
            rw [nstep]
            exact ⟨rfl, rfl⟩
          exact Ninst.none_staticStorageFrame nrun fork static

private theorem staticHalt_frame
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .halt out)
    (committed : Execution.commits out = true)
    (static : sevm.isStatic = true) (fork : CoveredFork sevm.benvStat.fork) :
    StaticStorageFrame sevm.currentTarget pre.state (Execution.committedPost out committed).state := by
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
          | next next =>
              rw [Evm.step_next decoded] at step
              exact (Ninst.step_ne_halt_ok step).elim
          | jump jumpInst =>
              rw [Evm.step_jump decoded] at step
              cases jumpEq : Jinst.run ⟨pc, sevm, pre⟩ jumpInst <;>
                rw [jumpEq] at step <;> cases step
          | last last =>
              rw [Evm.step_last decoded] at step
              exact StaticStorageFrame.of_eq (Linst.static_state_eq (Step.halt.inj step) fork static)


private theorem Xinst.step_spawn_static_ready {sevm : Sevm} {pre : Devm} {x : Xinst}
    {f : Jaune.Frame} {r : Resume}
    (spawn : Xinst.step sevm pre x = .spawn f r)
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = true)
    (hp : State.Protected pre.state sevm.currentTarget) :
    State.Protected f.inner.benv.state f.inner.currentTarget ∨ f.inner.code.size = 0 := by
  rcases Xinst.step_shapeCovered sevm pre x fork with
    ⟨ex, shape, hprefix⟩ |
    ⟨d, value, target, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, ca, stv, isSt, ii, isz, oi, osz,
      code, dp, hprefix, hprefix₀, _, source, shape⟩ <;> rw [shape] at spawn
  · cases spawn
  · exact absurd static (by rw [genericCreate.step_spawn_not_static spawn]; exact Bool.noConfusion)
  · obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
    change State.Protected d.state target ∨ code.size = 0
    by_cases child : State.Protected pre.state target
    · left; rw [← hprefix.state]; exact child
    · right
      rcases source with same | realized
      · exact False.elim (child (same ▸ hp))
      · have empty : (d₀.getCode target).size = 0 := by
          change (d₀.state.get target).code.size = 0
          rw [← hprefix₀.state]
          exact not_not.mp (fun hn => child (Or.inr hn))
        have noDelegation : ¬ isValidDelegation (d₀.getCode target) := by
          intro delegated
          exact Nat.noConfusion (empty.symm.trans delegated.1)
        rw [realized noDelegation]
        exact empty

private theorem Frame.enter_run_static_ready {f : Jaune.Frame} {cevm : Evm}
    (enter : f.enter = .run cevm)
    (ready : State.Protected f.inner.benv.state f.inner.currentTarget ∨ f.inner.code.size = 0) :
    State.Protected cevm.dyna.state cevm.sta.currentTarget ∨ cevm.sta.code.size = 0 := by
  rcases Frame.enter_run_inv enter with ⟨entry, transfer, rfl⟩
  rcases ready with hp | empty
  · left
    exact Msg.protected_of_benvAfterTransfer transfer _ hp
  · exact Or.inr empty

private theorem Xinst.step_staticcall_spawn_value_zero {sevm : Sevm} {pre : Devm}
    {f : Jaune.Frame} {r : Resume}
    (spawn : Xinst.step sevm pre .staticcall = .spawn f r)
    (fork : CoveredFork sevm.benvStat.fork) : f.inner.value = 0 := by
  simp only [Xinst.step, fork.rules_stateGas_none, Bind.bind, Except.bind,
    Pure.pure, Except.pure] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals
    obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
    rfl

private theorem processMessage_static_frame
    {msg : Msg} {post parent : Devm}
    {cevm : Evm} {out : Execution}
    (process : ProcessMessage msg (.some ⟨cevm, out⟩) (.ok post))
    (parentState : parent.state = msg.benv.state)
    (target : Adr)
    (safe : State.Protected msg.benv.state target →
      msg.shouldTransferValue = false ∨ msg.value = 0 ∨
        (msg.caller = msg.currentTarget ∧ State.Protected msg.benv.state msg.caller))
    (body : ∀ committed : Execution.commits out = true,
      StaticStorageFrame cevm.sta.currentTarget cevm.dyna.state
        (Execution.committedPost out committed).state)
    (bodyAll : ∀ committed : Execution.commits out = true,
      State.Protected msg.benv.state target →
      Devm.getStor (Execution.committedPost out committed) = Devm.getStor cevm.dyna) :
    StaticStorageFrame target parent.state post.state := by
  by_cases settles : Frame.settlementCommits (Frame.ofCall msg) out = true
  · have committed := Frame.raw_commits_of_settlementCommits settles
    have enter : (Frame.ofCall msg).enter = .run cevm :=
      (RunFrame.some_inv process).1
    rcases Frame.enter_run_inv enter with ⟨benv, transfer, evmEq⟩
    simp only [Frame.ofCall] at transfer evmEq
    have preState : cevm.dyna.state = benv.state :=
      congrArg (fun evm : Evm => evm.dyna.state) evmEq
    have postState : post.state =
        (Execution.committedPost out committed).state :=
      ProcessMessage.ok_state_eq_committedPost process committed
    rw [postState, parentState]
    refine ⟨?_, ?_, ?_⟩
    · intro owner hp
      apply (body committed).protects owner
      rw [preState]
      exact Msg.protected_of_benvAfterTransfer transfer owner hp
    · intro owner hp
      have entryProtected := Msg.protected_of_benvAfterTransfer transfer owner hp
      have preserved := (body committed).getStor owner (preState.symm ▸ entryProtected)
      change (Execution.committedPost out committed).state.getStor owner = _
      rw [preserved]
      rw [preState]
      exact benvAfterTransfer_ok_getStor transfer owner (Or.inr hp)
    · intro hp
      change Devm.getStor (Execution.committedPost out committed) = _
      rw [bodyAll committed hp]
      change cevm.dyna.state.getStor = _
      rw [preState]
      exact Msg.getStor_eq_of_safeTransfer transfer (safe hp)
  · have settledEq := (RunFrame.some_inv process).2
    have postError : post.error.isSome = true := by
      have notNone : post.error.isNone ≠ true := by
        intro clean
        apply settles
        unfold Frame.settlementCommits
        rw [← settledEq]
        exact clean
      cases errorEq : post.error <;> simp_all only [ExceptT.stM_eq, Bool.not_eq_true, Option.isNone_none, ne_eq, not_true_eq_false, Option.isNone_some, Bool.false_eq_true, not_false_eq_true, Option.isSome_some]
    have rollback := (ProcessMessage.rollback_of_error process postError).1
    exact StaticStorageFrame.of_eq (rollback.trans parentState.symm)

private theorem xinstSome_static_frame
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Jaune.Frame} {resume : Resume}
    {cevm : Evm} {out : Execution}
    {result : Except (EvmError × State × AdrSet × Tra) Devm}
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (hfork : CoveredFork sevm.benvStat.fork)
    (childStatic : frame.inner.isStatic = true)
    (frameRun : RunFrame frame (.some ⟨cevm, out⟩) result)
    (resumeRun : resume.run result = .ok post)
    (safe : State.Protected pre.state sevm.currentTarget →
      frame.inner.shouldTransferValue = false ∨ frame.inner.value = 0 ∨
        (frame.inner.caller = frame.inner.currentTarget ∧ State.Protected frame.inner.benv.state frame.inner.caller))
    (ready : State.Protected pre.state sevm.currentTarget →
      State.Protected frame.inner.benv.state frame.inner.currentTarget ∨ frame.inner.code.size = 0)
    (body : ∀ committed : Execution.commits out = true,
      StaticStorageFrame cevm.sta.currentTarget cevm.dyna.state
        (Execution.committedPost out committed).state)
    (emptyBody : cevm.sta.code.size = 0 →
      ∀ committed : Execution.commits out = true,
      Devm.getStor (Execution.committedPost out committed) = Devm.getStor cevm.dyna) :
    StaticStorageFrame sevm.currentTarget pre.state post.state := by
  rcases Xinst.step_shapeCovered sevm pre x hfork with
    ⟨execution, shape, hprefix⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · rcases genericCreate_step_spawn_exact spawn with ⟨rfl, -⟩
    simp only [Frame.ofCreate, createMsg, processCreateMessage.msg, Msg.withBenv,
      Bool.false_eq_true] at childStatic
  · rcases genericCall_step_spawn_exact spawn with ⟨rfl, rfl⟩
    have run : GenericCall sevm d gas value caller target codeAddress stv
        isStatic ii isz oi osz code disablePrecompiles
        (.some ⟨cevm, out⟩) (.ok post) := by
      unfold GenericCall XStep.Run
      rw [spawn]
      exact ⟨result, frameRun, resumeRun.symm⟩
    unfold GenericCall genericCall.step at run
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
    repeat' split at run
    all_goals simp only [XStep.ofExcept, XStep.Run] at run
    · cases run.1
    · cases run.1
    · obtain ⟨settled, process, resumed⟩ := run
      rcases settled with error | child
      · cases Resume.call_run_error resumed.symm
      have childState : post.state = child.state :=
        Resume.call_state resumed.symm
      have childEnter := (RunFrame.some_inv process).1
      have settledFrame := processMessage_static_frame
        (parent := d.withReturnData []) process rfl sevm.currentTarget
        (fun hp => safe (hprefix.state ▸ hp)) body
        (fun committed hp => by
          rcases Frame.enter_run_static_ready childEnter (ready (hprefix.state ▸ hp)) with protectedTarget | empty
          · exact (body committed).getStor_all protectedTarget
          · exact emptyBody empty committed)
      rw [childState]
      exact (StaticStorageFrame.of_eq hprefix.state.symm).trans settledFrame

private theorem Xinst.step_spawn_static_benv_state {sevm : Sevm} {pre : Devm} {x : Xinst}
    {f : Jaune.Frame} {r : Resume}
    (spawn : Xinst.step sevm pre x = .spawn f r)
    (fork : CoveredFork sevm.benvStat.fork) (childStatic : f.inner.isStatic = true) :
    f.inner.benv.state = pre.state := by
  rcases Xinst.step_shapeCovered sevm pre x fork with
    ⟨ex, shape, hprefix⟩ |
    ⟨d, value, target, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, ca, stv, isSt, ii, isz, oi, osz,
      code, dp, hprefix, _, _, _, shape⟩ <;> rw [shape] at spawn
  · cases spawn
  · obtain ⟨rfl, _⟩ := genericCreate_step_spawn_exact spawn
    simp only [Frame.ofCreate, createMsg, processCreateMessage.msg, Msg.withBenv,
      Bool.false_eq_true] at childStatic
  · obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
    exact hprefix.state.symm

private theorem Xinst.step_spawn_static_safeTransfer {sevm : Sevm} {pre : Devm} {x : Xinst}
    {f : Jaune.Frame} {r : Resume}
    (spawn : Xinst.step sevm pre x = .spawn f r)
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = true)
    (hp : State.Protected pre.state sevm.currentTarget) :
    f.inner.shouldTransferValue = false ∨ f.inner.value = 0 ∨
      (f.inner.caller = f.inner.currentTarget ∧ State.Protected f.inner.benv.state f.inner.caller) := by
  rcases Xinst.step_spawn_static_transfer spawn fork static with off | zero | ⟨caller, target⟩
  · exact Or.inl off
  · exact Or.inr (Or.inl zero)
  · exact Or.inr (Or.inr ⟨caller.trans target.symm, by
      rw [Xinst.step_spawn_static_benv_state spawn fork
        (Xinst.step_spawn_isStatic spawn static), caller]
      exact hp⟩)

private theorem Exec.staticStorageFrame_committedPost {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (static : sevm.isStatic = true)
    (committed : Execution.commits out = true) (fork : CoveredFork sevm.benvStat.fork) :
    StaticStorageFrame sevm.currentTarget pre.state (Execution.committedPost out committed).state := by
  induction run with
  | halt step => exact staticHalt_frame step committed static fork
  | cont step _ ih =>
      exact (staticStep_cont_frame step static fork).trans (ih static committed fork)
  | doneErr _ _ _ => simp only [Execution.commits, Bool.false_eq_true] at committed
  | @doneOk _ nodeSevm nodePre _ _ _ _ nodePost _ step enter resumeRun _ ih =>
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have xrun : Xinst.Run nodeSevm nodePre x .none (.ok nodePost) := by
        unfold Xinst.Run XStep.Run
        rw [spawn]
        exact ⟨_, RunFrame.of_done enter, resumeRun.symm⟩
      exact (Xinst.none_staticStorageFrame xrun fork static).trans (ih static committed fork)
  | runErr _ _ _ _ _ => simp only [Execution.commits, Bool.false_eq_true] at committed
  | runOk step enter child resumeRun _ childIH nextIH =>
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have childStatic := Evm.step_run_isStatic step enter static
      have childFork := Evm.step_spawn_child_fork step enter fork
      exact (xinstSome_static_frame spawn fork (Evm.step_spawn_isStatic step static)
        (RunFrame.of_run enter) resumeRun
        (Xinst.step_spawn_static_safeTransfer spawn fork static)
        (Xinst.step_spawn_static_ready spawn fork static)
        (fun childCommitted => childIH childStatic childCommitted childFork)
        (fun empty childCommitted => congrArg State.getStor
          (Exec.committedPost_state_eq_of_emptyCode child empty childCommitted))).trans
        (nextIH static committed fork)

private theorem processMessage_getStor_of_body
    {msg : Msg} {post parent : Devm}
    {cevm : Evm} {out : Execution}
    (process : ProcessMessage msg (.some ⟨cevm, out⟩) (.ok post))
    (parentState : parent.state = msg.benv.state)
    (safe : msg.shouldTransferValue = false ∨ msg.value = 0 ∨
      (msg.caller = msg.currentTarget ∧ State.Protected msg.benv.state msg.caller))
    (body : ∀ committed : Execution.commits out = true,
      Devm.getStor (Execution.committedPost out committed) =
        Devm.getStor cevm.dyna) :
    Devm.getStor post = Devm.getStor parent := by
  by_cases settles : Frame.settlementCommits (Frame.ofCall msg) out = true
  · have committed := Frame.raw_commits_of_settlementCommits settles
    have enter : (Frame.ofCall msg).enter = .run cevm :=
      (RunFrame.some_inv process).1
    rcases Frame.enter_run_inv enter with ⟨benv, transfer, evmEq⟩
    simp only [Frame.ofCall] at transfer evmEq
    have preState : cevm.dyna.state = benv.state :=
      congrArg (fun evm : Evm => evm.dyna.state) evmEq
    have postState : post.state =
        (Execution.committedPost out committed).state :=
      ProcessMessage.ok_state_eq_committedPost process committed
    funext owner
    change post.state.getStor owner = parent.state.getStor owner
    rw [postState]
    change Devm.getStor (Execution.committedPost out committed) owner = _
    rw [body committed]
    change cevm.dyna.state.getStor owner = parent.state.getStor owner
    rw [preState, parentState, Msg.getStor_eq_of_safeTransfer transfer safe]
  · have settledEq := (RunFrame.some_inv process).2
    have postError : post.error.isSome = true := by
      have notNone : post.error.isNone ≠ true := by
        intro clean
        apply settles
        unfold Frame.settlementCommits
        rw [← settledEq]
        exact clean
      cases errorEq : post.error <;> simp_all only [ExceptT.stM_eq, Bool.not_eq_true, Option.isNone_none, ne_eq, not_true_eq_false, Option.isNone_some, Bool.false_eq_true, not_false_eq_true, Option.isSome_some]
    have rollback := (ProcessMessage.rollback_of_error process postError).1
    funext owner
    change post.state.getStor owner = parent.state.getStor owner
    rw [rollback, parentState]

private theorem xinstSome_getStor
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Jaune.Frame} {resume : Resume}
    {cevm : Evm} {out : Execution}
    {result : Except (EvmError × State × AdrSet × Tra) Devm}
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (hfork : CoveredFork sevm.benvStat.fork)
    (childStatic : frame.inner.isStatic = true)
    (frameRun : RunFrame frame (.some ⟨cevm, out⟩) result)
    (resumeRun : resume.run result = .ok post)
    (safe : frame.inner.shouldTransferValue = false ∨ frame.inner.value = 0 ∨
      (frame.inner.caller = frame.inner.currentTarget ∧ State.Protected frame.inner.benv.state frame.inner.caller))
    (body : ∀ committed : Execution.commits out = true,
      Devm.getStor (Execution.committedPost out committed) =
        Devm.getStor cevm.dyna) :
    Devm.getStor post = Devm.getStor pre := by
  rcases Xinst.step_shapeCovered sevm pre x hfork with
    ⟨execution, shape, hprefix⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · rcases genericCreate_step_spawn_exact spawn with ⟨rfl, -⟩
    simp only [Frame.ofCreate, createMsg, processCreateMessage.msg, Msg.withBenv,
      Bool.false_eq_true] at childStatic
  · rcases genericCall_step_spawn_exact spawn with ⟨rfl, rfl⟩
    have run : GenericCall sevm d gas value caller target codeAddress stv
        isStatic ii isz oi osz code disablePrecompiles
        (.some ⟨cevm, out⟩) (.ok post) := by
      unfold GenericCall XStep.Run
      rw [spawn]
      exact ⟨result, frameRun, resumeRun.symm⟩
    unfold GenericCall genericCall.step at run
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
    repeat' split at run
    all_goals simp only [XStep.ofExcept, XStep.Run] at run
    · cases run.1
    · cases run.1
    · obtain ⟨settled, process, resumed⟩ := run
      rcases settled with error | child
      · cases Resume.call_run_error resumed.symm
      have childState : post.state = child.state :=
        Resume.call_state resumed.symm
      have settledEq := processMessage_getStor_of_body
        (parent := d.withReturnData []) process rfl safe body
      funext owner
      change post.state.getStor owner = pre.state.getStor owner
      rw [childState]
      exact (congrFun settledEq owner).trans (hprefix.getStor owner).symm

private theorem Xinst.staticcall_none_getStor_eq {sevm : Sevm} {pre post : Devm}
    (run : Xinst.Run sevm pre .staticcall .none (.ok post))
    (fork : CoveredFork sevm.benvStat.fork) :
    Devm.getStor post = Devm.getStor pre := by
  simp only [Xinst.Run, Xinst.step, fork.rules_stateGas_none, Bind.bind, Except.bind,
    Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  all_goals first
    | cases run.2
    | rename_i _ a₁ h₁ _ a₂ h₂ _ a₃ h₃ _ a₄ h₄ _ a₅ h₅ _ a₆ h₆ _ d charged
      have chargedFrame := chargeGas_worldEq_of_ok charged
      have frame₁ := Devm.pop_instructionFrame pre
      rw [h₁] at frame₁
      have frame₂ := Devm.popToAdr_instructionFrame a₁.2
      rw [h₂] at frame₂
      have frame₃ := Devm.popToNat_instructionFrame a₂.2
      rw [h₃] at frame₃
      have frame₄ := Devm.popToNat_instructionFrame a₃.2
      rw [h₄] at frame₄
      have frame₅ := Devm.popToNat_instructionFrame a₄.2
      rw [h₅] at frame₅
      have frame₆ := Devm.popToNat_instructionFrame a₅.2
      rw [h₆] at frame₆
      have back : d.state = pre.state := by
        rw [← chargedFrame.1, GasSchedule.accessDelegation_state, addAccessedAddress_state,
          ← frame₆.state, ← frame₅.state, ← frame₄.state, ← frame₃.state,
          ← frame₂.state, ← frame₁.state]
      have genericRun : GenericCall sevm (d.memExtends [(a₃.1, a₄.1), (a₅.1, a₆.1)])
        (calculateMsgCallGas 0 a₁.1.toNat
          (sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress a₆.2 a₂.1) a₂.1).2.2.2.2.gasLeft
          (a₆.2.extCost [(a₃.1, a₄.1), (a₅.1, a₆.1)])
          (sevm.benvStat.rules.gas.accessCost a₂.1 a₆.2.accessedAddresses +
            (sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress a₆.2 a₂.1) a₂.1).2.2.2.1)).2
        0 sevm.currentTarget a₂.1
        (sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress a₆.2 a₂.1) a₂.1).2.1
        true true a₃.1 a₄.1 a₅.1 a₆.1
        (sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress a₆.2 a₂.1) a₂.1).2.2.1
        (sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress a₆.2 a₂.1) a₂.1).1
        .none (.ok post) := by
        simpa only [GenericCall, XStep.Run, reduceCtorEq] using run
      rcases GenericCall.none_state_transfer genericRun with eq | ⟨f, r, entry, spawn, transfer, eq⟩
      · funext owner
        change post.state.getStor owner = _
        rw [eq]
        change d.state.getStor owner = _
        rw [back]
        rfl
      · obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
        have preserved := Msg.getStor_eq_of_safeTransfer transfer (Or.inr (Or.inl rfl))
        funext owner
        change post.state.getStor owner = _
        rw [eq, preserved]
        change d.state.getStor owner = _
        rw [back]
        rfl

/-- Static execution preserves raw storage at every structurally protected owner. -/
theorem Exec.getStor_committedPost_eq_of_static_protected
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (static : sevm.isStatic = true)
    (committed : Execution.commits out = true) (fork : CoveredFork sevm.benvStat.fork)
    (owner : Adr) (hp : State.Protected pre.state owner) :
    Devm.getStor (Execution.committedPost out committed) owner = Devm.getStor pre owner :=
  (Exec.staticStorageFrame_committedPost run static committed fork).getStor owner hp

/-- Static execution transports structural protection through every committed frame. -/
theorem Exec.protected_committedPost_of_static
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (static : sevm.isStatic = true)
    (committed : Execution.commits out = true) (fork : CoveredFork sevm.benvStat.fork)
    (owner : Adr) (hp : State.Protected pre.state owner) :
    State.Protected (Execution.committedPost out committed).state owner :=
  (Exec.staticStorageFrame_committedPost run static committed fork).protects owner hp

/-- Static execution preserves all raw storage when its target is protected
or its interpreter code is empty. Arbitrary mismatched static roots need this premise. -/
theorem Exec.getStor_committedPost_eq_of_static
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (static : sevm.isStatic = true)
    (committed : Execution.commits out = true) (fork : CoveredFork sevm.benvStat.fork)
    (ready : State.Protected pre.state sevm.currentTarget ∨ sevm.code.size = 0) :
    Devm.getStor (Execution.committedPost out committed) = Devm.getStor pre := by
  rcases ready with protectedTarget | empty
  · exact (Exec.staticStorageFrame_committedPost run static committed fork).getStor_all protectedTarget
  · exact congrArg State.getStor (Exec.committedPost_state_eq_of_emptyCode run empty committed)

/-- Shared raw-storage boundary for actual STATICCALL on a covered fork. -/
theorem Ninst.staticcall_getStor_eq
    {sevm : Sevm} {pre post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : Ninst.Run sevm pre Ninst.staticcall post) :
    Devm.getStor pre = Devm.getStor post := by
  rcases run with ⟨slot, filled, pc, stepRun⟩
  have xrun : Xinst.Run sevm pre .staticcall slot (.ok post) := by
    simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep,
      Xinst.Run] using stepRun
  cases slot with
  | none => exact (Xinst.staticcall_none_getStor_eq xrun hfork).symm
  | some child =>
      rcases child with ⟨cevm, out⟩
      rcases filled with ⟨childRun⟩
      rcases XStep.Run.some_inv xrun with ⟨frame, resume, spawn, enter, resumed⟩
      have childStatic : cevm.sta.isStatic = true :=
        (Frame.enter_run_isStatic enter).trans
          (Xinst.step_staticcall_spawn_isStatic spawn)
      have childFork : CoveredFork cevm.sta.benvStat.fork :=
        Xinst.Run.some_child_fork xrun hfork
      exact (xinstSome_getStor spawn hfork
        (Xinst.step_staticcall_spawn_isStatic spawn)
        (RunFrame.of_run enter) resumed.symm
        (Or.inr (Or.inl (Xinst.step_staticcall_spawn_value_zero spawn hfork)))
        (fun committed => Exec.getStor_committedPost_eq_of_static childRun
          childStatic committed childFork
          (Frame.enter_run_static_ready enter (Xinst.step_staticcall_spawn_ready spawn hfork)))).symm

/-- A committing static execution preserves storage observations under the
same readiness premise as the raw-storage theorem. -/
theorem Exec.storageView_committedPost_eq_of_static
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hstatic : sevm.isStatic = true)
    (committed : Execution.commits out = true)
    (hfork : CoveredFork sevm.benvStat.fork)
    (ready : State.Protected pre.state sevm.currentTarget ∨ sevm.code.size = 0) :
    Devm.storageView (Execution.committedPost out committed) = Devm.storageView pre := by
  have equal := Exec.getStor_committedPost_eq_of_static run hstatic committed hfork ready
  funext owner key
  exact congrArg (fun storage : Stor => storage.get key) (congrFun equal owner)

/-- Every successful actual STATICCALL preserves persistent storage,
including interpreted children and synchronous precompiles. -/
theorem Ninst.staticcall_inv_getStor
    {sevm : Sevm} {pre post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : Ninst.Run sevm pre Ninst.staticcall post) :
    Devm.storageView pre = Devm.storageView post := by
  have equal := Ninst.staticcall_getStor_eq hfork run
  funext owner key
  exact congrArg (fun storage : Stor => storage.get key) (congrFun equal owner)

end Blanc
