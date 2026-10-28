import Blanc.ExecutionHistoryInCodeAt
import Blanc.LockExclusion
import Blanc.ExecutionCellProvenance

/-! Code preservation from actual retained positions, including creation within a root. -/

namespace Blanc

open Jaune

/-- A successful CREATE cannot target an account with a nonzero nonce, and every
entered child inherits the nonzero nonce. This uses the actual CREATE guard. -/
theorem Evm.step_spawn_nonce_noStateGas
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume} {child : Evm} {a : Adr}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run child)
    (nonce : (pre.state.get a).nonce ≠ 0) :
    (child.dyna.state.get a).nonce ≠ 0 ∧
      (frame.isCreate = true → frame.inner.currentTarget ≠ a) := by
  obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with
    ⟨execution, shape, _⟩ |
    ⟨d, endowment, address, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · have nonceAt : (d.state.get a).nonce ≠ 0 := by rwa [← hprefix.state]
    have different : address ≠ a := by
      intro equal
      have unprotected := genericCreate_step_spawn_target_unprotected spawn
      rw [equal] at unprotected
      exact unprotected (Or.inl nonceAt)
    have nonwrap := UInt64.add_one_ne_zero_of_ne_max
      (genericCreate_step_spawn_nonce_ne_max spawn)
    obtain ⟨rfl, rfl⟩ := genericCreate_step_spawn_exact spawn
    refine ⟨?_, fun _ => different⟩
    obtain ⟨entry, transfer, childEq⟩ := Frame.enter_run_inv enter
    rw [childEq]
    change (entry.state.get a).nonce ≠ 0
    rw [Msg.benvAfterTransfer_get_nonce transfer a]
    change (((((d.state.incrNonce sevm.currentTarget).setStor address .empty).incrNonce
      address).get a).nonce) ≠ 0
    rw [State.incrNonce, State.setAccount_get_ne _ different]
    unfold State.setStor
    split
    · rw [State.get_setPresent_ne _ different]
      exact State.incrNonce_nonce_ne_zero nonwrap a nonceAt
    · rw [State.get_set_ne _ different]
      exact State.incrNonce_nonce_ne_zero nonwrap a nonceAt
  · obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
    refine ⟨?_, fun impossible => Bool.noConfusion impossible⟩
    obtain ⟨entry, transfer, childEq⟩ := Frame.enter_run_inv enter
    rw [childEq]
    change (entry.state.get a).nonce ≠ 0
    rw [Msg.benvAfterTransfer_get_nonce transfer a]
    change (d.state.get a).nonce ≠ 0
    rwa [← hprefix.state]

/-- A same-frame continuation preserves nonzero nonces, including a resumed
recursive child with arbitrary raw and settled outcomes. -/
theorem Exec.Deriv.ParentStep.nonce_ne_zero_noStateGas
    {node next : Exec.Deriv} (edge : Exec.Deriv.ParentStep next node)
    (hsg : node.sevm.benvStat.rules.stateGas = none) {a : Adr}
    (nonce : (node.devm.state.get a).nonce ≠ 0) :
    (next.devm.state.get a).nonce ≠ 0 := by
  cases edge with
  | cont step next => exact Evm.step_cont_nonce_ne_zero_noStateGas hsg step a nonce
  | doneOk step enter resumed next =>
    obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
    apply Xinst.nonce_ne_zero_of_body_noStateGas (x := x) (slot := .none) _ hsg trivial a nonce
    unfold Xinst.Run XStep.Run
    rw [spawn]
    exact ⟨_, RunFrame.of_done enter, resumed.symm⟩
  | runOk step enter child resumed next =>
    obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
    have childGas : _ := Evm.step_spawn_child_benvStat step enter
    apply Xinst.nonce_ne_zero_of_body_noStateGas (x := x) (slot := .some ⟨_, _⟩) _ hsg
      (fun committed owner nonceAt => Exec.nonce_ne_zero_committedPost_noStateGas
        child committed (by rw [childGas]; exact hsg) owner nonceAt) a nonce
    unfold Xinst.Run XStep.Run
    rw [spawn]
    exact ⟨_, RunFrame.of_run enter, resumed.symm⟩

/-- A nonce-protected account cannot be the target of this step's CREATE. -/
theorem Evm.step_codeAt_of_nonce_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {a : Adr} {slot : Xlot} {out : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (nonce : (pre.state.get a).nonce ≠ 0)
    (body : Xlot.Rel (Devm.CodeAt a) slot)
    (run : Step.Run (Evm.step ⟨pc, sevm, pre⟩) slot out) :
    Execution.Rel (Devm.CodeAt a) pre out := by
  apply ExecutionTrace.Evm.step_codeAt_noStateGas hsg
    (Xinst.avoidsAt_of_step (fun frame resume pc' child step enter create =>
      (Evm.step_spawn_nonce_noStateGas hsg step enter nonce).2 create)) body run

/-- A committed execution preserves the code at a nonce-protected address,
even when that code is empty. Discarded children use complete rollback. -/
theorem Exec.codeAt_of_nonce_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (nonce : (pre.state.get a).nonce ≠ 0) :
    (Execution.committedPost out committed).getCode a = pre.getCode a := by
  induction run with
  | @halt pc sevm pre out step =>
    cases out with
    | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post =>
      exact Evm.step_codeAt_of_nonce_noStateGas (slot := .none) hsg nonce trivial
        (by rw [step]; exact ⟨rfl, rfl⟩)
  | cont step next ih =>
    have head : Devm.CodeAt a _ _ :=
      Evm.step_codeAt_of_nonce_noStateGas (slot := .none) (out := .ok _) hsg nonce trivial
        (by rw [step]; exact ⟨rfl, rfl⟩)
    exact (ih committed hsg
      (Exec.Deriv.ParentStep.nonce_ne_zero_noStateGas (.cont step next) hsg nonce)).trans head
  | doneErr step enter resumed =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step enter resumed next ih =>
    have head : Devm.CodeAt a _ _ :=
      Evm.step_codeAt_of_nonce_noStateGas (slot := .none) (out := .ok _) hsg nonce trivial
        (by rw [step]; exact ⟨_, RunFrame.of_done enter, resumed.symm⟩)
    exact (ih committed hsg
      (Exec.Deriv.ParentStep.nonce_ne_zero_noStateGas
        (.doneOk step enter resumed next) hsg nonce)).trans head
  | runErr step enter child resumed ih =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre frame resume pc' childEvm raw post out
      step enter child resumed next childIH nextIH =>
    have head : Devm.CodeAt a pre post := by
      by_cases settles : frame.settlementCommits raw = true
      · have childCommit := Frame.raw_commits_of_settlementCommits settles
        have childGas : childEvm.sta.benvStat.rules.stateGas = none := by
          rw [Evm.step_spawn_child_benvStat step enter]; exact hsg
        have childCode := childIH childCommit childGas
          (Evm.step_spawn_nonce_noStateGas hsg step enter nonce).1
        have body : Xlot.Rel (Devm.CodeAt a) (.some ⟨childEvm, raw⟩) := by
          cases raw with
          | error error => simp only [Execution.commits, Bool.false_eq_true] at childCommit
          | ok childPost => exact childCode
        exact Evm.step_codeAt_of_nonce_noStateGas hsg nonce body
          (by rw [step]; exact ⟨_, RunFrame.of_run enter, resumed.symm⟩)
      · exact congrFun
          (Evm.step_spawn_rollback_code_stor_noStateGas hsg step enter resumed settles).1 a
    exact (nextIH committed hsg
      (Exec.Deriv.ParentStep.nonce_ne_zero_noStateGas
        (.runOk step enter child resumed next) hsg nonce)).trans head

/-- An entered constructor with zero target nonce and empty target code still
has empty target code at its raw committed endpoint, before code deposit. -/
theorem Exec.create_raw_target_code_empty_noStateGas
    {msg : Msg} {childEvm : Evm} {raw : Execution}
    (enter : (Frame.ofCreate msg).enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (committed : Execution.commits raw = true)
    (hsg : childEvm.sta.benvStat.rules.stateGas = none)
    (zeroNonce : (msg.benv.state.get msg.currentTarget).nonce = 0)
    (zeroSize : (msg.benv.state.getCode msg.currentTarget).size = 0) :
    (Execution.committedPost raw committed).getCode msg.currentTarget = .empty := by
  have seed : (childEvm.dyna.state.get msg.currentTarget).nonce ≠ 0 := by
    obtain ⟨entry, transfer, childEq⟩ := Frame.enter_run_inv enter
    rw [childEq]
    change (entry.state.get msg.currentTarget).nonce ≠ 0
    rw [Msg.benvAfterTransfer_get_nonce transfer msg.currentTarget]
    change (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
      msg.currentTarget).get msg.currentTarget).nonce ≠ 0
    rw [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce]
    have keep : ((msg.benv.state.setStor msg.currentTarget .empty).get
        msg.currentTarget).nonce = (msg.benv.state.get msg.currentTarget).nonce := by
      unfold State.setStor
      dsimp only
      split
      · rw [State.get_setPresent_self]
      · rw [State.get_set_self]
    rw [keep, zeroNonce]
    change (0 + 1 : UInt64) ≠ 0
    decide
  rw [Exec.codeAt_of_nonce_noStateGas child committed hsg seed,
    Frame.enter_run_getCode enter msg.currentTarget]
  change (processCreateMessage.msg msg).benv.state.getCode msg.currentTarget = .empty
  rw [processCreateMessage.msg_getCode]
  exact ByteArray.eq_empty_of_size_eq_zero zeroSize

/-- Complete successful child settlement preserves every nonempty code in
the child's raw result. In the CREATE case, the guarded target starts with
empty code and nonce one, so it is still empty before the final code deposit. -/
theorem Exec.spawn_codePreserve_of_settlementCommits_noStateGas
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {childEvm : Evm} {raw : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (settles : frame.settlementCommits raw = true) :
    Devm.CodePreserve (Execution.committedPost raw
      (Frame.raw_commits_of_settlementCommits settles)) post := by
  intro a nonempty
  have committed := Frame.raw_commits_of_settlementCommits settles
  have childGas : childEvm.sta.benvStat.rules.stateGas = none := by
    rw [Evm.step_spawn_child_benvStat step enter]; exact hsg
  obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with
    ⟨execution, shape, _⟩ |
    ⟨d, endowment, address, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · have unprotected := genericCreate_step_spawn_prepared_target_unprotected spawn
    have zeroNonce : ((d.state.incrNonce sevm.currentTarget).get address).nonce = 0 :=
      not_ne_iff.mp (fun nonzero => unprotected (Or.inl nonzero))
    have zeroSize : ((d.state.incrNonce sevm.currentTarget).getCode address).size = 0 :=
      not_ne_iff.mp (fun nonzero => unprotected (Or.inr nonzero))
    obtain ⟨rfl, rfl⟩ := genericCreate_step_spawn_exact spawn
    let prepared := addAccessedAddress
      (((d.withGasLeft (d.gasLeft - except64th d.gasLeft)).withReturnData
        []).incrNonce sevm.currentTarget) address
    let msg := createMsg sevm prepared (except64th d.gasLeft) endowment address
      ((d.memory.read mi ms).1)
    change (Frame.ofCreate msg).enter = .run childEvm at enter
    have rawEmpty : (Execution.committedPost raw committed).getCode address = .empty :=
      Exec.create_raw_target_code_empty_noStateGas enter child committed childGas zeroNonce zeroSize
    have different : address ≠ a := by
      intro equal
      apply nonempty
      rw [← equal, rawEmpty]
      exact ByteArray.toList_empty
    cases settledEq : (Frame.ofCreate msg).settle raw with
    | error error =>
      rw [settledEq] at resumed
      exact (Resume.create_run_error resumed).elim
    | ok settled =>
      have clean : settled.error.isSome = false := by
        change (Frame.ofCreate msg).settlementCommits raw = true at settles
        unfold Frame.settlementCommits at settles
        rw [settledEq] at settles
        change settled.error.isNone = true at settles
        cases h : settled.error with
        | none => rfl
        | some error => rw [h] at settles; cases settles
      have process := RunFrame.of_run (raw := raw) enter
      rw [settledEq] at process
      obtain ⟨inner, innerRun, _, deposited, stateEq⟩ :=
        ProcessCreateMessage.ok_setCode_state_of_clean process clean
      have rawEq := ProcessMessage.ok_state_eq_committedPost innerRun committed
      rw [settledEq] at resumed
      change post.state.getCode a = _
      rw [Resume.create_state resumed, stateEq, rawEq]
      exact State.setCode_get_code_ne different
  · obtain ⟨rfl, rfl⟩ := genericCall_step_spawn_exact spawn
    cases settledEq : (Frame.ofCall _).settle raw with
    | error error =>
      rw [settledEq] at resumed
      exact (Resume.call_run_error resumed).elim
    | ok settled =>
      have process := RunFrame.of_run (raw := raw) enter
      rw [settledEq] at process
      have stateEq := ProcessMessage.ok_state_eq_committedPost process committed
      rw [settledEq] at resumed
      change post.state.getCode a = _
      rw [Resume.call_state resumed, stateEq]
      rfl

private theorem retained_code_from_entry
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (nonempty : (pre.getCode a).toList ≠ []) {tail : List Exec.Deriv}
    (subset : ∀ n ∈ tail, n ∈ Exec.retainedNodes run) :
    (Execution.committedPost out committed).getCode a = pre.getCode a ∧
      ∀ n ∈ tail, n.devm.getCode a = pre.getCode a := by
  constructor
  · cases out with
    | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post => exact Exec.preserves_getCode run a nonempty
  · intro n member
    exact Exec.rawNodes_getCode run rfl nonempty n
      ((Exec.retainedNodes_sublist_rawNodes run).subset (subset n member))

/-- Once a retained node observes nonempty code, the same code is present at
every later retained node and at the committed endpoint. Earlier creation in
this very root is allowed; no root-entry code premise is used. -/
theorem Exec.retainedNodes_code_after_split_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    {before after : List Exec.Deriv} {n : Exec.Deriv}
    (split : Exec.retainedNodes run = before ++ n :: after)
    (nonempty : (n.devm.getCode a).toList ≠ []) :
    (Execution.committedPost out committed).getCode a = n.devm.getCode a ∧
      ∀ m ∈ after, m.devm.getCode a = n.devm.getCode a := by
  induction run generalizing before n after with
  | @halt pc sevm pre out step =>
    have original := split
    simp only [Exec.retainedNodes_eq_of_commits _ committed,
      Exec.retainedNodesOfCommits] at split
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      exact retained_code_from_entry (.halt step) committed nonempty
        (fun m member => (List.not_mem_nil member).elim)
    | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at split
      have length := congrArg List.length split.2
      simp only [List.length_nil, List.length_append, List.length_cons] at length
      omega
  | @cont pc sevm pre pc' post out step next ih =>
    have original := split
    rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
      ← Exec.retainedNodes_eq_of_commits next committed] at split
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      exact retained_code_from_entry (.cont step next) committed nonempty
        (fun m member => by rw [original]; exact List.mem_cons_of_mem _ member)
    | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at split
      exact ih committed hsg split.2 nonempty
  | doneErr step enter resumed =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @doneOk pc sevm pre frame resume pc' settled post out step enter resumed next ih =>
    have original := split
    rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
      ← Exec.retainedNodes_eq_of_commits next committed] at split
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      exact retained_code_from_entry (.doneOk step enter resumed next) committed nonempty
        (fun m member => by rw [original]; exact List.mem_cons_of_mem _ member)
    | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at split
      exact ih committed hsg split.2 nonempty
  | runErr step enter child resumed ih =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre frame resume pc' childEvm raw post out
      step enter child resumed next childIH nextIH =>
    have original := split
    by_cases settles : frame.settlementCommits raw = true
    · rw [Exec.retainedNodes_runOk_of_settlementCommits _ _ _ _ _ committed settles] at split
      cases before with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at split
        obtain ⟨rfl, rfl⟩ := split
        exact retained_code_from_entry (.runOk step enter child resumed next) committed nonempty
          (fun m member => by rw [original]; exact List.mem_cons_of_mem _ member)
      | cons b bs =>
        simp only [List.cons_append, List.cons.injEq] at split
        rcases List.split_append_cons split.2 with
          ⟨suffix, childSplit, afterEq⟩ | ⟨earlier, _, nextSplit⟩
        · have childCommit := Frame.raw_commits_of_settlementCommits settles
          have childGas : childEvm.sta.benvStat.rules.stateGas = none := by
            rw [Evm.step_spawn_child_benvStat step enter]; exact hsg
          obtain ⟨childLast, childLater⟩ := childIH childCommit childGas childSplit nonempty
          have resumedCode : post.getCode a = n.devm.getCode a := by
            exact (Exec.spawn_codePreserve_of_settlementCommits_noStateGas
              hsg step enter child resumed settles a
              (by rw [childLast]; exact nonempty)).trans childLast
          obtain ⟨last, later⟩ := retained_code_from_entry next committed
            (by rw [resumedCode]; exact nonempty) (fun m member => member)
          refine ⟨last.trans resumedCode, ?_⟩
          intro m member
          rw [afterEq] at member
          rcases List.mem_append.mp member with inChild | inNext
          · exact childLater m inChild
          · exact (later m inNext).trans resumedCode
        · exact nextIH committed hsg nextSplit nonempty
    · rw [Exec.retainedNodes_runOk_of_not_settlementCommits _ _ _ _ _ committed settles]
        at split
      cases before with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at split
        obtain ⟨rfl, rfl⟩ := split
        exact retained_code_from_entry (.runOk step enter child resumed next) committed nonempty
          (fun m member => by rw [original]; exact List.mem_cons_of_mem _ member)
      | cons b bs =>
        simp only [List.cons_append, List.cons.injEq] at split
        exact nextIH committed hsg split.2 nonempty

/-- Two original retained positions inherit the same nonempty code in order. -/
theorem Exec.retainedNodes_getCode_of_ordered_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    {before middle after : List Exec.Deriv} {m n : Exec.Deriv}
    (split : Exec.retainedNodes run = before ++ m :: (middle ++ n :: after))
    (nonempty : (m.devm.getCode a).toList ≠ []) :
    n.devm.getCode a = m.devm.getCode a := by
  exact (Exec.retainedNodes_code_after_split_noStateGas run committed hsg split nonempty).2 n
    (List.mem_append_right _ List.mem_cons_self)

end Blanc
