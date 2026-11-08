import Blanc.ExecutionCreateGuard
import Blanc.ExecutionHistoryInCodeAt
import Blanc.LockExclusion
import Blanc.ExecutionCellProvenance

/-! Code and nonce preservation from actual retained positions, including creation within a root. -/

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

/-- Complete successful child settlement preserves every raw nonce exactly. -/
theorem Exec.spawn_nonce_eq_of_settlementCommits_noStateGas
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {childEvm : Evm} {raw : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run childEvm)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (settles : frame.settlementCommits raw = true) :
    ∀ a, (post.state.get a).nonce =
      ((Execution.committedPost raw
        (Frame.raw_commits_of_settlementCommits settles)).state.get a).nonce := by
  intro a
  have committed := Frame.raw_commits_of_settlementCommits settles
  obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with
    ⟨execution, shape, _⟩ |
    ⟨d, endowment, address, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · obtain ⟨rfl, rfl⟩ := genericCreate_step_spawn_exact spawn
    cases settledEq : (Frame.ofCreate _).settle raw with
    | error error =>
      rw [settledEq] at resumed
      exact (Resume.create_run_error resumed).elim
    | ok settled =>
      have clean : settled.error.isSome = false := by
        change (Frame.ofCreate _).settlementCommits raw = true at settles
        unfold Frame.settlementCommits at settles
        rw [settledEq] at settles
        change settled.error.isNone = true at settles
        cases h : settled.error with
        | none => rfl
        | some error => rw [h] at settles; cases settles
      have process := RunFrame.of_run (raw := raw) enter
      rw [settledEq] at process
      obtain ⟨inner, innerRun, nonceEq⟩ :=
        ProcessCreateMessage.ok_nonce_eq_inner_of_clean process clean
      have rawEq := ProcessMessage.ok_state_eq_committedPost innerRun committed
      rw [settledEq] at resumed
      rw [Resume.create_state resumed, nonceEq, rawEq]
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
      rw [Resume.call_state resumed, stateEq]

/-- Every raw execution node inherits an entry nonzero nonce, including
nodes in children whose effects are later rolled back. -/
theorem Exec.rawNodes_nonce_ne_zero_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (run : Exec pc sevm pre out)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (nonce : (pre.state.get a).nonce ≠ 0) :
    ∀ n ∈ Exec.rawNodes run, (n.devm.state.get a).nonce ≠ 0 := by
  induction run with
  | halt step =>
    intro n member
    simp only [Exec.rawNodes, List.mem_singleton] at member
    subst n
    exact nonce
  | cont step next ih =>
    intro n member
    simp only [Exec.rawNodes, List.mem_cons] at member
    rcases member with rfl | member
    · exact nonce
    · exact ih hsg (Exec.Deriv.ParentStep.nonce_ne_zero_noStateGas
        (.cont step next) hsg nonce) n member
  | doneErr step enter resumed =>
    intro n member
    simp only [Exec.rawNodes, List.mem_singleton] at member
    subst n
    exact nonce
  | doneOk step enter resumed next ih =>
    intro n member
    simp only [Exec.rawNodes, List.mem_cons] at member
    rcases member with rfl | member
    · exact nonce
    · exact ih hsg (Exec.Deriv.ParentStep.nonce_ne_zero_noStateGas
        (.doneOk step enter resumed next) hsg nonce) n member
  | runErr step enter child resumed ih =>
    intro n member
    simp only [Exec.rawNodes, List.mem_cons] at member
    rcases member with rfl | member
    · exact nonce
    · exact ih (by rw [Evm.step_spawn_child_benvStat step enter]; exact hsg)
        (Evm.step_spawn_nonce_noStateGas hsg step enter nonce).1 n member
  | runOk step enter child resumed next childIH nextIH =>
    intro n member
    simp only [Exec.rawNodes, List.mem_cons, List.mem_append] at member
    rcases member with rfl | inChild | inNext
    · exact nonce
    · exact childIH (by rw [Evm.step_spawn_child_benvStat step enter]; exact hsg)
        (Evm.step_spawn_nonce_noStateGas hsg step enter nonce).1 n inChild
    · exact nextIH hsg (Exec.Deriv.ParentStep.nonce_ne_zero_noStateGas
        (.runOk step enter child resumed next) hsg nonce) n inNext

private theorem retained_nonce_from_entry
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (nonce : (pre.state.get a).nonce ≠ 0) {tail : List Exec.Deriv}
    (subset : ∀ n ∈ tail, n ∈ Exec.retainedNodes run) :
    ((Execution.committedPost out committed).state.get a).nonce ≠ 0 ∧
      ∀ n ∈ tail, (n.devm.state.get a).nonce ≠ 0 := by
  refine ⟨Exec.nonce_ne_zero_committedPost_noStateGas run committed hsg a nonce, ?_⟩
  intro n member
  exact Exec.rawNodes_nonce_ne_zero_noStateGas run hsg nonce n
    ((Exec.retainedNodes_sublist_rawNodes run).subset (subset n member))

/-- A retained nonzero nonce survives at all later retained nodes and at the
committed endpoint, including when the observation lies inside a child. -/
theorem Exec.retainedNodes_nonce_ne_zero_after_split_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    {before after : List Exec.Deriv} {n : Exec.Deriv}
    (split : Exec.retainedNodes run = before ++ n :: after)
    (nonce : (n.devm.state.get a).nonce ≠ 0) :
    ((Execution.committedPost out committed).state.get a).nonce ≠ 0 ∧
      ∀ m ∈ after, (m.devm.state.get a).nonce ≠ 0 := by
  induction run generalizing before n after with
  | @halt pc sevm pre out step =>
    have original := split
    simp only [Exec.retainedNodes_eq_of_commits _ committed,
      Exec.retainedNodesOfCommits] at split
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      exact retained_nonce_from_entry (.halt step) committed hsg nonce
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
      exact retained_nonce_from_entry (.cont step next) committed hsg nonce
        (fun m member => by rw [original]; exact List.mem_cons_of_mem _ member)
    | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at split
      exact ih committed hsg split.2 nonce
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
      exact retained_nonce_from_entry (.doneOk step enter resumed next) committed hsg nonce
        (fun m member => by rw [original]; exact List.mem_cons_of_mem _ member)
    | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at split
      exact ih committed hsg split.2 nonce
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
        exact retained_nonce_from_entry (.runOk step enter child resumed next) committed hsg nonce
          (fun m member => by rw [original]; exact List.mem_cons_of_mem _ member)
      | cons b bs =>
        simp only [List.cons_append, List.cons.injEq] at split
        rcases List.split_append_cons split.2 with
          ⟨suffix, childSplit, afterEq⟩ | ⟨earlier, _, nextSplit⟩
        · have childCommit := Frame.raw_commits_of_settlementCommits settles
          have childGas : childEvm.sta.benvStat.rules.stateGas = none := by
            rw [Evm.step_spawn_child_benvStat step enter]; exact hsg
          obtain ⟨childLast, childLater⟩ := childIH childCommit childGas childSplit nonce
          have resumedNonce : (post.state.get a).nonce ≠ 0 := by
            rw [Exec.spawn_nonce_eq_of_settlementCommits_noStateGas
              hsg step enter resumed settles a]
            exact childLast
          obtain ⟨last, later⟩ := retained_nonce_from_entry next committed hsg
            resumedNonce (fun m member => member)
          refine ⟨last, ?_⟩
          intro m member
          rw [afterEq] at member
          rcases List.mem_append.mp member with inChild | inNext
          · exact childLater m inChild
          · exact later m inNext
        · exact nextIH committed hsg nextSplit nonce
    · rw [Exec.retainedNodes_runOk_of_not_settlementCommits _ _ _ _ _ committed settles]
        at split
      cases before with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at split
        obtain ⟨rfl, rfl⟩ := split
        exact retained_nonce_from_entry (.runOk step enter child resumed next) committed hsg nonce
          (fun m member => by rw [original]; exact List.mem_cons_of_mem _ member)
      | cons b bs =>
        simp only [List.cons_append, List.cons.injEq] at split
        exact nextIH committed hsg split.2 nonce

/-- A later retained position cannot lose an earlier nonzero nonce. -/
theorem Exec.retainedNodes_nonce_ne_zero_of_ordered_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    {before middle after : List Exec.Deriv} {m n : Exec.Deriv}
    (split : Exec.retainedNodes run = before ++ m :: (middle ++ n :: after))
    (nonce : (m.devm.state.get a).nonce ≠ 0) :
    (n.devm.state.get a).nonce ≠ 0 := by
  exact (Exec.retainedNodes_nonce_ne_zero_after_split_noStateGas
    run committed hsg split nonce).2 n (List.mem_append_right _ List.mem_cons_self)

/-- An entered CREATE at a later retained position cannot reuse an address
whose nonce was already nonzero at the earlier retained position. -/
theorem Exec.retainedNodes_create_ne_of_ordered_nonce_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {a : Adr}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    {before middle after : List Exec.Deriv} {m n : Exec.Deriv}
    (split : Exec.retainedNodes run = before ++ m :: (middle ++ n :: after))
    (nonce : (m.devm.state.get a).nonce ≠ 0)
    {frame : Frame} {resume : Resume} {pc' : Nat} {child : Evm}
    (nodeGas : n.sevm.benvStat.rules.stateGas = none)
    (step : Evm.step ⟨n.pc, n.sevm, n.devm⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run child) (create : frame.isCreate = true) :
    frame.inner.currentTarget ≠ a := by
  exact (Evm.step_spawn_nonce_noStateGas nodeGas step enter
    (Exec.retainedNodes_nonce_ne_zero_of_ordered_noStateGas
      run committed hsg split nonce)).2 create

end Blanc
