import Blanc.ExecutionMessageEffects
import Blanc.ExecutionNoninterference
import Blanc.ExecutionTraceFrames
import Blanc.PrefixTransport

/-!
# Generic reentrancy-lock exclusion over the all-outcome frame tree

A reentrancy lock is one persistent storage cell `slot` of a storage owner `P`
that guarded code sets to a `locked` word before running a guarded body and
checks on entry to every guarded body.  This module proves, independently of
any contract, lifter, certificate or compiler, that such a discipline excludes
re-entry when the observed owner has nonempty world code at execution entry:

* `LockExclusion.LockSpec.lock_exclusion` (V+): while a frame of `P` running
  `L.code` is *active* (it has reached a mutating body start and has not
  since executed an SSTORE addressed at the lock slot), no frame spawned by
  it — nor any frame below that child — reaches a guarded body start in a
  `P`-owned frame running `L.code`.
* `LockExclusion.LockSpec.locked_core`: any derivation entered with the lock
  cell equal to `locked` at every same-frame ancestor keeps it equal at every
  raw node, performs no `P`-owned SSTORE addressed at the slot, retains no
  write to the cell, and enters no guarded body.

Everything is stated over Jaune's *raw* chronology (`Exec.rawNodes`,
`Exec.rawFrameRoots`, `Exec.Deriv.ParentPrefix`), never over committed or
settlement-retained frames: a callee that later reverts or runs out of gas has
still executed, and read-only reentrancy needs no commitment at all, so a
theorem that inspected only successful frames would miss exactly the attacks a
lock exists to prevent.  The outer execution, the active frame, the spawned
child and the entered frame may each succeed, revert or halt exceptionally.

The per-code obligation `LockSpec.Dominance` (every body start and every
slot-addressed SSTORE is preceded in its frame by a node where the lock was
not held, and every mutating body start holds the lock) and the per-world
facts `LockSpec.OwnerDiscipline`/`LockSpec.HashAvoidIn` are hypotheses here;
other units discharge them.
-/

namespace Blanc

open Jaune

/-! ## Generic storage facts about one driver step -/

/-- A successful non-`SSTORE` instruction preserves persistent storage at
each structurally protected owner. -/
theorem Ninst.none_getStor_eq_of_ne_sstore
    {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (run : Ninst.StepRun pc sevm pre n .none (.ok post))
    (notStore : n ≠ .reg .sstore)
    (owner : Adr) (protection : State.Protected pre.state owner) :
    Devm.getStor post owner = Devm.getStor pre owner := by
  cases n with
  | reg regular =>
      have regularRun : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post :=
        ((Step.run_ofExecution (xl := (.none : Xlot))).mp run).2.symm
      have store : regular ≠ .sstore := fun h => notStore (by rw [h])
      exact (congrFun (Rinst.preserves_stor store regularRun) owner).symm
  | exec executable =>
      simp only [Ninst.StepRun, Ninst.step_exec] at run
      exact Xinst.none_getStor_eq (XStep.run_toStep.mp run) owner protection
  | push bytes bound =>
      exact ((Ninst.push_instructionFrame_effectRec
        (hxs := bound) (xl := .none) trivial run).getStor owner).symm
  | dupn imm =>
      exact ((Ninst.dupn_instructionFrame_effectRec
        (xl := .none) trivial run).getStor owner).symm
  | swapn imm =>
      exact ((Ninst.swapn_instructionFrame_effectRec
        (xl := .none) trivial run).getStor owner).symm
  | exchange imm =>
      exact ((Ninst.exchange_instructionFrame_effectRec
        (xl := .none) trivial run).getStor owner).symm

/-- A continuing driver step preserves one persistent cell unless it is an
`SSTORE`, executed by that cell's owner, whose key operand is that cell's key. -/
theorem Evm.step_cont_getStor_get
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    {owner : Adr} {key : B256}
    (notStore : sevm.currentTarget = owner →
      Ninst.At sevm.code pc (.reg .sstore) → pre.stack.head? ≠ some key) :
    (Devm.getStor post owner).get key = (Devm.getStor pre owner).get key := by
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
              rw [← frame.getStor owner]
      | next instruction =>
          have nstep : Ninst.step ⟨pc, sevm, pre⟩ instruction =
              .cont pc' post := by
            rw [← Evm.step_next decoded]
            exact step
          have nrun : Ninst.StepRun pc sevm pre instruction .none (.ok post) := by
            unfold Ninst.StepRun
            rw [nstep]
            exact ⟨rfl, rfl⟩
          cases instruction with
          | exec executable =>
              simp only [Ninst.step_exec, XStep.toStep] at nstep
              cases actual : Xinst.step sevm pre executable with
              | spawn frame resume => rw [actual] at nstep; cases nstep
              | done out =>
                  rw [actual] at nstep
                  cases out with
                  | error error => cases nstep
                  | ok actualPost =>
                      cases nstep
                      exact congrArg (fun storage => storage.get key)
                        (Xinst.step_done_getStor hfork actual owner)
          | reg regular =>
              have run : Rinst.run ⟨pc, sevm, pre⟩ regular = .ok post :=
                ((Step.run_ofExecution (xl := (.none : Xlot))).mp nrun).2.symm
              by_cases store : regular = .sstore
              · subst regular
                by_cases own : sevm.currentTarget = owner
                · subst owner
                  have sstoreRun : Ninst.Run sevm pre Ninst.sstore post :=
                    ⟨.none, trivial, pc, nrun⟩
                  rcases of_run_sstore sstoreRun with ⟨written, value, popped⟩
                  rcases pref_of_split popped with ⟨rest, stackEq⟩
                  rw [sstore_getStor_set sstoreRun ⟨rest, stackEq⟩]
                  apply Stor.get_set_ne
                  intro same
                  apply notStore rfl decoded
                  simp only [Split, List.cons_append, List.nil_append] at stackEq
                  rw [stackEq, same]
                  rfl
                · rw [sstore_preserves_getStor_ne run own]
              · rw [← congrFun (Rinst.preserves_stor store run) owner]
          | push bytes bound =>
              exact congrArg (fun storage => storage.get key) ((Ninst.push_instructionFrame_effectRec
                (hxs := bound) (xl := .none) trivial nrun).getStor owner).symm
          | dupn imm =>
              exact congrArg (fun storage => storage.get key) ((Ninst.dupn_instructionFrame_effectRec
                (xl := .none) trivial nrun).getStor owner).symm
          | swapn imm =>
              exact congrArg (fun storage => storage.get key) ((Ninst.swapn_instructionFrame_effectRec
                (xl := .none) trivial nrun).getStor owner).symm
          | exchange imm =>
              exact congrArg (fun storage => storage.get key) ((Ninst.exchange_instructionFrame_effectRec
                (xl := .none) trivial nrun).getStor owner).symm

/-- An immediately completed spawn (precompile, failed entry) preserves
persistent storage at each structurally protected owner. -/
theorem Evm.step_doneOk_getStor_eq
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Jaune.Frame} {resume : Resume}
    {settled : Except (EvmError × State × AdrSet × Tra) Devm}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .done settled)
    (resumeRun : resume.run settled = .ok post)
    (owner : Adr) (protection : State.Protected pre.state owner) :
    Devm.getStor post owner = Devm.getStor pre owner := by
  rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
  apply Xinst.none_getStor_eq (sevm := sevm) (x := x) _ owner protection
  unfold Xinst.Run XStep.Run
  rw [spawn]
  exact ⟨settled, RunFrame.of_done enter, resumeRun.symm⟩

/-- An entered child preserves the storage of each structurally protected owner. -/
theorem Evm.step_spawn_enter_getStor
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Jaune.Frame} {resume : Resume} {child : Evm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run child)
    (owner : Adr) (protection : State.Protected pre.state owner) :
    Devm.getStor child.dyna owner = Devm.getStor pre owner := by
  rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
  have messageFacts : frame.inner.benv.state.getStor owner = pre.getStor owner ∧
      State.Protected frame.inner.benv.state owner := by
    rcases Xinst.step_shapeCovered sevm pre x hfork with
      ⟨execution, shape, -⟩ |
      ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
      ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
        ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
      rw [shape] at spawn
    · cases spawn
    · have nonce := UInt64.add_one_ne_zero_of_ne_max
        (genericCreate_step_spawn_nonce_ne_max spawn)
      have dProtected : State.Protected d.state owner := by
        rw [← hprefix.state]
        exact protection
      have targetNe : newAddress ≠ owner := by
        intro equal
        apply genericCreate_step_spawn_target_unprotected spawn
        rw [equal]
        exact dProtected
      rcases genericCreate_step_spawn_exact spawn with ⟨rfl, -⟩
      let prepared := addAccessedAddress
        (((d.withGasLeft (d.gasLeft - except64th d.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress
      have preparedStor : prepared.state.getStor owner = d.state.getStor owner :=
        congrFun (genericCreate_prepared_getStor sevm d newAddress nonce) owner
      have preparedProtection : State.Protected prepared.state owner := by
        change State.Protected (d.state.incrNonce sevm.currentTarget) owner
        unfold State.Protected
        by_cases equal : sevm.currentTarget = owner
        · subst owner
          left
          simpa only [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce] using nonce
        · rw [State.incrNonce, State.setAccount_get_ne _ equal]
          exact dProtected
      have preparedGet :
          (processCreateMessage.msg (createMsg sevm prepared (except64th d.gasLeft)
            endowment newAddress ((d.memory.read mi ms).1))).benv.state.get owner =
            prepared.state.get owner := by
        dsimp only [Frame.ofCreate, createMsg, processCreateMessage.msg, Msg.withBenv,
          Benv.setStor, Benv.incrNonce, Benv.clearStorageWritesIfEmpty, addCreatedAccount]
        rw [State.incrNonce, State.setAccount_get_ne _ targetNe,
          State.setStor, State.get_set_ne _ targetNe]
      refine ⟨(congrArg Acct.stor preparedGet).trans (preparedStor.trans ?_), ?_⟩
      · exact (hprefix.getStor owner).symm
      · change State.Protected
          (processCreateMessage.msg (createMsg sevm prepared (except64th d.gasLeft)
            endowment newAddress ((d.memory.read mi ms).1))).benv.state owner
        unfold State.Protected at preparedProtection ⊢
        rw [preparedGet]
        exact preparedProtection
    · rcases genericCall_step_spawn_exact spawn with ⟨rfl, -⟩
      refine ⟨(hprefix.getStor owner).symm, ?_⟩
      change State.Protected d.state owner
      rw [← hprefix.state]
      exact protection
  rcases Frame.enter_run_inv enter with ⟨benv, transfer, rfl⟩
  exact (benvAfterTransfer_ok_getStor transfer owner (Or.inr messageFacts.2)).trans
    messageFacts.1

/-- A child discarded by complete settlement preserves all parent storage,
including raw cells at unprotected owners. -/
theorem Evm.step_spawn_rollback_getStor
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Jaune.Frame} {resume : Resume} {child : Evm} {raw : Execution}
    (hfork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run child)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (discarded : frame.settlementCommits raw ≠ true) :
    Devm.getStor post = Devm.getStor pre := by
  rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
  rcases Xinst.step_shapeCovered sevm pre x hfork with
    ⟨execution, shape, -⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, shape⟩ <;>
    rw [shape] at spawn
  · cases spawn
  · have nonce := UInt64.add_one_ne_zero_of_ne_max
      (genericCreate_step_spawn_nonce_ne_max spawn)
    rcases genericCreate_step_spawn_exact spawn with ⟨rfl, rfl⟩
    cases settledEq : (Frame.ofCreate _).settle raw with
    | error error => rw [settledEq] at resumed; cases resumed
    | ok settled =>
      have error : settled.error.isSome = true := by
        unfold Frame.settlementCommits at discarded
        rw [settledEq] at discarded
        change settled.error.isNone ≠ true at discarded
        cases h : settled.error with
        | none => rw [h] at discarded; exact (discarded rfl).elim
        | some error => rfl
      have process := RunFrame.of_run (raw := raw) enter
      rw [settledEq] at process
      have rollback := ProcessCreateMessage.rollback_of_error process error
      rw [settledEq] at resumed
      have stateEq := (Resume.create_state resumed).trans rollback
      funext owner
      change post.state.getStor owner = pre.state.getStor owner
      rw [stateEq]
      exact (congrFun (genericCreate_prepared_getStor sevm d newAddress nonce) owner).trans
        (hprefix.getStor owner).symm
  · rcases genericCall_step_spawn_exact spawn with ⟨rfl, rfl⟩
    cases settledEq : (Frame.ofCall _).settle raw with
    | error error => rw [settledEq] at resumed; cases Resume.call_run_error resumed
    | ok settled =>
      have error : settled.error.isSome = true := by
        unfold Frame.settlementCommits at discarded
        rw [settledEq] at discarded
        change settled.error.isNone ≠ true at discarded
        cases h : settled.error with
        | none => rw [h] at discarded; exact (discarded rfl).elim
        | some error => rfl
      have process := RunFrame.of_run (raw := raw) enter
      rw [settledEq] at process
      have rollback := (ProcessMessage.rollback_of_error process error).1
      rw [settledEq] at resumed
      have stateEq := (Resume.call_state resumed).trans rollback
      funext owner
      change post.state.getStor owner = pre.state.getStor owner
      rw [stateEq]
      exact (hprefix.getStor owner).symm

/-- A successful regular instruction keeps every account nonce unchanged. -/
theorem Rinst.get_nonce_eq_of_ok {pc : Nat} {sevm : Sevm} {pre post : Devm} {r : Rinst}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : Rinst.run ⟨pc, sevm, pre⟩ r = .ok post) (owner : Adr) :
    (post.state.get owner).nonce = (pre.state.get owner).nonce := by
  by_cases store : r = .sstore
  · subst r
    simp only [Rinst.run, Rinst.runCore, fork.rules_stateGas_none] at run
    rcases Except.bind_eq_ok run with ⟨⟨key, first⟩, popKey, rest⟩
    rcases Except.bind_eq_ok rest with ⟨⟨value, second⟩, popValue, rest⟩
    rcases Except.bind_eq_ok rest with ⟨_, asserted, rest⟩
    rcases Except.bind_eq_ok rest with ⟨⟨third, gas⟩, warmed, rest⟩
    rcases Except.bind_eq_ok rest with ⟨gas', priced, rest⟩
    rcases Except.bind_eq_ok rest with ⟨fourth, refund, rest⟩
    rcases Except.bind_eq_ok rest with ⟨fifth, charged, rest⟩
    rcases Except.bind_eq_ok rest with ⟨_, asserted', final⟩
    have eq1 : pre.state = first.state := (Devm.pop_of_pop popKey).state
    have eq2 : first.state = second.state := (Devm.pop_of_pop popValue).state
    have eq3 : second.state = third.state := by
      split at warmed <;>
        have projected := congrArg (fun pair : Devm × Nat => pair.1.state)
          (Except.ok.inj warmed) <;>
        exact (Devm.balReadStorage_state sevm.benvStat.rules
          sevm.currentTarget key second).symm.trans projected
    have eq4 : third.state = fourth.state := by
      have projected := congrArg Devm.state (Except.ok.inj refund)
      exact projected
    have eq5 : fourth.state = fifth.state := (chargeGas_worldEq_of_ok charged).1
    have eq : pre.state = fifth.state := eq1.trans (eq2.trans (eq3.trans (eq4.trans eq5)))
    rw [← Except.ok.inj final]
    change ((fifth.state.setStorVal sevm.currentTarget key value).get owner).nonce = _
    dsimp only [State.setStorVal]
    by_cases equal : sevm.currentTarget = owner
    · subst owner
      rw [State.get_set_self]
      exact congrArg (fun st : State => (st.get sevm.currentTarget).nonce) eq.symm
    · rw [State.get_set_ne _ equal]
      exact congrArg (fun st : State => (st.get owner).nonce) eq.symm
  · by_cases transient : r = .tstore
    · subst r
      have frame := Rinst.tstore_run_transientWriteFrame pc pre sevm
      rw [run] at frame
      have stateEq : pre.state = post.state := frame.state
      rw [← stateEq]
    · rw [← Rinst.preserves_state store transient run]

/-- Successful ordinary instructions preserve nonzero account nonces. -/
theorem Ninst.nonce_ne_zero_of_none
    {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : Ninst.StepRun pc sevm pre n .none (.ok post))
    (owner : Adr) (nonce : (pre.state.get owner).nonce ≠ 0) :
    (post.state.get owner).nonce ≠ 0 := by
  cases n with
  | reg regular =>
      rw [Rinst.get_nonce_eq_of_ok fork ((Step.run_ofExecution.mp run).2.symm) owner]
      exact nonce
  | exec executable =>
      simp only [Ninst.StepRun, Ninst.step_exec] at run
      exact Xinst.nonce_ne_zero_of_body (XStep.run_toStep.mp run) fork trivial owner nonce
  | push bytes bound =>
      have stateEq : pre.state = post.state := (Ninst.push_instructionFrame_effectRec (xl := .none) trivial run).state
      rwa [← stateEq]
  | dupn imm =>
      have stateEq : pre.state = post.state := (Ninst.dupn_instructionFrame_effectRec (xl := .none) trivial run).state
      rwa [← stateEq]
  | swapn imm =>
      have stateEq : pre.state = post.state := (Ninst.swapn_instructionFrame_effectRec (xl := .none) trivial run).state
      rwa [← stateEq]
  | exchange imm =>
      have stateEq : pre.state = post.state := (Ninst.exchange_instructionFrame_effectRec (xl := .none) trivial run).state
      rwa [← stateEq]

/-- A continuing driver step preserves nonzero nonces. -/
theorem Evm.step_cont_nonce_ne_zero
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    (owner : Adr) (nonce : (pre.state.get owner).nonce ≠ 0) :
    (post.state.get owner).nonce ≠ 0 := by
  cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
  | none => unfold Evm.step at step; rw [decoded] at step; cases step
  | some instruction =>
      cases instruction with
      | last last => rw [Evm.step_last decoded] at step; cases step
      | jump jumpInst =>
          rw [Evm.step_jump decoded] at step
          cases jumped : Jinst.run ⟨pc, sevm, pre⟩ jumpInst with
          | error error => rw [jumped] at step; cases step
          | ok pair =>
              rcases pair with ⟨actualPc, actualPost⟩
              rw [jumped] at step
              cases step
              have frame := Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ jumpInst
              rw [jumped] at frame
              rwa [← frame.state]
      | next instruction =>
          have stepped : Ninst.step ⟨pc, sevm, pre⟩ instruction = .cont pc' post := by
            rw [← Evm.step_next decoded]
            exact step
          have nrun : Ninst.StepRun pc sevm pre instruction .none (.ok post) := by
            unfold Ninst.StepRun
            rw [stepped]
            exact ⟨rfl, rfl⟩
          exact Ninst.nonce_ne_zero_of_none fork nrun owner nonce

/-- A successful terminating instruction keeps all account nonces unchanged. -/
theorem Linst.get_nonce_eq_of_ok {sevm : Sevm} {pre post : Devm} {last : Linst}
    (fork : CoveredFork sevm.benvStat.fork) (run : Linst.Run sevm pre last (.ok post))
    (owner : Adr) : (post.state.get owner).nonce = (pre.state.get owner).nonce := by
  by_cases destroy : last = .selfdestruct
  · subst last
    simp only [Linst.Run, Linst.run, fork.rules_stateGas_none,
      Devm.balReadAccount_of_bal_none fork.rules_bal_none,
      ne_eq, Except.bind_ok, ite_not, Lean.Elab.WF.paramLet] at run
    rcases Except.bind_eq_ok run with ⟨⟨donee, first⟩, pop, rest⟩
    rcases Except.bind_eq_ok rest with ⟨second, charge, rest⟩
    rcases Except.bind_eq_ok rest with ⟨_, asserted, rest⟩
    rcases Except.bind_eq_ok rest with ⟨third, sub, final⟩
    have subSome : second.subBal sevm.currentTarget
        (first.getAcct sevm.currentTarget).bal = some third := by
      cases eq : second.subBal sevm.currentTarget (first.getAcct sevm.currentTarget).bal
      · rw [eq] at sub
        contradiction
      · rw [eq] at sub
        injection sub with equal
        subst equal
        rfl
    have subState : second.state.subBal sevm.currentTarget
        (first.getAcct sevm.currentTarget).bal = some third.state := by
      dsimp only [Devm.subBal, Option.bind_eq_bind, Option.bind] at subSome
      cases eq : second.state.subBal sevm.currentTarget (first.getAcct sevm.currentTarget).bal
      · rw [eq] at subSome
        contradiction
      · rw [eq] at subSome
        injection subSome with equal
        subst equal
        rfl
    have stateEq : pre.state = second.state := by
      have firstEq : pre.state = first.state :=
        (liftMach_worldEq_of_ok (core := Mach.popToAdr) pop).1
      rw [firstEq, ← (chargeGas_worldEq_of_ok charge).1]
      split <;> simp only [Devm.balReadAccount_state, addAccessedAddress_state]
    let transferred := third.addBal donee (first.getAcct sevm.currentTarget).bal
    have nonceEq : (transferred.state.get owner).nonce = (pre.state.get owner).nonce := by
      change ((third.state.addBal donee _).get owner).nonce = _
      rw [State.addBal, State.setBal_get_nonce, (State.of_subBal subState).2,
        State.setBal_get_nonce, ← stateEq]
    have postEq : (post.state.get owner).nonce = (transferred.state.get owner).nonce := by
      dsimp only [transferred] at final ⊢
      by_cases deleted : sevm.currentTarget ∈
          (third.addBal donee (first.getAcct sevm.currentTarget).bal).createdAccounts
      · simp only [deleted, ite_eq_left] at final
        rw [← Except.ok.inj final]
        exact State.setBal_get_nonce
      · simp only [deleted] at final
        rw [← Except.ok.inj final]
    exact postEq.trans nonceEq
  · have frame := Linst.run_instructionFrame sevm pre last destroy
    rw [run] at frame
    have stateEq : pre.state = post.state := frame.state
    rw [← stateEq]

/-- Nonzero account nonces survive every actual committed execution on a covered fork. -/
theorem Exec.nonce_ne_zero_committedPost
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (fork : CoveredFork sevm.benvStat.fork) (owner : Adr)
    (nonce : (pre.state.get owner).nonce ≠ 0) :
    ((Execution.committedPost out committed).state.get owner).nonce ≠ 0 := by
  revert committed fork owner
  induction run with
  | @halt pc sevm pre out step =>
      intro committed fork owner nonce
      cases out with
      | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
      | ok post =>
          cases decoded : Evm.getInst ⟨pc, sevm, pre⟩ with
          | none => unfold Evm.step at step; rw [decoded] at step; cases step
          | some instruction =>
              cases instruction with
              | last last =>
                  rw [Evm.step_last decoded] at step
                  have lastRun : Linst.Run sevm pre last (.ok post) := Step.halt.inj step
                  change (post.state.get owner).nonce ≠ 0
                  rw [Linst.get_nonce_eq_of_ok fork lastRun owner]
                  exact nonce
              | next next =>
                  rw [Evm.step_next decoded] at step
                  exact (Ninst.step_ne_halt_ok step).elim
              | jump jumpInst =>
                  rw [Evm.step_jump decoded] at step
                  cases jumped : Jinst.run ⟨pc, sevm, pre⟩ jumpInst <;>
                    rw [jumped] at step <;> cases step
  | cont step next ih =>
      intro committed fork owner nonce
      exact ih committed fork owner (Evm.step_cont_nonce_ne_zero fork step owner nonce)
  | doneErr step enter resumed =>
      intro committed
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | @doneOk nodePc nodeSevm nodePre frame resume nextPc settled post final step enter resumed next ih =>
      intro committed fork owner nonce
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have xrun : Xinst.Run nodeSevm nodePre x .none (.ok post) := by
        unfold Xinst.Run XStep.Run
        rw [spawn]
        exact ⟨_, RunFrame.of_done enter, resumed.symm⟩
      exact ih committed fork owner (Xinst.nonce_ne_zero_of_body xrun fork trivial owner nonce)
  | runErr step enter child resumed ih =>
      intro committed
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk nodePc nodeSevm nodePre frame resume nextPc childEvm raw post final step enter child resumed next childIH nextIH =>
      intro committed fork owner nonce
      rcases Evm.step_spawn_inv step with ⟨x, _, spawn, _⟩
      have childFork := Evm.step_spawn_child_fork step enter fork
      have xrun : Xinst.Run nodeSevm nodePre x (.some ⟨childEvm, raw⟩) (.ok post) := by
        unfold Xinst.Run XStep.Run
        rw [spawn]
        exact ⟨_, RunFrame.of_run enter, resumed.symm⟩
      have body : Xlot.NonceNonzero (.some ⟨childEvm, raw⟩) :=
        fun commit childOwner childNonce => childIH commit childFork childOwner childNonce
      exact nextIH committed fork owner (Xinst.nonce_ne_zero_of_body xrun fork body owner nonce)

/-- Same-frame prefixes preserve every entry-code-nonempty owner's code. -/
theorem Exec.Deriv.ParentPrefix.codePreserve {root tail : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix root tail) : Devm.CodePreserve root.devm tail.devm := by
  induction chain with
  | refl => exact codePreserve_refl_trans.1 _
  | step head rest ih =>
      intro owner nonempty
      have first := Blanc.Exec.Deriv.ParentStep.codePreserve head owner nonempty
      exact (ih owner (by rw [first]; exact nonempty)).trans first

/-- Every raw frame root retains the code of each entry-code-nonempty owner. -/
theorem Exec.rawFrameRoots_codePreserve {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) (owner : Adr)
    (nonempty : (pre.getCode owner).toList ≠ []) :
    ∀ root ∈ Exec.rawFrameRoots run, root.devm.getCode owner = pre.getCode owner := by
  revert nonempty
  induction run with
  | halt =>
      intro nonempty root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst root
      rfl
  | doneErr =>
      intro nonempty root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst root
      rfl
  | @cont pc sevm pre pc' post out step next ih =>
      intro nonempty root member
      have equal := Blanc.Exec.Deriv.ParentStep.codePreserve (.cont step next) owner nonempty
      have nextNonempty : (post.getCode owner).toList ≠ [] := by rw [equal]; exact nonempty
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact (ih nextNonempty root (by simp only [Exec.rawFrameRoots, List.mem_cons]; exact Or.inr member)).trans equal
  | @doneOk pc sevm pre frame resume pc' settled post out step enter resumeRun next ih =>
      intro nonempty root member
      have equal := Blanc.Exec.Deriv.ParentStep.codePreserve (.doneOk step enter resumeRun next) owner nonempty
      have nextNonempty : (post.getCode owner).toList ≠ [] := by rw [equal]; exact nonempty
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact (ih nextNonempty root (by simp only [Exec.rawFrameRoots, List.mem_cons]; exact Or.inr member)).trans equal
  | @runErr pc sevm pre frame resume pc' childEvm raw error step enter child resumeRun childIH =>
      intro nonempty root member
      have equal := (Evm.step_spawn_child step enter).2.1 owner
      have childNonempty : (childEvm.dyna.getCode owner).toList ≠ [] := by rw [equal]; exact nonempty
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | childRoot | childDesc
      · rfl
      · subst root
        exact equal
      · exact (childIH childNonempty root (by simp only [Exec.rawFrameRoots, List.mem_cons]; exact Or.inr childDesc)).trans equal
  | @runOk pc sevm pre frame resume pc' childEvm raw post out step enter child resumeRun next childIH nextIH =>
      intro nonempty root member
      have childEqual := (Evm.step_spawn_child step enter).2.1 owner
      have childNonempty : (childEvm.dyna.getCode owner).toList ≠ [] := by rw [childEqual]; exact nonempty
      have nextEqual := Blanc.Exec.Deriv.ParentStep.codePreserve (.runOk step enter child resumeRun next) owner nonempty
      have nextNonempty : (post.getCode owner).toList ≠ [] := by rw [nextEqual]; exact nonempty
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at member
      rcases member with rfl | childRoot | childDesc | nextDesc
      · rfl
      · subst root
        exact childEqual
      · exact (childIH childNonempty root (by simp only [Exec.rawFrameRoots, List.mem_cons]; exact Or.inr childDesc)).trans childEqual
      · exact (nextIH nextNonempty root (by simp only [Exec.rawFrameRoots, List.mem_cons]; exact Or.inr nextDesc)).trans nextEqual

/-- Every actually entered descendant frame starts at program counter zero
and inherits the covered fork of its ancestors. -/
theorem Exec.rawFrameDescendants_entry
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hfork : CoveredFork sevm.benvStat.fork) :
    ∀ root ∈ Exec.rawFrameDescendants run,
      root.pc = 0 ∧ CoveredFork root.sevm.benvStat.fork := by
  induction run with
  | halt => simp only [rawFrameDescendants, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | cont hstep next ih =>
      simpa only [Exec.rawFrameDescendants] using ih hfork
  | doneErr => simp only [rawFrameDescendants, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | doneOk hstep henter hresume next ih =>
      simpa only [Exec.rawFrameDescendants] using ih hfork
  | runErr hstep henter child hresume ih =>
      have childFork := Evm.step_spawn_child_fork hstep henter hfork
      intro root member
      simp only [Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨Frame.enter_run_pc henter, childFork⟩
      · exact ih childFork root member
  | runOk hstep henter child hresume next childIh nextIh =>
      have childFork := Evm.step_spawn_child_fork hstep henter hfork
      intro root member
      simp only [Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | member | member
      · exact ⟨Frame.enter_run_pc henter, childFork⟩
      · exact childIh childFork root member
      · exact nextIh hfork root member

/-- Same-frame prefixes are antisymmetric. -/
theorem Exec.Deriv.ParentPrefix.antisymm
    {left right : Exec.Deriv}
    (forward : Exec.Deriv.ParentPrefix left right)
    (back : Exec.Deriv.ParentPrefix right left) : left = right := by
  cases forward with
  | refl => rfl
  | step head rest =>
      exact (Blanc.Exec.Deriv.ParentStep.not_parentPrefix_back head rest back).elim

namespace LockExclusion

open Jaune.Exec.Deriv

/-! ## The specification -/

/-- A reentrancy lock: the code that implements it, the lock slot and its
held word, the pcs of every guarded body start (`bodies`) and of the body
starts reached only after the lock has been set (`mutBodies`). -/
structure LockSpec where
  code : ByteArray
  slot : B256
  locked : B256
  bodies : List Nat
  mutBodies : List Nat

/-- The node executes an `SSTORE` whose key operand is `key`. -/
def SstoreAt (n : Exec.Deriv) (key : B256) : Prop :=
  Ninst.At n.sevm.code n.pc (.reg .sstore) ∧ n.devm.stack.head? = some key

/-- The word held in `P`'s storage cell `slot`. -/
def lockAt (P : Adr) (slot : B256) (d : Devm) : B256 :=
  (Devm.getStor d P).get slot

/-- A frame root at pc 0 whose storage owner is `P` and whose code is `code`. -/
def CPFrame (P : Adr) (code : ByteArray) (F : Exec.Deriv) : Prop :=
  F.pc = 0 ∧ F.sevm.currentTarget = P ∧ F.sevm.code = code

/-- The code contains no `SSTORE` at any decoded instruction boundary. -/
def NoSstore (code : ByteArray) : Prop :=
  ∀ pc, ¬ Ninst.At code pc (.reg .sstore)

/-- Trace-local hash avoidance: every `KECCAK256` actually executed in the
frame rooted at `F` leaves a digest different from `slot`.  This quantifies
over executed hashes only, never over all inputs of a shape. -/
def HashAvoid (slot : B256) (F : Exec.Deriv) : Prop :=
  ∀ x y, ParentPrefix F x → ParentStep y x →
    Ninst.At x.sevm.code x.pc (.reg .keccak256) → y.devm.stack.head? ≠ some slot

namespace LockSpec

/-- `Active L P F h`: `F` is a frame of `P` running `L.code`, and on its way to
`h` it reached a mutating body start `b` after which no node strictly before
`h` executed an `SSTORE` addressed at the lock slot.  Activity therefore ends
at the frame's first concrete write to the slot, whatever value it writes. -/
def Active (L : LockSpec) (P : Adr) (F h : Exec.Deriv) : Prop :=
  CPFrame P L.code F ∧ ParentPrefix F h ∧
    ∃ b, ParentPrefix F b ∧ ParentPrefix b h ∧ b.pc ∈ L.mutBodies ∧
      ∀ x, ParentPrefix b x → ParentPrefix x h → x ≠ h → ¬ SstoreAt x L.slot

/-- `Enters L P G`: the frame rooted at `G` is a frame of `P` running `L.code`
that reaches some guarded body start, whether or not it later succeeds. -/
def Enters (L : LockSpec) (P : Adr) (G : Exec.Deriv) : Prop :=
  CPFrame P L.code G ∧ ∃ x, ParentPrefix G x ∧ x.pc ∈ L.bodies

/-- Per-code dominance obligation (discharged from a certificate elsewhere):
in every frame running `L.code` on a covered fork whose executed hashes avoid
the slot,
(a) every body start and every slot-addressed `SSTORE` is preceded, in its
frame, by a node where the lock cell did not hold `locked`; and (c) every
mutating body start holds `locked`. -/
def Dominance (L : LockSpec) : Prop :=
  ∀ F : Exec.Deriv, F.pc = 0 → CoveredFork F.sevm.benvStat.fork →
    F.sevm.code = L.code → HashAvoid L.slot F →
    ∀ n, ParentPrefix F n →
      ((n.pc ∈ L.bodies ∨ SstoreAt n L.slot) →
        ∃ m, ParentPrefix F m ∧ ParentPrefix m n ∧
          lockAt F.sevm.currentTarget L.slot m.devm ≠ L.locked) ∧
      (n.pc ∈ L.mutBodies →
        lockAt F.sevm.currentTarget L.slot n.devm = L.locked)

/-- Owner discipline: every frame of the execution that owns `P`'s storage
runs `L.code` or a code without `SSTORE`. -/
def OwnerDiscipline (L : LockSpec) (P : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : Prop :=
  ∀ G ∈ Exec.rawFrameRoots run,
    G.sevm.currentTarget = P → G.sevm.code = L.code ∨ NoSstore G.sevm.code

/-- Every frame of `P` running `L.code` in the execution avoids the lock slot
with its executed hashes. -/
def HashAvoidIn (L : LockSpec) (P : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : Prop :=
  ∀ G ∈ Exec.rawFrameRoots run, CPFrame P L.code G → HashAvoid L.slot G

end LockSpec

/-- `h` spawns the entered child frame rooted at the second derivation,
whether the parent then resumes (`runOk`) or fails to resume (`runErr`). -/
inductive Spawns : Exec.Deriv → Exec.Deriv → Prop
  | runErr {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
      {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
      {raw : Execution} {error : EvmError × Devm}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (henter : frame.enter = .run childEvm)
      (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (hresume : resume.run (frame.settle raw) = .error error) :
      Spawns ⟨pc, sevm, pre, .error error, .runErr hstep henter child hresume⟩
        ⟨childEvm.pc, childEvm.sta, childEvm.dyna, raw, child⟩
  | runOk {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
      {raw out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (henter : frame.enter = .run childEvm)
      (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (hresume : resume.run (frame.settle raw) = .ok post)
      (next : Exec pc' sevm post out) :
      Spawns ⟨pc, sevm, pre, out, .runOk hstep henter child hresume next⟩
        ⟨childEvm.pc, childEvm.sta, childEvm.dyna, raw, child⟩

/-! ## Proof -/

variable (L : LockSpec) (P : Adr)

/-- The frame-local facts the proof needs about one frame root. -/
def FrameOK (G : Exec.Deriv) : Prop :=
  (G.sevm.currentTarget = P → G.sevm.code = L.code ∨ NoSstore G.sevm.code) ∧
    (CPFrame P L.code G → HashAvoid L.slot G)

/-- What the proof establishes at every reached node. -/
def NodeSafe (x : Exec.Deriv) : Prop :=
  lockAt P L.slot x.devm = L.locked ∧
    ¬ (x.sevm.currentTarget = P ∧ SstoreAt x L.slot) ∧
    ¬ (x.sevm.currentTarget = P ∧ x.sevm.code = L.code ∧ x.pc ∈ L.bodies)

/-- The lock cell holds `locked` at every same-frame node from `B` to `E`. -/
def LockedFrom (B E : Exec.Deriv) : Prop :=
  ∀ x, ParentPrefix B x → ParentPrefix x E →
    lockAt P L.slot x.devm = L.locked

variable {L P}

theorem lockedFrom_self {E : Exec.Deriv}
    (locked : lockAt P L.slot E.devm = L.locked) : LockedFrom L P E E := by
  intro x forward back
  rcases Exec.Deriv.ParentPrefix.antisymm forward back with rfl
  exact locked

theorem lockedFrom_step {F E N : Exec.Deriv}
    (anc : LockedFrom L P F E) (reach : ParentPrefix F E)
    (edge : ParentStep N E) (locked : lockAt P L.slot N.devm = L.locked) :
    LockedFrom L P F N := by
  intro x hFx hxN
  rcases Blanc.Exec.Deriv.ParentPrefix.linear hFx reach with before | after
  · exact anc x hFx before
  · rcases (Blanc.Exec.Deriv.ParentStep.parentPrefix_iff edge).mp after with
      rfl | hNx
    · exact anc x hFx (.refl _)
    · rw [Exec.Deriv.ParentPrefix.antisymm hxN hNx]
      exact locked

/-- The node heading a same-frame prefix whose every node held the lock is
itself safe: dominance forbids its being a body start or slot-addressed
`SSTORE` in a frame of `P` running `L.code`, and owner discipline forbids any
other `P`-owned frame from writing storage. -/
theorem nodeSafe_head (dom : L.Dominance) {F E : Exec.Deriv}
    (pc0 : F.pc = 0) (reach : ParentPrefix F E) (ok : FrameOK L P F)
    (eFork : CoveredFork E.sevm.benvStat.fork)
    (anc : LockedFrom L P F E) : NodeSafe L P E := by
  have sevmEq : E.sevm = F.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq reach
  have dominated : ∀ owned : F.sevm.currentTarget = P,
      F.sevm.code = L.code → (E.pc ∈ L.bodies ∨ SstoreAt E L.slot) → False := by
    intro owned code bad
    rcases (dom F pc0 (by rw [← sevmEq]; exact eFork) code
        (ok.2 ⟨pc0, owned, code⟩) E reach).1 bad with
      ⟨m, hFm, hmE, unlocked⟩
    rw [owned] at unlocked
    exact unlocked (anc m hFm hmE)
  refine ⟨anc E reach (.refl _), ?_, ?_⟩
  · rintro ⟨owned, store⟩
    rw [sevmEq] at owned
    rcases ok.1 owned with code | noStore
    · exact dominated owned code (Or.inr store)
    · exact noStore E.pc (by rw [← sevmEq]; exact store.1)
  · rintro ⟨owned, code, body⟩
    rw [sevmEq] at owned code
    exact dominated owned code (Or.inl body)

/-- A frame all of whose raw nodes are safe retains no write to the lock
cell. -/
theorem noRetainedWriteTo_of_nodeSafe
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (safe : ∀ x ∈ Exec.rawNodes run, NodeSafe L P x) :
    Exec.NoRetainedWriteTo run P L.slot := by
  intro event member hmatch
  rcases Exec.exists_successfulSstore_of_mem_retainedStorageWrites
      (root := (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv))
      (event := event) member with ⟨write, -, rfl⟩
  have identities := Exec.StorageWrite.matches_eq_true.mp hmatch
  have decoded := write.occurrence.decoded
  rw [write.instruction_eq] at decoded
  rcases pref_of_split write.popped with ⟨rest, stackEq⟩
  apply (safe _ write.occurrence.reached).2.1
  refine ⟨identities.1, decoded, ?_⟩
  simp only [Split] at stackEq
  rw [stackEq]
  simpa only [List.cons_append, List.nil_append, List.head?_cons, Option.some.injEq,
    Exec.SuccessfulSstoreOccurrence.storageWrite] using identities.2

/-- A parent resuming from a child all of whose raw nodes are safe finds the
lock cell where it left it: a committed child retained no write to it, and a
failed one was rolled back. -/
theorem resume_lockAt
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
    {raw : Execution}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok post)
    (nonempty : (pre.getCode P).toList ≠ [])
    (safe : ∀ x ∈ Exec.rawNodes child, NodeSafe L P x) :
    lockAt P L.slot post = lockAt P L.slot pre := by
  rcases Evm.step_spawn_inv hstep with ⟨x, _, spawn, _⟩
  have childFork := Evm.step_spawn_child_fork hstep henter hfork
  have replay := Xinst.storageReplay_some_of_body spawn
    (RunFrame.of_run henter) hresume
    (fun committed => Exec.storageReplay_committedPost child committed childFork)
    hfork
  have entry : (Devm.getStor childEvm.dyna P).get L.slot =
      (Devm.getStor pre P).get L.slot := by
    rw [Evm.step_spawn_enter_getStor hfork hstep henter P (State.Protected.of_code_ne_nil nonempty)]
  have childNonempty : (childEvm.dyna.getCode P).toList ≠ [] := by
    rw [(Evm.step_spawn_child hstep henter).2.1 P]
    exact nonempty
  unfold lockAt
  rw [replay.2 P nonempty L.slot]
  split
  · rename_i settles
    have committed := Frame.raw_commits_of_settlementCommits settles
    have throughChild :=
      (Exec.storageReplay_committedPost child committed childFork).2 P childNonempty L.slot
    have unchanged := Exec.committedCell_eq_of_noRetainedWriteTo child
      committed childFork P L.slot childNonempty (noRetainedWriteTo_of_nodeSafe child safe)
    rw [← entry, ← throughChild, unchanged]
  · rfl

/-- The core induction.  From any node `E` of a frame rooted at `F` whose
same-frame nodes up to `E` all held the lock, every raw node of `E`'s
derivation — its own frame's continuation and every frame entered below it,
whatever their outcomes — is safe. -/
theorem nodeSafe_of_lockedFrom (dom : L.Dominance) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
      (run : Exec pc sevm pre out) (F : Exec.Deriv),
      F.pc = 0 → ParentPrefix F ⟨pc, sevm, pre, out, run⟩ → FrameOK L P F →
      (∀ G ∈ Exec.rawFrameDescendants run, FrameOK L P G) →
      CoveredFork sevm.benvStat.fork →
      (pre.getCode P).toList ≠ [] →
      LockedFrom L P F ⟨pc, sevm, pre, out, run⟩ →
      ∀ x ∈ Exec.rawNodes run, NodeSafe L P x := by
  intro pc sevm pre out run
  induction run with
  | halt hstep =>
      intro F pc0 reach ok _ hfork nonempty anc x member
      simp only [Exec.rawNodes, List.mem_singleton] at member
      subst x
      exact nodeSafe_head dom pc0 reach ok hfork anc
  | doneErr hstep henter hresume =>
      intro F pc0 reach ok _ hfork nonempty anc x member
      simp only [Exec.rawNodes, List.mem_singleton] at member
      subst x
      exact nodeSafe_head dom pc0 reach ok hfork anc
  | @cont _ _ _ _ post _ hstep next ih =>
      intro F pc0 reach ok okDesc hfork nonempty anc x member
      have head := nodeSafe_head dom pc0 reach ok hfork anc
      have edge := ParentStep.cont hstep next
      have locked : lockAt P L.slot post = L.locked := by
        unfold lockAt
        rw [Evm.step_cont_getStor_get hfork hstep (fun owned decoded key =>
          head.2.1 ⟨owned, decoded, key⟩)]
        exact head.1
      simp only [Exec.rawNodes, List.mem_cons] at member
      rcases member with rfl | member
      · exact head
      · exact ih F pc0 (reach.snoc edge) ok
          (by simpa only [Exec.rawFrameDescendants] using okDesc) hfork
          (by rw [Blanc.Exec.Deriv.ParentStep.codePreserve edge P nonempty]; exact nonempty)
          (lockedFrom_step anc reach edge locked) x member
  | @doneOk _ _ _ _ _ _ _ post _ hstep henter hresume next ih =>
      intro F pc0 reach ok okDesc hfork nonempty anc x member
      have head := nodeSafe_head dom pc0 reach ok hfork anc
      have edge := ParentStep.doneOk hstep henter hresume next
      have locked : lockAt P L.slot post = L.locked := by
        unfold lockAt
        rw [Evm.step_doneOk_getStor_eq hstep henter hresume P (State.Protected.of_code_ne_nil nonempty)]
        exact head.1
      simp only [Exec.rawNodes, List.mem_cons] at member
      rcases member with rfl | member
      · exact head
      · exact ih F pc0 (reach.snoc edge) ok
          (by simpa only [Exec.rawFrameDescendants] using okDesc) hfork
          (by rw [Blanc.Exec.Deriv.ParentStep.codePreserve edge P nonempty]; exact nonempty)
          (lockedFrom_step anc reach edge locked) x member
  | @runErr _ _ _ _ _ _ childEvm _ _ hstep henter child hresume childIh =>
      intro F pc0 reach ok okDesc hfork nonempty anc x member
      have head := nodeSafe_head dom pc0 reach ok hfork anc
      simp only [Exec.rawFrameDescendants, List.mem_cons] at okDesc
      have childNonempty : (childEvm.dyna.getCode P).toList ≠ [] := by
        rw [(Evm.step_spawn_child hstep henter).2.1 P]
        exact nonempty
      have childLocked : lockAt P L.slot childEvm.dyna = L.locked := by
        unfold lockAt
        rw [Evm.step_spawn_enter_getStor hfork hstep henter P (State.Protected.of_code_ne_nil nonempty)]
        exact head.1
      simp only [Exec.rawNodes, List.mem_cons] at member
      rcases member with rfl | member
      · exact head
      · exact childIh _ (Frame.enter_run_pc henter) (.refl _)
          (okDesc _ (Or.inl rfl)) (fun G member => okDesc G (Or.inr member))
          (Evm.step_spawn_child_fork hstep henter hfork) childNonempty
          (lockedFrom_self childLocked) x member
  | @runOk _ _ _ _ _ _ childEvm _ post _ hstep henter child hresume next childIh nextIh =>
      intro F pc0 reach ok okDesc hfork nonempty anc x member
      have head := nodeSafe_head dom pc0 reach ok hfork anc
      simp only [Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at okDesc
      have childNonempty : (childEvm.dyna.getCode P).toList ≠ [] := by
        rw [(Evm.step_spawn_child hstep henter).2.1 P]
        exact nonempty
      have childLocked : lockAt P L.slot childEvm.dyna = L.locked := by
        unfold lockAt
        rw [Evm.step_spawn_enter_getStor hfork hstep henter P (State.Protected.of_code_ne_nil nonempty)]
        exact head.1
      have childSafe : ∀ x ∈ Exec.rawNodes child, NodeSafe L P x :=
        childIh _ (Frame.enter_run_pc henter) (.refl _)
          (okDesc _ (Or.inl rfl)) (fun G member => okDesc G (Or.inr (Or.inl member)))
          (Evm.step_spawn_child_fork hstep henter hfork) childNonempty
          (lockedFrom_self childLocked)
      have edge := ParentStep.runOk hstep henter child hresume next
      have locked : lockAt P L.slot post = L.locked := by
        rw [resume_lockAt hfork hstep henter child hresume nonempty childSafe]
        exact head.1
      simp only [Exec.rawNodes, List.mem_cons, List.mem_append] at member
      rcases member with rfl | member | member
      · exact head
      · exact childSafe x member
      · exact nextIh F pc0 (reach.snoc edge) ok
          (fun G member => okDesc G (Or.inr (Or.inr member))) hfork
          (by rw [Blanc.Exec.Deriv.ParentStep.codePreserve edge P nonempty]; exact nonempty)
          (lockedFrom_step anc reach edge locked) x member

/-- Along a same-frame segment from `b` in which no node before `h` executes a
slot-addressed `SSTORE`, the lock word held at `b` is still held at `h`:
children spawned in between cannot change it (by the core induction) and
completed spawns never touch storage. -/
theorem lockAt_of_segment (dom : L.Dominance) {F b h : Exec.Deriv}
    (reachB : ParentPrefix F b) (segment : ParentPrefix b h)
    (okDesc : ∀ G ∈ Exec.rawFrameDescendants F.exc, FrameOK L P G)
    (hfork : CoveredFork F.sevm.benvStat.fork)
    (nonempty : (b.devm.getCode P).toList ≠ [])
    (noStore : ∀ x, ParentPrefix b x → ParentPrefix x h → x ≠ h →
      ¬ SstoreAt x L.slot)
    (locked : lockAt P L.slot b.devm = L.locked) :
    lockAt P L.slot h.devm = L.locked := by
  induction segment with
  | refl => exact locked
  | @step root next tail edge rest ih =>
      have distinct : root ≠ tail := by
        rintro rfl
        exact Blanc.Exec.Deriv.ParentStep.not_parentPrefix_back edge rest (.refl _)
      have rootFork : CoveredFork root.sevm.benvStat.fork := by
        rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq reachB]
        exact hfork
      apply ih (reachB.snoc edge)
        (by rw [Blanc.Exec.Deriv.ParentStep.codePreserve edge P nonempty]; exact nonempty)
        (fun x hnx hxt ne => noStore x (.step edge hnx) hxt ne)
      cases edge with
      | cont hstep nextRun =>
          unfold lockAt
          rw [Evm.step_cont_getStor_get rootFork hstep (fun _ decoded key =>
            noStore _ (.refl _) (.step (.cont hstep nextRun) rest) distinct
              ⟨decoded, key⟩)]
          exact locked
      | doneOk hstep henter hresume nextRun =>
          unfold lockAt
          rw [Evm.step_doneOk_getStor_eq hstep henter hresume P (State.Protected.of_code_ne_nil nonempty)]
          exact locked
      | @runOk _ _ _ _ _ _ _ childEvm _ _ hstep henter child hresume nextRun =>
          have childMember : ∀ G ∈ Exec.rawFrameRoots child,
              G ∈ Exec.rawFrameDescendants F.exc := by
            intro G member
            apply Exec.mem_rawFrameDescendants_of_parentPrefix reachB
            simp only [Exec.rawFrameRoots, List.mem_cons] at member
            simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
            rcases member with rfl | member
            · exact Or.inl rfl
            · exact Or.inr (Or.inl member)
          have childNonempty : (childEvm.dyna.getCode P).toList ≠ [] := by
            rw [(Evm.step_spawn_child hstep henter).2.1 P]
            exact nonempty
          have childLocked : lockAt P L.slot childEvm.dyna = L.locked := by
            unfold lockAt
            rw [Evm.step_spawn_enter_getStor rootFork hstep henter P (State.Protected.of_code_ne_nil nonempty)]
            exact locked
          have childSafe := nodeSafe_of_lockedFrom dom child _
            (Frame.enter_run_pc henter) (.refl _)
            (okDesc _ (childMember _ (by simp only [Exec.rawFrameRoots, List.mem_cons, true_or])))
            (fun G member => okDesc G (childMember G (by
              simp only [Exec.rawFrameRoots, List.mem_cons]
              exact Or.inr member)))
            (Evm.step_spawn_child_fork hstep henter rootFork) childNonempty
            (lockedFrom_self childLocked)
          rw [resume_lockAt rootFork hstep henter child hresume nonempty childSafe]
          exact locked

/-- Frame-local facts for every raw frame root of a disciplined execution. -/
theorem frameOK_of_mem
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (owner : L.OwnerDiscipline P run) (hash : L.HashAvoidIn P run)
    {G : Exec.Deriv} (member : G ∈ Exec.rawFrameRoots run) :
    FrameOK L P G :=
  ⟨owner G member, hash G member⟩

/-- Every frame below a raw frame root of `run` is again a raw frame root. -/
theorem mem_rawFrameRoots_of_descendant
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out} {F G : Exec.Deriv}
    (hF : F ∈ Exec.rawFrameRoots run)
    (hG : G ∈ Exec.rawFrameDescendants F.exc) :
    G ∈ Exec.rawFrameRoots run :=
  Exec.rawFrameRoots_trans hF (by
    simp only [Exec.rawFrameRoots, List.mem_cons]
    exact Or.inr hG)

/-- Every raw frame root of an execution started at pc 0 on a covered fork
starts at pc 0 on a covered fork. -/
theorem rawFrameRoots_entry
    {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) (hfork : CoveredFork sevm.benvStat.fork)
    {F : Exec.Deriv} (hF : F ∈ Exec.rawFrameRoots run) :
    F.pc = 0 ∧ CoveredFork F.sevm.benvStat.fork := by
  simp only [Exec.rawFrameRoots, List.mem_cons] at hF
  rcases hF with rfl | hF
  · exact ⟨rfl, hfork⟩
  · exact Exec.rawFrameDescendants_entry run hfork F hF

/-! ## Public theorems -/

/-- **V+ (generic lock exclusion).**  In any execution `R` — of any outcome,
with nonempty entry world code at `P`, under current-fork semantics (`CoveredFork`) — satisfying the per-code dominance obligation, owner discipline and trace-local
hash avoidance, if a frame `F` of `P` running `L.code` is active at a node `h`
that spawns a child frame `c` (whether `h` then resumes or not), then no frame
at or below `c` is a frame of `P` running `L.code` that reaches a guarded body
start.  No frame involved is required to succeed. -/
theorem LockSpec.lock_exclusion
    {sevm : Sevm} {pre : Devm} {out : Execution}
    (R : Exec 0 sevm pre out) (hfork : CoveredFork sevm.benvStat.fork)
    (nonempty : (pre.getCode P).toList ≠ [])
    (dom : L.Dominance) (owner : L.OwnerDiscipline P R)
    (hash : L.HashAvoidIn P R)
    {F h c : Exec.Deriv} (hF : F ∈ Exec.rawFrameRoots R)
    (active : L.Active P F h) (spawn : Spawns h c)
    {G : Exec.Deriv} (hG : G ∈ Exec.rawFrameRoots c.exc) :
    ¬ L.Enters P G := by
  rintro ⟨⟨_, gOwner, gCode⟩, x, hGx, body⟩
  rcases active with ⟨⟨pc0, fOwner, fCode⟩, reachH, b, reachB, segment, mutBody,
    noStore⟩
  have fFork := (rawFrameRoots_entry R hfork hF).2
  have okDesc : ∀ G ∈ Exec.rawFrameDescendants F.exc, FrameOK L P G :=
    fun G member => frameOK_of_mem owner hash
      (mem_rawFrameRoots_of_descendant hF member)
  have fNonempty : (F.devm.getCode P).toList ≠ [] := by
    rw [Exec.rawFrameRoots_codePreserve R P nonempty F hF]
    exact nonempty
  have bNonempty : (b.devm.getCode P).toList ≠ [] := by
    rw [Blanc.Exec.Deriv.ParentPrefix.codePreserve reachB P fNonempty]
    exact fNonempty
  have hNonempty : (h.devm.getCode P).toList ≠ [] := by
    rw [Blanc.Exec.Deriv.ParentPrefix.codePreserve reachH P fNonempty]
    exact fNonempty
  have bLocked : lockAt P L.slot b.devm = L.locked := by
    have := (dom F pc0 fFork fCode (hash F hF ⟨pc0, fOwner, fCode⟩) b reachB).2 mutBody
    rwa [fOwner] at this
  have hLocked :=
    lockAt_of_segment dom reachB segment okDesc fFork bNonempty noStore bLocked
  have hFork : CoveredFork h.sevm.benvStat.fork := by
    rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq reachH]
    exact fFork
  have childSafe : ∀ y ∈ Exec.rawNodes c.exc, NodeSafe L P y := by
    have childMember : ∀ D ∈ Exec.rawFrameRoots c.exc,
        D ∈ Exec.rawFrameDescendants F.exc := by
      intro D member
      apply Exec.mem_rawFrameDescendants_of_parentPrefix reachH
      cases spawn with
      | runErr hstep henter child hresume =>
          simp only [Exec.rawFrameRoots, List.mem_cons] at member
          simp only [Exec.rawFrameDescendants, List.mem_cons]
          exact member
      | runOk hstep henter child hresume next =>
          simp only [Exec.rawFrameRoots, List.mem_cons] at member
          simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
          rcases member with rfl | member
          · exact Or.inl rfl
          · exact Or.inr (Or.inl member)
    cases spawn with
    | @runErr _ _ _ _ _ _ childEvm _ _ hstep henter child hresume =>
        have childNonempty : (childEvm.dyna.getCode P).toList ≠ [] := by
          rw [(Evm.step_spawn_child hstep henter).2.1 P]
          exact hNonempty
        have childLocked : lockAt P L.slot childEvm.dyna = L.locked := by
          unfold lockAt
          rw [Evm.step_spawn_enter_getStor hFork hstep henter P (State.Protected.of_code_ne_nil hNonempty)]
          exact hLocked
        exact nodeSafe_of_lockedFrom dom child _
          (Frame.enter_run_pc henter) (.refl _)
          (okDesc _ (childMember _ (by simp only [Exec.rawFrameRoots, List.mem_cons, true_or])))
          (fun D member => okDesc D (childMember D (by
            simp only [Exec.rawFrameRoots, List.mem_cons]
            exact Or.inr member)))
          (Evm.step_spawn_child_fork hstep henter hFork) childNonempty
          (lockedFrom_self childLocked)
    | @runOk _ _ _ _ _ _ _ childEvm _ _ hstep henter child hresume next =>
        have childNonempty : (childEvm.dyna.getCode P).toList ≠ [] := by
          rw [(Evm.step_spawn_child hstep henter).2.1 P]
          exact hNonempty
        have childLocked : lockAt P L.slot childEvm.dyna = L.locked := by
          unfold lockAt
          rw [Evm.step_spawn_enter_getStor hFork hstep henter P (State.Protected.of_code_ne_nil hNonempty)]
          exact hLocked
        exact nodeSafe_of_lockedFrom dom child _
          (Frame.enter_run_pc henter) (.refl _)
          (okDesc _ (childMember _ (by simp only [Exec.rawFrameRoots, List.mem_cons, true_or])))
          (fun D member => okDesc D (childMember D (by
            simp only [Exec.rawFrameRoots, List.mem_cons]
            exact Or.inr member)))
          (Evm.step_spawn_child_fork hstep henter hFork) childNonempty
          (lockedFrom_self childLocked)
  have reached : x ∈ Exec.rawNodes c.exc :=
    (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix c.exc x).mpr ⟨G, hG, hGx⟩
  have xSevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hGx
  exact (childSafe x reached).2.2 ⟨xSevm ▸ gOwner, xSevm ▸ gCode, body⟩

/-- **Locked core.**  With nonempty entry world code at `P`, if every same-frame node of a raw frame `F` of `R` up to
`E` held the lock word, then from `E` on — in `E`'s own frame and in every
frame entered below it, whatever their outcomes — the lock cell holds the lock
word at every raw node, no `P`-owned `SSTORE` addresses the slot, no write to
the cell is retained, and no frame of `P` running `L.code` reaches a guarded
body start. -/
theorem LockSpec.locked_core
    {sevm : Sevm} {pre : Devm} {out : Execution}
    (R : Exec 0 sevm pre out) (hfork : CoveredFork sevm.benvStat.fork)
    (nonempty : (pre.getCode P).toList ≠ [])
    (dom : L.Dominance) (owner : L.OwnerDiscipline P R)
    (hash : L.HashAvoidIn P R)
    {F E : Exec.Deriv} (hF : F ∈ Exec.rawFrameRoots R)
    (reach : ParentPrefix F E) (anc : LockedFrom L P F E) :
    (∀ x ∈ Exec.rawNodes E.exc,
      lockAt P L.slot x.devm = L.locked ∧
        ¬ (x.sevm.currentTarget = P ∧ SstoreAt x L.slot)) ∧
    (∀ G ∈ Exec.rawFrameDescendants E.exc, ¬ L.Enters P G) ∧
    Exec.NoRetainedWriteTo E.exc P L.slot := by
  rcases rawFrameRoots_entry R hfork hF with ⟨pc0, fFork⟩
  have okDesc : ∀ G ∈ Exec.rawFrameDescendants E.exc, FrameOK L P G :=
    fun G member => frameOK_of_mem owner hash
      (mem_rawFrameRoots_of_descendant hF
        (Exec.mem_rawFrameDescendants_of_parentPrefix reach member))
  have eFork : CoveredFork E.sevm.benvStat.fork := by
    rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq reach]
    exact fFork
  have fNonempty : (F.devm.getCode P).toList ≠ [] := by
    rw [Exec.rawFrameRoots_codePreserve R P nonempty F hF]
    exact nonempty
  have eNonempty : (E.devm.getCode P).toList ≠ [] := by
    rw [Blanc.Exec.Deriv.ParentPrefix.codePreserve reach P fNonempty]
    exact fNonempty
  rcases E with ⟨pc, sevm', devm, exn, run⟩
  have safe := nodeSafe_of_lockedFrom dom run F pc0 reach
    (frameOK_of_mem owner hash hF) okDesc eFork eNonempty anc
  refine ⟨fun x member => ⟨(safe x member).1, (safe x member).2.1⟩, ?_,
    noRetainedWriteTo_of_nodeSafe run safe⟩
  rintro G member ⟨⟨_, gOwner, gCode⟩, x, hGx, body⟩
  have reached : x ∈ Exec.rawNodes run :=
    (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run x).mpr
      ⟨G, by simp only [Exec.rawFrameRoots, List.mem_cons]; exact Or.inr member,
        hGx⟩
  have xSevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hGx
  exact (safe x reached).2.2 ⟨xSevm ▸ gOwner, xSevm ▸ gCode, body⟩

/-! ## Vacuity guard -/

/-- The dominance obligation is satisfiable: it holds for every lock whose
code has no `SSTORE` and that declares no body starts.  (It then constrains
nothing, which is the point of a guard: the hypothesis is not contradictory.) -/
theorem dominance_of_noSstore_of_nil
    (noStore : NoSstore L.code) (bodies : L.bodies = [])
    (mutBodies : L.mutBodies = []) : L.Dominance := by
  intro F _ _ code _ n reach
  refine ⟨?_, ?_⟩
  · rintro (body | store)
    · rw [bodies] at body
      cases body
    · have sevmEq := Blanc.Exec.Deriv.ParentPrefix.sevm_eq reach
      exact (noStore n.pc (by rw [← code, ← sevmEq]; exact store.1)).elim
  · intro body
    rw [mutBodies] at body
    cases body

/-- The one-byte code `STOP`. -/
def stopCode : ByteArray := ByteArray.mk #[0x00]

/-- A frame entered at pc 0 on `stopCode` has no same-frame continuation. -/
theorem stopCode_no_parentStep {F y : Exec.Deriv}
    (pc0 : F.pc = 0) (code : F.sevm.code = stopCode) : ¬ ParentStep y F := by
  rcases F with ⟨pc, sevm, devm, out, run⟩
  simp only at pc0 code
  subst pc0
  have halts : Evm.step ⟨0, sevm, devm⟩ = .halt (Linst.stop.run sevm devm) :=
    Evm.step_last (by rw [code]; rfl)
  intro edge
  cases edge with
  | cont hstep _ => rw [halts] at hstep; cases hstep
  | doneOk hstep _ _ _ => rw [halts] at hstep; cases hstep
  | runOk hstep _ _ _ _ => rw [halts] at hstep; cases hstep

/-- A non-degenerate satisfiability witness for `Dominance`: a lock whose
code is `STOP` and whose guarded and mutating body start is pc 1.  Every
frame running it halts at pc 0, so no body start is reached and no `SSTORE`
executes; the obligation is met with nonempty `bodies` and `mutBodies`. -/
theorem stopLock_dominance (slot locked : B256) :
    (⟨stopCode, slot, locked, [1], [1]⟩ : LockSpec).Dominance := by
  intro F pc0 _ code _ n reach
  have atRoot : n = F := by
    cases reach with
    | refl => rfl
    | step head _ => exact (stopCode_no_parentStep pc0 code head).elim
  subst atRoot
  refine ⟨?_, ?_⟩
  · rintro (body | store)
    · simp only [pc0, List.mem_cons, zero_ne_one, List.not_mem_nil, or_self] at body
    · have decoded := store.1
      rw [code, pc0] at decoded
      have stop : stopCode.getInst 0 = some (.last .stop) := rfl
      unfold Ninst.At at decoded
      rw [stop] at decoded
      cases decoded
  · intro body
    simp only [pc0, List.mem_cons, zero_ne_one, List.not_mem_nil, or_self] at body

/-- Hash avoidance holds for any frame whose code has no `KECCAK256`. -/
theorem hashAvoid_of_no_keccak {slot : B256} {F : Exec.Deriv}
    (noHash : ∀ pc, ¬ Ninst.At F.sevm.code pc (.reg .keccak256)) :
    HashAvoid slot F := by
  intro x _ reach _ hash
  rw [Blanc.Exec.Deriv.ParentPrefix.sevm_eq reach] at hash
  exact (noHash x.pc hash).elim

end LockExclusion

end Blanc
