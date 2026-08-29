-- ProrataAccountingExec.lean : recursive execution accounting replay.

import Blanc.ProrataRealizedAccounting
import Blanc.ExecutionMessageEffects

namespace Blanc

open Jaune

namespace Prorata

namespace AccountingSnapshot

/-- The accounting boundary at an instruction-frame entry.  A frame executing
PRORATA begins immediately before its value credit; a foreign frame begins at
the ordinary world-state projection. -/
def execEntry (ca : Adr) (sevm : Sevm) (state : State) :
    AccountingSnapshot :=
  if sevm.currentTarget = ca then beforeCredit ca sevm.value state
  else ofState ca state

@[simp] theorem execEntry_of_target
    {ca : Adr} {sevm : Sevm} {state : State}
    (target : sevm.currentTarget = ca) :
    execEntry ca sevm state = beforeCredit ca sevm.value state := by
  simp [execEntry, target]

@[simp] theorem execEntry_of_target_ne
    {ca : Adr} {sevm : Sevm} {state : State}
    (target : sevm.currentTarget ≠ ca) :
    execEntry ca sevm state = ofState ca state := by
  simp [execEntry, target]

end AccountingSnapshot

/-- The exact message-level facts needed to interpret a retained raw execution
as PRORATA accounting.  `codeOrForeign` excludes synthetic CREATE roots that
run arbitrary code at the installed address; `caller_ne` excludes a direct
self-withdrawal root, and is stated as the implication its one consumer uses
so that a wrapper may discharge it from the caller's own identity rather than
only from value transfer or foreignness. -/
structure AccountingMessageReady (ca : Adr) (msg : Msg) : Prop where
  runReady : prorataSpec.MessageRunReady ca msg
  caller_ne : msg.currentTarget = ca → msg.caller ≠ ca

/-- Settlement-aware accounting replay for one retained CALL message.  A
committing child contributes its recursively proved body; a noncommitting
child rolls back to the message's pre-transfer world and contributes nothing. -/
theorem ProcessMessage.accountingReplay_of_body
    {ca : Adr} {msg : Msg} {post : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (process : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256)
    (body : ∀ committed : Execution.commits out = true, ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.execEntry ca sevm pre.state) steps
        (AccountingSnapshot.ofState ca
          (Execution.committedPost out committed).state)) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca msg.benv.state) steps
        (AccountingSnapshot.ofState ca post.state) := by
  by_cases settles :
      Frame.settlementCommits (Frame.ofCall msg) out = true
  · have committed := Frame.raw_commits_of_settlementCommits settles
    have enter : (Frame.ofCall msg).enter = .run ⟨pc, sevm, pre⟩ :=
      (RunFrame.some_inv process).1
    rcases Frame.enter_run_inv enter with ⟨entry, transfer, evmEq⟩
    simp only [Frame.ofCall] at transfer evmEq
    have sevmEq : sevm = initSevm (msg.withBenv entry) :=
      congrArg (fun evm : Evm => evm.sta) evmEq
    have preState : pre.state = entry.state :=
      congrArg (fun evm : Evm => evm.dyna.state) evmEq
    have entryBoundary :
        AccountingSnapshot.execEntry ca sevm pre.state =
          AccountingSnapshot.messageEntry ca msg entry.state := by
      rw [sevmEq, preState]
      rfl
    have prefixEq :
        AccountingSnapshot.execEntry ca sevm pre.state =
          AccountingSnapshot.ofState ca msg.benv.state :=
      entryBoundary.trans
        (AccountingSnapshot.messageEntry_eq_ofState caller_ne value_zero
          transfer sum_nof)
    have postState : post.state =
        (Execution.committedPost out committed).state :=
      _root_.Blanc.ProcessMessage.ok_state_eq_committedPost process committed
    rcases body committed with ⟨steps, replay⟩
    refine ⟨steps, ?_⟩
    rw [← prefixEq, postState]
    exact replay
  · have settledEq := (RunFrame.some_inv process).2
    have postError : post.error.isSome = true := by
      have notNone : post.error.isNone ≠ true := by
        intro clean
        apply settles
        unfold Frame.settlementCommits
        rw [← settledEq]
        exact clean
      cases errorEq : post.error <;> simp_all
    have rollback :=
      (_root_.Blanc.ProcessMessage.rollback_of_error process postError).1
    refine ⟨[], ProrataAccountingReplay.nil_of_eq ?_⟩
    exact congrArg (AccountingSnapshot.ofState ca) rollback

/-- Settlement-aware accounting replay for one retained CREATE constructor.
Fresh-account preparation is silent in the PRORATA projection; clean code
deposit preserves the constructor endpoint, while every failed settlement
rolls back to the outer CREATE-message world. -/
theorem ProcessCreateMessage.accountingReplay_of_body
    {ca : Adr} {msg : Msg} {post : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (process : ProcessCreateMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (fresh : msg.benv.state.getStor msg.currentTarget = .empty)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256)
    (body : ∀ committed : Execution.commits out = true, ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.execEntry ca sevm pre.state) steps
        (AccountingSnapshot.ofState ca
          (Execution.committedPost out committed).state)) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca msg.benv.state) steps
        (AccountingSnapshot.ofState ca post.state) := by
  by_cases settles :
      Frame.settlementCommits (Frame.ofCreate msg) out = true
  · have clean : post.error.isSome = false := by
      have settledEq := (RunFrame.some_inv process).2
      unfold Frame.settlementCommits at settles
      rw [← settledEq] at settles
      cases errorEq : post.error <;> simp_all
    rcases _root_.Blanc.ProcessCreateMessage.ok_getStor_eq_inner_of_clean
        process clean with ⟨inner, innerProcess, postStor, innerClean⟩
    rcases _root_.Blanc.ProcessCreateMessage.ok_state_eq_inner_of_no_error
        process clean with ⟨balanceInner, balanceProcess, postBalance⟩
    have innerEq : inner = balanceInner := by
      have left := (RunFrame.some_inv innerProcess).2
      have right := (RunFrame.some_inv balanceProcess).2
      exact Except.ok.inj (left.trans right.symm)
    subst balanceInner
    have preparedStor :=
      _root_.Blanc.processCreateMessage_msg_getStor_eq_of_empty fresh
    have preparedBalance :=
      _root_.Blanc.processCreateMessage_msg_bal_eq msg
    have preparedSnapshot :
        AccountingSnapshot.ofState ca
            (processCreateMessage.msg msg).benv.state =
          AccountingSnapshot.ofState ca msg.benv.state := by
      unfold AccountingSnapshot.ofState
      exact congrArg₂ AccountingSnapshot.mk
        (congrArg supplyN (congrFun preparedStor ca))
        (congrArg B256.toNat (congrFun preparedBalance ca))
    have postSnapshot :
        AccountingSnapshot.ofState ca post.state =
          AccountingSnapshot.ofState ca inner.state := by
      unfold AccountingSnapshot.ofState
      exact congrArg₂ AccountingSnapshot.mk
        (congrArg supplyN (congrFun postStor ca))
        (congrArg B256.toNat (congrFun postBalance ca))
    have innerSum :
        sum (processCreateMessage.msg msg).benv.state.bal < 2 ^ 256 := by
      rw [preparedBalance]
      exact sum_nof
    have innerReplay := ProcessMessage.accountingReplay_of_body
      (ca := ca) innerProcess caller_ne value_zero innerSum body
    rcases innerReplay with ⟨steps, replay⟩
    refine ⟨steps, ?_⟩
    rw [← preparedSnapshot, postSnapshot]
    exact replay
  · have settledEq := (RunFrame.some_inv process).2
    have postError : post.error.isSome = true := by
      have notClean : post.error.isSome ≠ false := by
        intro clean
        apply settles
        unfold Frame.settlementCommits
        rw [← settledEq]
        cases errorEq : post.error <;> simp_all
      cases errorEq : post.error <;> simp_all
    have rollback :=
      _root_.Blanc.ProcessCreateMessage.rollback_of_error process postError
    refine ⟨[], ProrataAccountingReplay.nil_of_eq ?_⟩
    exact congrArg (AccountingSnapshot.ofState ca) rollback

/-- Recursive accounting transport for one actual filled executable slot in a
foreign frame.  CALL and CREATE share the same settlement-aware child replay;
their distinct instruction prefixes and resumptions are projection-silent. -/
theorem Xinst.foreignSomeAccountingReplay
    {ca : Adr} {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    {cevm : Evm} {raw : Execution} {settled : Devm}
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (frameRun : RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled))
    (resumeRun : resume.run (.ok settled) = .ok post)
    (target_ne : sevm.currentTarget ≠ ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256)
    (body : ∀ committed : Execution.commits raw = true, ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.execEntry ca cevm.sta cevm.dyna.state) steps
        (AccountingSnapshot.ofState ca
          (Execution.committedPost raw committed).state)) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca pre.state) steps
        (AccountingSnapshot.ofState ca post.state) := by
  rcases Xinst.step_shape sevm pre x with
    ⟨execution, shape, hprefix⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, shape⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, callShape, _,
      shape⟩ <;> rw [shape] at spawn
  · cases spawn
  · rcases genericCreate_step_spawn_exact spawn with ⟨rfl, rfl⟩
    let createPre :=
      addAccessedAddress
        (((d.withGasLeft
            (d.gasLeft - except64th d.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress
    let msg := createMsg sevm createPre (except64th d.gasLeft)
      endowment newAddress ((d.memory.read mi ms).1)
    have process : ProcessCreateMessage msg (.some ⟨cevm, raw⟩)
        (.ok settled) := by
      simpa only [ProcessCreateMessage, msg, createPre] using frameRun
    have dSum : sum d.state.bal < 2 ^ 256 := by
      rw [← hprefix.state]
      exact sum_nof
    have preparedStor : createPre.state.getStor = d.state.getStor := by
      simpa only [createPre] using
        genericCreate_prepared_getStor sevm d newAddress
    have preparedBalance : createPre.state.bal = d.state.bal := by
      simpa only [createPre] using genericCreate_prepared_bal sevm d newAddress
    have preparedSnapshot :
        AccountingSnapshot.ofState ca createPre.state =
          AccountingSnapshot.ofState ca d.state := by
      unfold AccountingSnapshot.ofState
      exact congrArg₂ AccountingSnapshot.mk
        (congrArg supplyN (congrFun preparedStor ca))
        (congrArg B256.toNat (congrFun preparedBalance ca))
    have targetEmpty : Devm.getStor d newAddress = .empty :=
      genericCreate_step_spawn_getStor_empty spawn
    have fresh : msg.benv.state.getStor msg.currentTarget = .empty := by
      change createPre.state.getStor newAddress = .empty
      rw [preparedStor]
      exact targetEmpty
    have callerNe : msg.shouldTransferValue = true → msg.caller ≠ ca := by
      simpa [msg, createMsg] using target_ne
    have valueZero : msg.shouldTransferValue = false →
        msg.currentTarget = ca → msg.value = 0 := by
      simp [msg, createMsg]
    have msgSum : sum msg.benv.state.bal < 2 ^ 256 := by
      change sum createPre.state.bal < 2 ^ 256
      rw [preparedBalance]
      exact dSum
    rcases ProcessCreateMessage.accountingReplay_of_body process callerNe
        valueZero fresh msgSum body with ⟨steps, replay⟩
    have postState : post.state = settled.state :=
      Resume.create_state resumeRun
    refine ⟨steps, ?_⟩
    rw [hprefix.state, ← preparedSnapshot, postState]
    exact replay
  · rcases genericCall_step_spawn_exact spawn with ⟨rfl, rfl⟩
    let msg := callMsg sevm (d.withReturnData []) gas value caller target
      codeAddress stv isStatic ((d.memory.read ii isz).1) code
      disablePrecompiles
    have process : ProcessMessage msg (.some ⟨cevm, raw⟩) (.ok settled) := by
      simpa only [ProcessMessage, msg] using frameRun
    have dSum : sum d.state.bal < 2 ^ 256 := by
      rw [← hprefix.state]
      exact sum_nof
    have callerNe : stv = true → caller ≠ ca := by
      intro transfer
      rcases callShape with ⟨_, caller_eq⟩ | ⟨noTransfer, _⟩
      · rw [caller_eq]
        exact target_ne
      · rw [transfer] at noTransfer
        contradiction
    have valueZero : stv = false → target = ca → value = 0 := by
      intro noTransfer target_eq
      rcases callShape with ⟨transfer, _⟩ | ⟨_, targetParent⟩
      · rw [noTransfer] at transfer
        contradiction
      · exact False.elim (target_ne (targetParent.symm.trans target_eq))
    have msgCallerNe :
        msg.shouldTransferValue = true → msg.caller ≠ ca := by
      simpa [msg, callMsg] using callerNe
    have msgValueZero : msg.shouldTransferValue = false →
        msg.currentTarget = ca → msg.value = 0 := by
      simpa [msg, callMsg] using valueZero
    have msgSum : sum msg.benv.state.bal < 2 ^ 256 := by
      change sum d.state.bal < 2 ^ 256
      exact dSum
    rcases ProcessMessage.accountingReplay_of_body process msgCallerNe
        msgValueZero msgSum body with ⟨steps, replay⟩
    have postState : post.state = settled.state :=
      Resume.call_state resumeRun
    refine ⟨steps, ?_⟩
    rw [hprefix.state, postState]
    exact replay

/-- Proof-indexed committed accounting replay for one interpreter suffix.
`nextChild` is the ordinal of the next frame spawned by the current execution;
it is threaded independently of the emitted accounting list so provenance
remains stable across childless and rolled-back frames. -/
def Exec.CoreProrataAccounting
    (ca : Adr) (pc : Nat) (sevm : Sevm) (pre : Devm)
    (out : Execution) : Prop :=
  ∀ (_run : Exec pc sevm pre out)
    (committed : Execution.commits out = true),
    Prog.At prorata ca pc sevm pre →
    prorataSpec.Pre ca sevm pre →
    (sevm.currentTarget = ca → sevm.codeAddress = some ca) →
    (sevm.currentTarget = ca → sevm.caller.toB256.toAdr ≠ ca) →
    ∀ (_blockIndex : Nat) (_transactionIndex : Option Nat)
      (_framePath : List Nat) (_nextChild : Nat),
      ∃ steps,
        ProrataAccountingReplay offset.toNat
          (AccountingSnapshot.execEntry ca sevm pre.state) steps
          (AccountingSnapshot.ofState ca
            (Execution.committedPost out committed).state)

/-- A failed raw execution cannot satisfy the committed replay premise. -/
theorem Exec.CoreProrataAccounting.error
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {error : EvmError × Devm} :
    Exec.CoreProrataAccounting ca pc sevm pre (.error error) := by
  intro _ committed
  simp [Execution.commits] at committed

/-- The compiled PRORATA frame handler.  Ordinary deployed routes close in
one classified replay; withdrawal prefixes recurse only into the exact
settlement-retained payout child before returning to the outer endpoint. -/
theorem Exec.CoreProrataAccounting.atTarget
    {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (_programRun : Prog.Run sevm pre prorata post)
    (target : sevm.currentTarget = ca)
    (deeper : ForallDeeperAt sevm.depth ca prorata
      (fun pc childSevm childPre childOut _ =>
        Exec.CoreProrataAccounting ca pc childSevm childPre childOut)) :
    Exec.CoreProrataAccounting ca 0 sevm pre (.ok post) := by
  subst ca
  intro run committed installed precondition direct caller
    blockIndex transactionIndex framePath nextChild
  let frame := Exec.Frame.ofRun run committed
  have invocation : frame.exactInvocation prorata
      sevm.currentTarget sevm.currentTarget := by
    refine ⟨rfl, rfl, direct rfl, ?_⟩
    exact (installed.2 rfl).1
  let provenance : ProrataAccountingProvenance :=
    { blockIndex := blockIndex
      transactionIndex := transactionIndex
      framePath := framePath
      actor := some sevm.caller.toB256.toAdr }
  rcases
      _root_.Blanc.Prorata.Exec.Frame.accountingReplay_or_realizedWithdrawal
        invocation precondition provenance (caller rfl) with
    replay | withdrawal
  · rw [AccountingSnapshot.execEntry_of_target rfl]
    exact replay
  · rcases withdrawal with ⟨withdrawal⟩
    dsimp only [frame, Exec.Frame.ofRun, Exec.Frame.post] at withdrawal
    have childReplay : ∃ steps,
        ProrataAccountingReplay offset.toNat
          (AccountingSnapshot.ofState sevm.currentTarget
            withdrawal.payout.entry.state)
          steps
          (AccountingSnapshot.ofState sevm.currentTarget
            withdrawal.payout.child.state) := by
      rcases withdrawal.payout.trace with ⟨slot, retained, process⟩
      cases retained with
      | none =>
          have childState :=
            _root_.Blanc.ProcessMessage.none_ok_state_eq_entry_of_clean
              process withdrawal.payout.entryTransfer
                withdrawal.payout.childClean
          refine ⟨[], ProrataAccountingReplay.nil_of_eq ?_⟩
          exact congrArg
            (AccountingSnapshot.ofState sevm.currentTarget) childState
      | @some childPc childSevm childPre childOut childRun =>
          have settles :=
            _root_.Blanc.ProcessMessage.settlementCommits_of_some_ok_clean
              process withdrawal.payout.childClean
          have childCommitted :=
            Frame.raw_commits_of_settlementCommits settles
          have enter := (RunFrame.some_inv process).1
          rcases Frame.enter_run_inv enter with
            ⟨entry, transfer, childEvmEq⟩
          simp only [Frame.ofCall] at transfer childEvmEq
          have entryEq : entry = withdrawal.payout.entry :=
            Except.ok.inj
              (transfer.symm.trans withdrawal.payout.entryTransfer)
          subst entry
          have childSevmEq : childSevm =
              initSevm
                (withdrawal.payout.childMsg.withBenv
                  withdrawal.payout.entry) :=
            congrArg (fun evm : Evm => evm.sta) childEvmEq
          have childPreEq : childPre =
              initDevm
                (withdrawal.payout.childMsg.withBenv
                  withdrawal.payout.entry) :=
            congrArg (fun evm : Evm => evm.dyna) childEvmEq
          have childTargetNe :
              childSevm.currentTarget ≠ sevm.currentTarget := by
            rw [childSevmEq]
            simpa [initSevm, Msg.withBenv] using
              withdrawal.payout.targetNe
          have childAt : Prog.At prorata sevm.currentTarget childPc
              childSevm childPre := by
            refine ⟨?_, fun childTarget => (childTargetNe childTarget).elim⟩
            rw [childPreEq]
            exact withdrawal.childPre.code
          have childPrecondition :
              prorataSpec.Pre sevm.currentTarget childSevm childPre := by
            rw [childSevmEq, childPreEq]
            exact withdrawal.childPre
          have childDepth : childSevm.depth < sevm.depth := by
            rw [childSevmEq]
            exact withdrawal.payout.depth
          have childCore : Exec.CoreProrataAccounting sevm.currentTarget
              childPc childSevm childPre childOut :=
            deeper childPc childSevm childPre childOut childRun childDepth
              childAt
          rcases childCore childRun childCommitted childAt childPrecondition
              (fun childTarget => (childTargetNe childTarget).elim)
              (fun childTarget => (childTargetNe childTarget).elim)
              blockIndex transactionIndex (framePath ++ [nextChild]) 0 with
            ⟨steps, replay⟩
          have startEq :
              AccountingSnapshot.execEntry sevm.currentTarget childSevm
                  childPre.state =
                AccountingSnapshot.ofState sevm.currentTarget
                  withdrawal.payout.entry.state := by
            rw [AccountingSnapshot.execEntry_of_target_ne childTargetNe,
              childPreEq]
            rfl
          have childPost :=
            _root_.Blanc.ProcessMessage.ok_state_eq_committedPost
              process childCommitted
          refine ⟨steps, ?_⟩
          rw [← startEq, childPost]
          exact replay
    rcases withdrawal.accountingReplay provenance childReplay with
      ⟨steps, replay⟩
    refine ⟨steps, ?_⟩
    rw [AccountingSnapshot.execEntry_of_target rfl]
    exact replay

/-- Foreign nonrecursive execution prefixes their projected accounting change
to the continuation replay.  Childless message spawns still consume one child
ordinal even though they add no recursively interpreted frame. -/
theorem Exec.CoreProrataAccounting.nextNone
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {n : Ninst}
    {inter : Devm} {out : Execution}
    (_at : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out)
    (target_ne : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreProrataAccounting ca (pc + n.size) sevm inter out) :
    Exec.CoreProrataAccounting ca pc sevm pre out := by
  intro _ committed installed precondition _ _
    blockIndex transactionIndex framePath nextChild
  have interPre : prorataSpec.Pre ca sevm inter :=
    _root_.Blanc.ContractSpec.Ninst.none_preserves_precond
      (c := prorataSpec) step target_ne precondition
  have installedInter : Prog.At prorata ca (pc + n.size) sevm inter :=
    ⟨interPre.code, fun target => (target_ne target).elim⟩
  have sumNof : sum pre.state.bal < 2 ^ 256 := precondition.side
  let provenance : ProrataAccountingProvenance :=
    { blockIndex := blockIndex
      transactionIndex := transactionIndex
      framePath := framePath
      actor := none }
  rcases Ninst.foreignNoneAccountingReplay step target_ne sumNof provenance
      with ⟨headSteps, headReplay⟩
  cases stepShape : Ninst.step ⟨pc, sevm, pre⟩ n with
  | halt execution =>
      simp only [Ninst.StepRun, stepShape, Step.Run] at step
      rcases step with ⟨_, impossible⟩
      cases impossible
      exact False.elim (Ninst.step_ne_halt_ok stepShape)
  | cont pc' actual =>
      simp only [Ninst.StepRun, stepShape, Step.Run] at step
      rcases step with ⟨_, actualEq⟩
      cases actualEq
      have pcEq : pc' = pc + n.size := Ninst.step_cont_pc stepShape
      subst pc'
      rcases ih next committed installedInter interPre
          (fun target => (target_ne target).elim)
          (fun target => (target_ne target).elim)
          blockIndex transactionIndex framePath nextChild with
        ⟨tailSteps, tailReplay⟩
      rw [AccountingSnapshot.execEntry_of_target_ne target_ne] at tailReplay
      refine ⟨headSteps ++ tailSteps, ?_⟩
      rw [AccountingSnapshot.execEntry_of_target_ne target_ne]
      exact headReplay.append tailReplay
  | spawn frame resume pc' =>
      simp only [Ninst.StepRun, stepShape, Step.Run] at step
      rcases step with ⟨result, frameRun, resumeRun⟩
      have pcEq : pc' = pc + n.size := Ninst.step_spawn_pc stepShape
      subst pc'
      rcases ih next committed installedInter interPre
          (fun target => (target_ne target).elim)
          (fun target => (target_ne target).elim)
          blockIndex transactionIndex framePath (nextChild + 1) with
        ⟨tailSteps, tailReplay⟩
      rw [AccountingSnapshot.execEntry_of_target_ne target_ne] at tailReplay
      refine ⟨headSteps ++ tailSteps, ?_⟩
      rw [AccountingSnapshot.execEntry_of_target_ne target_ne]
      exact headReplay.append tailReplay

/-- A foreign terminal instruction is the final projected accounting segment
of its frame. -/
theorem Exec.CoreProrataAccounting.last
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {l : Linst}
    {out : Execution}
    (_at : Linst.At sevm.code pc l)
    (step : Linst.Run sevm pre l out)
    (target_ne : sevm.currentTarget ≠ ca) :
    Exec.CoreProrataAccounting ca pc sevm pre out := by
  intro _ committed _ precondition _ _
    blockIndex transactionIndex framePath _
  cases out with
  | error error =>
      simp [Execution.commits] at committed
  | ok post =>
      have sumNof : sum pre.state.bal < 2 ^ 256 := precondition.side
      let provenance : ProrataAccountingProvenance :=
        { blockIndex := blockIndex
          transactionIndex := transactionIndex
          framePath := framePath
          actor := none }
      rcases Linst.foreignAccountingReplay step target_ne sumNof provenance
          with ⟨steps, replay⟩
      refine ⟨steps, ?_⟩
      rw [AccountingSnapshot.execEntry_of_target_ne target_ne]
      exact replay

/-- Jump execution is world-state silent, so only its continuation contributes
accounting steps and the child ordinal is unchanged. -/
theorem Exec.CoreProrataAccounting.jump
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {j : Jinst}
    {pc' : Nat} {inter : Devm} {out : Execution}
    (_at : Jinst.At sevm.code pc j)
    (step : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out)
    (target_ne : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreProrataAccounting ca pc' sevm inter out) :
    Exec.CoreProrataAccounting ca pc sevm pre out := by
  intro _ committed _ precondition _ _
    blockIndex transactionIndex framePath nextChild
  have stateEq : inter.state = pre.state := Jinst.preserves_state step
  have interPre : prorataSpec.Pre ca sevm inter :=
    precondition.state_eq stateEq
  have installedInter : Prog.At prorata ca pc' sevm inter :=
    ⟨interPre.code, fun target => (target_ne target).elim⟩
  rcases ih next committed installedInter interPre
      (fun target => (target_ne target).elim)
      (fun target => (target_ne target).elim)
      blockIndex transactionIndex framePath nextChild with
    ⟨steps, replay⟩
  rw [AccountingSnapshot.execEntry_of_target_ne target_ne] at replay
  refine ⟨steps, ?_⟩
  rw [AccountingSnapshot.execEntry_of_target_ne target_ne, ← stateEq]
  exact replay

/-- A foreign filled child is replayed at its exact child path, transported
through complete CALL/CREATE settlement, and followed by the parent
continuation at the next sibling ordinal. -/
theorem Exec.CoreProrataAccounting.nextSome
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {n : Ninst}
    {cevm : Evm} {raw : Execution} {inter : Devm} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n
      (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out)
    (target_ne : sevm.currentTarget ≠ ca)
    (ihChild : Exec.CoreProrataAccounting ca
      cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : Exec.CoreProrataAccounting ca
      (pc + n.size) sevm inter out) :
    Exec.CoreProrataAccounting ca pc sevm pre out := by
  cases n with
  | reg r =>
      simp [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at step
  | push xs length =>
      simp [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at step
  | exec x =>
      intro _ committed installed precondition _ _
        blockIndex transactionIndex framePath nextChild
      have xrun : Xinst.Run sevm pre x (.some ⟨cevm, raw⟩)
          (.ok inter) := by
        simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep,
          Xinst.Run] using step
      have hxrun := XStep.run_toStep.mp step
      cases spawnEq : Xinst.step sevm pre x with
      | done execution =>
          simp [spawnEq, XStep.Run] at hxrun
      | spawn frame resume =>
          simp only [spawnEq, XStep.Run] at hxrun
          obtain ⟨result, frameRun, resumeRun⟩ := hxrun
          cases result with
          | error error =>
              cases resume <;>
                simp [Resume.run, liftToExecution] at resumeRun
          | ok settled =>
              have enter := (RunFrame.some_inv frameRun).1
              have evmStep : Evm.step ⟨pc, sevm, pre⟩ =
                  .spawn frame resume (pc + 1) := by
                rw [Evm.step_next hat]
                simp only [Ninst.step_exec, spawnEq, XStep.toStep]
              obtain ⟨childPcZero, childGetCode, childCodeSource⟩ :=
                Evm.step_spawn_child evmStep enter
              have childAt : Prog.At prorata ca cevm.pc cevm.sta cevm.dyna := by
                refine ⟨?_, fun childTarget => ⟨?_, childPcZero⟩⟩
                · rw [childGetCode ca]
                  exact installed.1
                · have parentTargetNe :
                      sevm.currentTarget ≠ cevm.sta.currentTarget := by
                    rw [childTarget]
                    exact target_ne
                  have codeEq := childCodeSource parentTargetNe
                    (by rw [childTarget]
                        exact not_empty_of_compile installed.1)
                    (by rw [childTarget]
                        exact not_delegation_of_compile installed.1)
                  rw [codeEq, childTarget]
                  exact installed.1
              rcases Frame.enter_run_inv enter with
                ⟨entry, transfer, childEvmEq⟩
              have childDirect : cevm.sta.currentTarget = ca →
                  cevm.sta.codeAddress = some ca := by
                intro childTarget
                have innerTarget : frame.inner.currentTarget = ca := by
                  rw [← Frame.enter_run_currentTarget enter]
                  exact childTarget
                have parentTargetNe :
                    sevm.currentTarget ≠ frame.inner.currentTarget := by
                  rw [innerTarget]
                  exact target_ne
                have targetCodeNonempty :
                    pre.getCode frame.inner.currentTarget ≠ .empty := by
                  rw [innerTarget]
                  exact not_empty_of_compile installed.1
                have codeAddress :=
                  _root_.Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget
                    spawnEq parentTargetNe targetCodeNonempty
                    (by rw [innerTarget]
                        dsimp only [getDelegatedCodeAddress]
                        rw [if_neg
                          (not_delegation_of_compile installed.1)])
                have childCodeAddress :=
                  congrArg (fun evm : Evm => evm.sta.codeAddress) childEvmEq
                dsimp [initEvm, initSevm, Msg.withBenv] at childCodeAddress
                rw [childCodeAddress, codeAddress, innerTarget]
              have childCaller : cevm.sta.currentTarget = ca →
                  cevm.sta.caller.toB256.toAdr ≠ ca := by
                intro childTarget
                have innerTarget : frame.inner.currentTarget = ca := by
                  rw [← Frame.enter_run_currentTarget enter]
                  exact childTarget
                have callerNe :=
                  _root_.Blanc.Xinst.step_spawn_caller_ne_of_target_eq
                    spawnEq target_ne innerTarget
                have childCallerEq :=
                  congrArg (fun evm : Evm => evm.sta.caller) childEvmEq
                dsimp [initEvm, initSevm, Msg.withBenv] at childCallerEq
                rw [childCallerEq, toAdr_toB256]
                exact callerNe
              obtain ⟨childPrecondition, continuationOfPost⟩ :=
                _root_.Blanc.ContractSpec.Xinst.some_preserves_precond
                  (c := prorataSpec) xrun child target_ne precondition
              have childPost :
                  ifOk (prorataSpec.Post ca cevm.sta) raw := by
                cases raw with
                | error error => trivial
                | ok rawPost =>
                    have childAtZero :
                        Exec 0 cevm.sta cevm.dyna (.ok rawPost) := by
                      rw [← childPcZero]
                      exact child
                    exact prorataSpec_preservesNoMem ca cevm.sta cevm.dyna
                      rawPost childAtZero
                      (fun childTarget => (childAt.2 childTarget).1)
                      childPrecondition
              have interPre : prorataSpec.Pre ca sevm inter :=
                continuationOfPost childPost
              have installedInter :
                  Prog.At prorata ca (pc + 1) sevm inter :=
                ⟨interPre.code, fun target => (target_ne target).elim⟩
              have sumNof : sum pre.state.bal < 2 ^ 256 :=
                precondition.side
              have childBody :
                  ∀ childCommitted : Execution.commits raw = true, ∃ steps,
                    ProrataAccountingReplay offset.toNat
                      (AccountingSnapshot.execEntry ca cevm.sta
                        cevm.dyna.state)
                      steps
                      (AccountingSnapshot.ofState ca
                        (Execution.committedPost raw childCommitted).state) := by
                intro childCommitted
                exact ihChild child childCommitted childAt childPrecondition
                  childDirect childCaller blockIndex transactionIndex
                  (framePath ++ [nextChild]) 0
              rcases Xinst.foreignSomeAccountingReplay spawnEq frameRun
                  resumeRun.symm target_ne sumNof childBody with
                ⟨headSteps, headReplay⟩
              rcases ihNext next committed installedInter interPre
                  (fun target => (target_ne target).elim)
                  (fun target => (target_ne target).elim)
                  blockIndex transactionIndex framePath (nextChild + 1) with
                ⟨tailSteps, tailReplay⟩
              rw [AccountingSnapshot.execEntry_of_target_ne target_ne]
                at tailReplay
              refine ⟨headSteps ++ tailSteps, ?_⟩
              rw [AccountingSnapshot.execEntry_of_target_ne target_ne]
              exact headReplay.append tailReplay

/-- The complete interpreter recursion for committed PRORATA accounting.
Every at-target frame is discharged by the compiled-frame classifier; all
foreign instruction cases preserve and compose the exact accounting replay. -/
theorem Exec.coreProrataAccounting {ca : Adr} :
    Exec.Fa (Exec.Wkn ca prorata
      (fun pc sevm pre out _ =>
        Exec.CoreProrataAccounting ca pc sevm pre out)) := by
  apply lift_core
    (ε := fun pc sevm pre out =>
      Exec.CoreProrataAccounting ca pc sevm pre out)
    (π := fun sevm pre post =>
      Exec.CoreProrataAccounting ca 0 sevm pre (.ok post))
    (analog := fun h => h)
    (ca := ca) (p := prorata)
  · intro sevm pre post run target deeper
    exact Exec.CoreProrataAccounting.atTarget run target deeper
  · intro pc sevm pre error post target
    exact Exec.CoreProrataAccounting.error
  · intro pc sevm pre noneAt targetNe
    exact Exec.CoreProrataAccounting.error
  · intro pc sevm pre n error post hat step targetNe
    exact Exec.CoreProrataAccounting.error
  · intro pc sevm pre n childEvm childOut error post
      hat step child targetNe ihChild
    exact Exec.CoreProrataAccounting.error
  · intro pc sevm pre n inter out hat step next targetNe ihNext
    exact Exec.CoreProrataAccounting.nextNone
      hat step next targetNe ihNext
  · intro pc sevm pre n childEvm childOut inter out
      hat step child next targetNe ihChild ihNext
    exact Exec.CoreProrataAccounting.nextSome
      hat step child next targetNe ihChild ihNext
  · intro pc sevm pre j error post hat step targetNe
    exact Exec.CoreProrataAccounting.error
  · intro pc sevm pre j pc' inter out
      hat step next targetNe ihNext
    exact Exec.CoreProrataAccounting.jump
      hat step next targetNe ihNext
  · intro pc sevm pre l out hat step targetNe
    exact Exec.CoreProrataAccounting.last hat step targetNe

/-- Instantiate the recursive interpreter theorem at the exact EVM root
selected by a successful message entry. -/
theorem Exec.prorataAccountingReplay_of_messageRoot
    {ca : Adr} {msg : Msg} {entry : Benv}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (transfer : msg.benvAfterTransfer = .ok entry)
    (evmEq : (⟨pc, sevm, pre⟩ : Evm) =
      initEvm (msg.withBenv entry))
    (committed : Execution.commits out = true)
    (ready : AccountingMessageReady ca msg)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.execEntry ca sevm pre.state) steps
        (AccountingSnapshot.ofState ca
          (Execution.committedPost out committed).state) := by
  have precondition :=
    ContractSpec.Pre.of_inv_benvAfterTransfer
      ready.runReady.ready.ne ready.runReady.ready.val0
      transfer ready.runReady.ready.state
  have pcEq := congrArg Evm.pc evmEq
  have sevmEq := congrArg Evm.sta evmEq
  have preEq := congrArg Evm.dyna evmEq
  dsimp only [initEvm] at pcEq sevmEq preEq
  subst pc
  subst sevm
  subst pre
  have installed : Prog.At prorata ca 0
      (initSevm (msg.withBenv entry))
      (initDevm (msg.withBenv entry)) := by
    refine ⟨precondition.code, ?_⟩
    intro target
    refine ⟨?_, rfl⟩
    rcases ready.runReady.codeOrForeign with call | foreign
    · exact ready.runReady.ready.code call
        (by simpa [initSevm, Msg.withBenv] using target)
    · exact False.elim (foreign
        (by simpa [initSevm, Msg.withBenv] using target))
  have direct :
      (initSevm (msg.withBenv entry)).currentTarget = ca →
        (initSevm (msg.withBenv entry)).codeAddress = some ca := by
    intro target
    rcases ready.runReady.codeOrForeign with call | foreign
    · exact ready.runReady.ready.codeAddress call
        (by simpa [initSevm, Msg.withBenv] using target)
    · exact False.elim (foreign
        (by simpa [initSevm, Msg.withBenv] using target))
  have caller :
      (initSevm (msg.withBenv entry)).currentTarget = ca →
        (initSevm (msg.withBenv entry)).caller.toB256.toAdr ≠ ca := by
    intro target
    rw [toAdr_toB256]
    exact ready.caller_ne
      (by simpa [initSevm, Msg.withBenv] using target)
  have all := Exec.coreProrataAccounting (ca := ca)
  have core := all 0 (initSevm (msg.withBenv entry))
    (initDevm (msg.withBenv entry)) out run installed
  exact core run committed installed precondition direct caller
    blockIndex transactionIndex [] 0

/-- A retained raw message realizes a complete PRORATA accounting replay from
the wrapper's pre-transfer world to its settled post-state.  A no-slot message
is classified directly; an interpreted slot consumes the generic recursive
execution theorem with root frame provenance. -/
theorem retainedProcessMessageAccountingReplay
    {ca : Adr} {msg : Msg} {post : Devm}
    (trace : _root_.Blanc.ExecutionTrace.ProcessMessageTrace msg (.ok post))
    (ready : AccountingMessageReady ca msg)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca msg.benv.state) steps
        (AccountingSnapshot.ofState ca post.state) := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      let provenance : ProrataAccountingProvenance :=
        { blockIndex := blockIndex
          transactionIndex := transactionIndex
          framePath := []
          actor := none }
      exact ProrataAccountingReplay.of_storage_eq_balance_mono provenance
        (congrFun
          (_root_.Blanc.ExecutionTrace.ProcessMessage.none_ok_getStor_eq
            process) ca)
        (_root_.Blanc.ProcessMessage.targetBalanceMono_of_none process
          ready.runReady.ready.ne ready.runReady.ready.state.side)
  | @some pc sevm pre out run =>
      apply ProcessMessage.accountingReplay_of_body process
        ready.runReady.ready.ne ready.runReady.ready.val0
        ready.runReady.ready.state.side
      intro committed
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with
        ⟨entry, transfer, evmEq⟩
      exact Exec.prorataAccountingReplay_of_messageRoot run transfer evmEq
        committed ready blockIndex transactionIndex

/-- CREATE counterpart of `retainedProcessMessageAccountingReplay`.  Fresh
account preparation and code-deposit settlement are interpreted once around
the same retained recursive constructor execution. -/
theorem retainedProcessCreateMessageAccountingReplay
    {ca : Adr} {msg : Msg} {post : Devm}
    (trace :
      _root_.Blanc.ExecutionTrace.ProcessCreateMessageTrace msg (.ok post))
    (ready : AccountingMessageReady ca msg)
    (targetNone : msg.target.isNone = true)
    (targetNe : msg.currentTarget ≠ ca)
    (fresh : msg.benv.state.getStor msg.currentTarget = .empty)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca msg.benv.state) steps
        (AccountingSnapshot.ofState ca post.state) := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      let provenance : ProrataAccountingProvenance :=
        { blockIndex := blockIndex
          transactionIndex := transactionIndex
          framePath := []
          actor := none }
      exact ProrataAccountingReplay.of_storage_eq_balance_mono provenance
        (congrFun
          (_root_.Blanc.ExecutionTrace.ProcessCreateMessage.none_ok_getStor_eq_of_empty
            process fresh) ca)
        (_root_.Blanc.ProcessCreateMessage.targetBalanceMono_of_none process
          ready.runReady.ready.ne ready.runReady.ready.state.side)
  | @some pc sevm pre out run =>
      apply ProcessCreateMessage.accountingReplay_of_body process
        ready.runReady.ready.ne ready.runReady.ready.val0 fresh
        ready.runReady.ready.state.side
      intro committed
      have preparedInv :=
        ready.runReady.ready.processCreateMessage_msg targetNone targetNe
      have preparedTargetNe :
          (processCreateMessage.msg msg).currentTarget ≠ ca := by
        intro target
        exact targetNe (by
          simpa [processCreateMessage.msg, Msg.withBenv] using target)
      have preparedReady : AccountingMessageReady ca
          (processCreateMessage.msg msg) :=
        ⟨preparedInv.runReady_of_foreign preparedTargetNe,
          fun target => absurd target preparedTargetNe⟩
      have enter := (RunFrame.some_inv process).1
      rcases Frame.enter_run_inv enter with
        ⟨entry, transfer, evmEq⟩
      exact Exec.prorataAccountingReplay_of_messageRoot run transfer evmEq
        committed preparedReady blockIndex transactionIndex

open _root_.Blanc.ExecutionTrace in
/-- The settled message-call wrapper realizes a complete PRORATA accounting
replay from its pre-transfer world to the wrapper's settled world state.  A
create collision runs no code at all; a CREATE execution reuses the create
rung with the freshness its own collision test already certifies; an ordinary
call transports readiness and the accounting projection across the EIP-7702
delegation prefix and delegated-code resolution before reusing the message
rung. -/
theorem retainedMessageCallAccountingReplay
    {ca : Adr} {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : _root_.Blanc.ExecutionTrace.MessageCallTrace msg state out)
    (ready : AccountingMessageReady ca msg)
    (blockIndex : Nat) (transactionIndex : Option Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca msg.benv.state) steps
        (AccountingSnapshot.ofState ca state) := by
  cases trace with
  | createCollision targetNone collision result =>
      have stateEq :=
        processMessageCall_createCollision_state_eq targetNone collision result
      let provenance : ProrataAccountingProvenance :=
        { blockIndex := blockIndex
          transactionIndex := transactionIndex
          framePath := []
          actor := none }
      exact ProrataAccountingReplay.of_storage_eq_balance_mono provenance
        (by rw [stateEq]) (by rw [stateEq])
  | createRun targetNone collision evm core inner result =>
      have targetNe : msg.currentTarget ≠ ca := by
        rcases ready.runReady.codeOrForeign with call | foreign
        · exact Bool.noConfusion (targetNone.symm.trans call)
        · exact foreign
      have fresh := messageCreateCollision_false_getStor_eq_empty collision
      have stateEq :=
        processMessageCall_createRun_state_eq targetNone collision core result
      rw [stateEq]
      exact retainedProcessCreateMessageAccountingReplay inner ready
        targetNone targetNe fresh blockIndex transactionIndex
  | callRun targetSome delegated refund delegation execMsg execMsgEq evm
      core inner result =>
      subst execMsgEq
      have stateEq :=
        processMessageCall_callRun_state_eq targetSome delegation rfl core
          result
      have delegatedInv :=
        ready.runReady.ready.of_messageCallDelegation delegation
      have execReady : AccountingMessageReady ca
          (messageCallExecutionMessage delegated) := by
        refine ⟨⟨delegatedInv.messageCallExecutionMessage, Or.inl ?_⟩, ?_⟩
        · rw [messageCallExecutionMessage_target_eq,
            messageCallDelegation_target_eq delegation]
          exact targetSome
        · intro target
          rw [messageCallExecutionMessage_currentTarget_eq,
            messageCallDelegation_currentTarget_eq delegation] at target
          rw [messageCallExecutionMessage_caller_eq,
            messageCallDelegation_caller_eq delegation]
          exact ready.caller_ne target
      have snapshotEq :
          AccountingSnapshot.ofState ca
              (messageCallExecutionMessage delegated).benv.state =
            AccountingSnapshot.ofState ca msg.benv.state := by
        unfold AccountingSnapshot.ofState
        rw [messageCallExecutionMessage_getStor_eq,
          messageCallExecutionMessage_bal_eq,
          messageCallDelegation_getStor_eq delegation,
          messageCallDelegation_bal_eq delegation]
      rw [stateEq, ← snapshotEq]
      exact retainedProcessMessageAccountingReplay inner execReady
        blockIndex transactionIndex

end Prorata

end Blanc
