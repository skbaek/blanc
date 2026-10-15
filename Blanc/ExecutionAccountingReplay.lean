-- ExecutionAccountingReplay.lean : contract-neutral accounting replay seams.
--
-- Retained CALL/CREATE accounting separates body replay, entry transfer and
-- settlement. Rollback restores the message's pre-transfer world. Successful
-- CREATE preparation and code deposit preserve the storages a boundary reads
-- when its target is outside that boundary's declared storage-owner footprint.
-- A foreign executable slot derives that exclusion from owner protection.
--
-- SettlementCarrier supports any number of observed storage owners, retains
-- whole-world balance equality, and carries structural entry safety. The local
-- ReplayCarrier marks whether it reads storage; balance-only carriers therefore
-- obtain an empty footprint without new code premises. Their strong local entry
-- law and storage-fixed balance-monotone classifier remain unchanged.

import Blanc.ExecutionOccurrence

namespace Blanc

open Jaune

namespace ExecutionAccountingReplay

/-- Entry storage is preserved when a positive debit is foreign or the owner
is protected; the world-sum bound prevents a positive recipient credit wrapping. -/
theorem benvAfterTransfer_getStor_eq_of_safe
    {msg : Msg} {entry : Benv} {owner : Adr}
    (transfer : msg.benvAfterTransfer = .ok entry)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256)
    (safe : msg.shouldTransferValue = true → msg.value ≠ 0 →
      msg.caller ≠ owner ∨ State.Protected msg.benv.state owner) :
    entry.state.getStor owner = msg.benv.state.getStor owner := by
  by_cases zero : msg.value = 0
  · exact benvAfterTransfer_ok_getStor transfer owner (Or.inl zero)
  by_cases transfers : msg.shouldTransferValue = true
  · rcases safe transfers zero with callerNe | hp
    · obtain ⟨debit, sub, rfl⟩ := of_benvAfterTransfer transfers zero transfer
      change (debit.addBal msg.currentTarget msg.value).getStor owner = _
      have debitStorage : debit.getStor owner = msg.benv.state.getStor owner := by
        obtain ⟨_, debitEq⟩ := State.of_subBal sub
        rw [debitEq]
        exact congrArg Acct.stor (State.setBal_get_ne callerNe)
      by_cases targetEq : msg.currentTarget = owner
      · have balance := of_transfer_bal_target sub (fun he => callerNe (he.trans targetEq)) sum_nof
        have positive : (debit.bal msg.currentTarget + msg.value).toNat ≠ 0 := by
          change ((debit.setBal msg.currentTarget _).get msg.currentTarget).bal.toNat = _ at balance
          rw [State.setBal_get_self, Acct.clearIfEmpty_bal] at balance
          have valueNe : msg.value.toNat ≠ 0 := by
            intro h
            apply zero
            exact B256.toNat_inj _ _ h
          change (debit.bal msg.currentTarget + msg.value).toNat = _ at balance
          omega
        unfold State.addBal State.getStor
        rw [State.setBal_get_stor, ite_eq_right]
        · exact debitStorage
        · rintro ⟨_, empty⟩
          apply positive
          have hz : debit.bal msg.currentTarget + msg.value = 0 := empty.2.2
          rw [hz]
          rfl
      · unfold State.addBal State.getStor
        rw [State.setBal_get_ne targetEq]
        exact debitStorage
    · exact benvAfterTransfer_ok_getStor transfer owner (Or.inr hp)
  · rw [of_benvAfterTransfer_no transfers transfer]

/-- Structural storage safety at each owner a boundary observes. -/
def EntryStorageSafe (owners : Adr → Prop) (msg : Msg) : Prop :=
  ∀ owner, owners owner → msg.shouldTransferValue = true → msg.value ≠ 0 →
    msg.caller ≠ owner ∨ State.Protected msg.benv.state owner

/-- The settlement-facing part of a replay interpretation: everything the three
seams below consume, and nothing else.

`Snap` is whatever boundary the contract prices with, `Step` whatever it
records, and `Replay` its own connected-path relation; the seams never inspect
any of the three.  `ofState` is the boundary of an ordinary world state and
`frameEntry` the boundary at an instruction-frame entry, which may sit *before*
a message's value credit and therefore need not be any world state's boundary —
that is the whole reason the two are separate functions.

The three laws are exactly what the seams use, no more:

* `nil` — a boundary replays to itself with no step;
* `worldSilent` — equality of storage at all declared `storageOwners`, and
  equality of the whole balance map, imply boundary equality. A multiaccount
  boundary lists each observed owner; it is not restricted to `ca`;
* `entry_eq_ofState` — a successful transfer with structural entry safety at
  those owners connects frame entry to the pre-transfer boundary.

`ca` is the account the seams call *foreign* frames foreign to: it appears only
in the two value-transfer side conditions of `entry_eq_ofState`.  A carrier
whose boundary ignores balances discharges that law without reading them. -/
structure SettlementCarrier (ca : Adr) where
  /-- The contract's own boundary type. -/
  Snap : Type
  /-- The contract's own accounting step type. -/
  Step : Type
  /-- The contract's own connected replay relation. -/
  Replay : Snap → List Step → Snap → Prop
  /-- The boundary of an ordinary world state. -/
  ofState : State → Snap
  /-- The boundary at an entered instruction frame. -/
  frameEntry : Sevm → State → Snap
  /-- A boundary replays to itself with no step. -/
  nil : ∀ boundary : Snap, Replay boundary [] boundary
  /-- Accounts whose storage the boundary may read. -/
  storageOwners : Adr → Prop
  /-- Scoped storage equality and whole-world balance equality fix the boundary. -/
  worldSilent : ∀ {pre post : State},
    (∀ owner, storageOwners owner → post.getStor owner = pre.getStor owner) →
    post.bal = pre.bal →
    ofState post = ofState pre
  /-- A successful message transfer connects the entered frame's boundary to
  the ordinary boundary of the world the message opened on. -/
  entry_eq_ofState : ∀ {msg : Msg} {entry : Benv},
    (msg.shouldTransferValue = true → msg.caller ≠ ca) →
    (msg.shouldTransferValue = false → msg.currentTarget = ca → msg.value = 0) →
    EntryStorageSafe storageOwners msg →
    msg.benvAfterTransfer = .ok entry →
    sum msg.benv.state.bal < 2 ^ 256 →
    frameEntry (initSevm (msg.withBenv entry)) entry.state =
      ofState msg.benv.state

/-- The account-local replay interpretation: a boundary that reads the single
account `ca`, with the law that produces a step.  It presents itself to the
settlement seams through `ReplayCarrier.toSettlementCarrier`.

`Snap`, `Step`, `Replay`, `ofState`, `frameEntry`, `nil` and `entry_eq_ofState`
are as in `SettlementCarrier`.  The two account-local laws:

* `silent` — balance equality at `ca`, plus storage equality there when
  `readsStorage = true`, fixes the boundary. A false flag requires a proof
  of storage independence and converts to an empty storage footprint;
* `credit` — a storage-fixed strictly increasing balance is some replay, which
  is the only place a step is ever produced.

`Tag` is whatever provenance a credit step must record.  A carrier that records
none sets it to `Unit`. -/
structure ReplayCarrier (ca : Adr) where
  /-- The contract's own boundary type. -/
  Snap : Type
  /-- The contract's own accounting step type. -/
  Step : Type
  /-- Provenance a produced credit step must carry. -/
  Tag : Type
  /-- The contract's own connected replay relation. -/
  Replay : Snap → List Step → Snap → Prop
  /-- The boundary of an ordinary world state. -/
  ofState : State → Snap
  /-- The boundary at an entered instruction frame. -/
  frameEntry : Sevm → State → Snap
  /-- A boundary replays to itself with no step. -/
  nil : ∀ boundary : Snap, Replay boundary [] boundary
  /-- Whether silence requires storage equality at this account. -/
  readsStorage : Bool
  /-- A transition invisible to this account moves no boundary. -/
  silent : ∀ {pre post : State},
    (readsStorage = true → post.getStor ca = pre.getStor ca) →
    (post.bal ca).toNat = (pre.bal ca).toNat →
    ofState post = ofState pre
  /-- A storage-fixed positive balance increase is some replay. -/
  credit : ∀ (_tag : Tag) {pre post : State} {amount : Nat},
    post.getStor ca = pre.getStor ca →
    (post.bal ca).toNat = (pre.bal ca).toNat + amount →
    0 < amount →
    ∃ steps, Replay (ofState pre) steps (ofState post)
  /-- A successful message transfer connects the entered frame's boundary to
  the ordinary boundary of the world the message opened on. -/
  entry_eq_ofState : ∀ {msg : Msg} {entry : Benv},
    (msg.shouldTransferValue = true → msg.caller ≠ ca) →
    (msg.shouldTransferValue = false → msg.currentTarget = ca → msg.value = 0) →
    msg.benvAfterTransfer = .ok entry →
    sum msg.benv.state.bal < 2 ^ 256 →
    frameEntry (initSevm (msg.withBenv entry)) entry.state =
      ofState msg.benv.state

/-- A local carrier observes `ca` storage exactly when its storage flag is true;
its stronger local entry law also supplies the settlement entry law. -/
def ReplayCarrier.toSettlementCarrier {ca : Adr} (C : ReplayCarrier ca) :
    SettlementCarrier ca where
  Snap := C.Snap
  Step := C.Step
  Replay := C.Replay
  ofState := C.ofState
  frameEntry := C.frameEntry
  nil := C.nil
  storageOwners owner := owner = ca ∧ C.readsStorage = true
  worldSilent := fun storage_eq balance_eq =>
    C.silent (fun reads => storage_eq ca ⟨rfl, reads⟩)
      (congrArg B256.toNat (congrFun balance_eq ca))
  entry_eq_ofState := fun caller value _ transfer bound =>
    C.entry_eq_ofState caller value transfer bound

namespace SettlementCarrier

variable {ca : Adr}

/-- Equal boundaries contribute no step. -/
theorem nilOfEq (C : SettlementCarrier ca) {pre post : C.Snap} (eq : post = pre) :
    C.Replay pre [] post := by
  rw [eq]
  exact C.nil pre

/-- Settlement-aware accounting replay for one retained CALL message, observed.
A committing child contributes its recursively proved body together with that
body's observation; a noncommitting child rolls back to the message's
pre-transfer world and contributes nothing, which `obs` sees as nothing. -/
theorem processMessage_of_body_observed (C : SettlementCarrier ca)
    {O : Type} (obs : List C.Step → List O) (obs_nil : obs [] = [])
    {msg : Msg} {post : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (process : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (entrySafe : EntryStorageSafe C.storageOwners msg)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256)
    {settled : List O}
    (body : ∀ committed : Execution.commits out = true, ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost out committed).state) ∧
      obs steps = settled) :
    ∃ steps,
      C.Replay (C.ofState msg.benv.state) steps (C.ofState post.state) ∧
      obs steps = if Frame.settlementCommits (Frame.ofCall msg) out = true
        then settled else [] := by
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
    have prefixEq :
        C.frameEntry sevm pre.state = C.ofState msg.benv.state := by
      rw [sevmEq, preState]
      exact C.entry_eq_ofState caller_ne value_zero entrySafe transfer sum_nof
    have postState : post.state =
        (Execution.committedPost out committed).state :=
      _root_.Blanc.ProcessMessage.ok_state_eq_committedPost process committed
    rcases body committed with ⟨steps, replay, observed⟩
    refine ⟨steps, ?_, by rw [ite_eq_left settles]; exact observed⟩
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
      cases errorEq : post.error <;> simp_all only [ExceptT.stM_eq, ne_eq, Nat.reducePow, Bool.not_eq_true, Option.isNone_none, not_true_eq_false, Option.isNone_some, Bool.false_eq_true, not_false_eq_true, Option.isSome_some]
    have rollback :=
      (_root_.Blanc.ProcessMessage.rollback_of_error process postError).1
    exact ⟨[], C.nilOfEq (congrArg C.ofState rollback),
      by rw [ite_eq_right settles]; exact obs_nil⟩

/-- Settlement-aware accounting replay for one retained CALL message.  A
committing child contributes its recursively proved body; a noncommitting child
rolls back to the message's pre-transfer world and contributes nothing. -/
theorem processMessage_of_body (C : SettlementCarrier ca)
    {msg : Msg} {post : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (process : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (entrySafe : EntryStorageSafe C.storageOwners msg)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256)
    (body : ∀ committed : Execution.commits out = true, ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost out committed).state)) :
    ∃ steps,
      C.Replay (C.ofState msg.benv.state) steps (C.ofState post.state) := by
  exact (C.processMessage_of_body_observed (fun _ => ([] : List Unit)) rfl process
    caller_ne value_zero entrySafe sum_nof (settled := [])
    fun committed => (body committed).imp fun _ replay => ⟨replay, rfl⟩).imp
    fun _ replay => replay.1

/-- Settlement-aware accounting replay for one retained CREATE constructor,
observed.  A settling constructor's observation is its body's, because a
settled CREATE's raw execution commits and so its inner CALL settles. -/
theorem processCreateMessage_of_body_observed (C : SettlementCarrier ca)
    {O : Type} (obs : List C.Step → List O) (obs_nil : obs [] = [])
    {msg : Msg} {post : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (process : ProcessCreateMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (targetAway : ∀ owner, C.storageOwners owner → msg.currentTarget ≠ owner)
    (entrySafe : EntryStorageSafe C.storageOwners msg)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256)
    {settled : List O}
    (body : ∀ committed : Execution.commits out = true, ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost out committed).state) ∧
      obs steps = settled) :
    ∃ steps,
      C.Replay (C.ofState msg.benv.state) steps (C.ofState post.state) ∧
      obs steps = if Frame.settlementCommits (Frame.ofCreate msg) out = true
        then settled else [] := by
  by_cases settles :
      Frame.settlementCommits (Frame.ofCreate msg) out = true
  · have clean : post.error.isSome = false := by
      have settledEq := (RunFrame.some_inv process).2
      unfold Frame.settlementCommits at settles
      rw [← settledEq] at settles
      cases errorEq : post.error <;> simp_all only [ExceptT.stM_eq, ne_eq, Nat.reducePow, Option.isNone_none, Option.isSome_none, Option.isNone_some, Bool.false_eq_true]
    rcases _root_.Blanc.ProcessCreateMessage.ok_getStor_eq_inner_of_clean
        process clean with ⟨inner, innerProcess, postStor, innerClean⟩
    rcases _root_.Jaune.ProcessCreateMessage.ok_state_eq_inner_of_no_error
        process clean with ⟨balanceInner, balanceProcess, postBalance⟩
    have innerEq : inner = balanceInner := by
      have left := (RunFrame.some_inv innerProcess).2
      have right := (RunFrame.some_inv balanceProcess).2
      exact Except.ok.inj (left.trans right.symm)
    subst balanceInner
    have preparedGet : ∀ owner, C.storageOwners owner →
        (processCreateMessage.msg msg).benv.state.get owner = msg.benv.state.get owner := by
      intro owner observed
      dsimp only [processCreateMessage.msg, Msg.withBenv, Benv.setStor,
        Benv.incrNonce, addCreatedAccount, Benv.clearStorageWritesIfEmpty]
      rw [State.incrNonce, State.setAccount_get_ne _ (targetAway owner observed),
        State.setStor, State.get_set_ne _ (targetAway owner observed)]
    have preparedStor := fun owner observed => congrArg Acct.stor (preparedGet owner observed)
    have preparedSafe : EntryStorageSafe C.storageOwners (processCreateMessage.msg msg) := by
      intro owner observed transfers nonzero
      rcases entrySafe owner observed transfers nonzero with foreign | hp
      · exact Or.inl foreign
      · right
        unfold State.Protected at hp ⊢
        rw [preparedGet owner observed]
        exact hp
    have preparedBalance :=
      _root_.Jaune.processCreateMessage_msg_bal_eq msg
    have preparedSnapshot :
        C.ofState (processCreateMessage.msg msg).benv.state =
          C.ofState msg.benv.state :=
      C.worldSilent preparedStor preparedBalance
    have postSnapshot :
        C.ofState post.state = C.ofState inner.state :=
      C.worldSilent (fun owner observed => (postStor owner (targetAway owner observed)).2) postBalance
    have innerSum :
        sum (processCreateMessage.msg msg).benv.state.bal < 2 ^ 256 := by
      rw [preparedBalance]
      exact sum_nof
    have innerSettles :
        Frame.settlementCommits
          (Frame.ofCall (processCreateMessage.msg msg)) out = true :=
      Frame.settlementCommits_ofCall_of_raw_commits
        (Frame.raw_commits_of_settlementCommits settles)
    rcases C.processMessage_of_body_observed obs obs_nil
        innerProcess caller_ne value_zero preparedSafe innerSum body with
      ⟨steps, replay, observed⟩
    rw [ite_eq_left innerSettles] at observed
    refine ⟨steps, ?_, by rw [ite_eq_left settles]; exact observed⟩
    rw [← preparedSnapshot, postSnapshot]
    exact replay
  · have settledEq := (RunFrame.some_inv process).2
    have postError : post.error.isSome = true := by
      have notClean : post.error.isSome ≠ false := by
        intro clean
        apply settles
        unfold Frame.settlementCommits
        rw [← settledEq]
        cases errorEq : post.error <;> simp_all only [ExceptT.stM_eq, ne_eq, Nat.reducePow, Bool.not_eq_true, Option.isSome_none, Option.isNone_none, Option.isSome_some, Bool.true_eq_false]
      cases errorEq : post.error <;> simp_all only [ExceptT.stM_eq, ne_eq, Nat.reducePow, Bool.not_eq_true, Option.isSome_none, not_true_eq_false, Option.isSome_some, Bool.true_eq_false, not_false_eq_true]
    have rollback :=
      _root_.Blanc.ProcessCreateMessage.rollback_of_error process postError
    exact ⟨[], C.nilOfEq (congrArg C.ofState rollback),
      by rw [ite_eq_right settles]; exact obs_nil⟩

/-- Settlement-aware accounting replay for one retained CREATE constructor.
Fresh-account preparation is silent in any account-local projection; clean code
deposit preserves the constructor endpoint, while every failed settlement rolls
back to the outer CREATE-message world. -/
theorem processCreateMessage_of_body (C : SettlementCarrier ca)
    {msg : Msg} {post : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (process : ProcessCreateMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (targetAway : ∀ owner, C.storageOwners owner → msg.currentTarget ≠ owner)
    (entrySafe : EntryStorageSafe C.storageOwners msg)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256)
    (body : ∀ committed : Execution.commits out = true, ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost out committed).state)) :
    ∃ steps,
      C.Replay (C.ofState msg.benv.state) steps (C.ofState post.state) := by
  exact (C.processCreateMessage_of_body_observed (fun _ => ([] : List Unit)) rfl
    process caller_ne value_zero targetAway entrySafe sum_nof (settled := [])
    fun committed => (body committed).imp fun _ replay => ⟨replay, rfl⟩).imp
    fun _ replay => replay.1

/-- Recursive accounting transport for one actual filled executable slot in a
foreign frame, observed: the slot contributes its child's observation exactly
when the spawned frame settles. -/
theorem xinstForeignSome_observed (C : SettlementCarrier ca)
    {O : Type} (obs : List C.Step → List O) (obs_nil : obs [] = [])
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    {cevm : Evm} {raw : Execution} {settled : Devm}
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (frameRun : RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled))
    (resumeRun : resume.run (.ok settled) = .ok post)
    (target_ne : sevm.currentTarget ≠ ca)
    (hfork : CoveredFork sevm.benvStat.fork)
    (protection : ∀ owner, C.storageOwners owner → State.Protected pre.state owner)
    (sum_nof : sum pre.state.bal < 2 ^ 256)
    {child : List O}
    (body : ∀ committed : Execution.commits raw = true, ∃ steps,
      C.Replay (C.frameEntry cevm.sta cevm.dyna.state) steps
        (C.ofState (Execution.committedPost raw committed).state) ∧
      obs steps = child) :
    ∃ steps,
      C.Replay (C.ofState pre.state) steps (C.ofState post.state) ∧
      obs steps = if Frame.settlementCommits frame raw = true
        then child else [] := by
  rcases Xinst.step_shapeCovered sevm pre x hfork with
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
          (UInt64.add_one_ne_zero_of_ne_max
            (genericCreate_step_spawn_nonce_ne_max spawn))
    have preparedBalance : createPre.state.bal = d.state.bal := by
      simpa only [createPre] using genericCreate_prepared_bal sevm d newAddress
    have preparedSnapshot :
        C.ofState createPre.state = C.ofState d.state :=
      C.worldSilent (fun owner _ => congrFun preparedStor owner) preparedBalance
    have creatorNonce : (d.state.get sevm.currentTarget).nonce + 1 ≠ 0 :=
      UInt64.add_one_ne_zero_of_ne_max (genericCreate_step_spawn_nonce_ne_max spawn)
    have dProtected : ∀ owner, C.storageOwners owner → State.Protected d.state owner := by
      intro owner observed
      rw [← hprefix.state]
      exact protection owner observed
    have preparedProtected : ∀ owner, C.storageOwners owner →
        State.Protected createPre.state owner := by
      intro owner observed
      change State.Protected (d.state.incrNonce sevm.currentTarget) owner
      unfold State.Protected
      by_cases equal : sevm.currentTarget = owner
      · subst owner
        left
        simpa only [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce] using creatorNonce
      · rw [State.incrNonce, State.setAccount_get_ne _ equal]
        exact dProtected owner observed
    have targetAway : ∀ owner, C.storageOwners owner → msg.currentTarget ≠ owner := by
      intro owner observed equal
      have fresh := genericCreate_step_spawn_target_unprotected spawn
      apply fresh
      have targetEq : newAddress = owner := equal
      rw [targetEq]
      exact dProtected owner observed
    have entrySafe : EntryStorageSafe C.storageOwners msg := by
      intro owner observed _ _
      exact Or.inr (preparedProtected owner observed)
    have callerNe : msg.shouldTransferValue = true → msg.caller ≠ ca := by
      simpa only [msg, createMsg, ne_eq, forall_const] using target_ne
    have valueZero : msg.shouldTransferValue = false →
        msg.currentTarget = ca → msg.value = 0 := by
      simp only [msg, createMsg, Bool.true_eq_false, IsEmpty.forall_iff]
    have msgSum : sum msg.benv.state.bal < 2 ^ 256 := by
      change sum createPre.state.bal < 2 ^ 256
      rw [preparedBalance]
      exact dSum
    rcases C.processCreateMessage_of_body_observed obs obs_nil process callerNe
        valueZero targetAway entrySafe msgSum body with ⟨steps, replay, observed⟩
    have postState : post.state = settled.state :=
      Resume.create_state resumeRun
    refine ⟨steps, ?_, observed⟩
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
      simpa only [msg, callMsg, ne_eq] using callerNe
    have msgValueZero : msg.shouldTransferValue = false →
        msg.currentTarget = ca → msg.value = 0 := by
      simpa only [msg, callMsg] using valueZero
    have msgSum : sum msg.benv.state.bal < 2 ^ 256 := by
      change sum d.state.bal < 2 ^ 256
      exact dSum
    have entrySafe : EntryStorageSafe C.storageOwners msg := by
      intro owner observed _ _
      right
      change State.Protected d.state owner
      rw [← hprefix.state]
      exact protection owner observed
    rcases C.processMessage_of_body_observed obs obs_nil process msgCallerNe
        msgValueZero entrySafe msgSum body with ⟨steps, replay, observed⟩
    have postState : post.state = settled.state :=
      Resume.call_state resumeRun
    refine ⟨steps, ?_, observed⟩
    rw [hprefix.state, postState]
    exact replay

/-- Recursive accounting transport for one actual filled executable slot in a
foreign frame.  CALL and CREATE share the same settlement-aware child replay;
their distinct instruction prefixes and resumptions are projection-silent. -/
theorem xinstForeignSome (C : SettlementCarrier ca)
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    {cevm : Evm} {raw : Execution} {settled : Devm}
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (frameRun : RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled))
    (resumeRun : resume.run (.ok settled) = .ok post)
    (target_ne : sevm.currentTarget ≠ ca)
    (hfork : CoveredFork sevm.benvStat.fork)
    (protection : ∀ owner, C.storageOwners owner → State.Protected pre.state owner)
    (sum_nof : sum pre.state.bal < 2 ^ 256)
    (body : ∀ committed : Execution.commits raw = true, ∃ steps,
      C.Replay (C.frameEntry cevm.sta cevm.dyna.state) steps
        (C.ofState (Execution.committedPost raw committed).state)) :
    ∃ steps,
      C.Replay (C.ofState pre.state) steps (C.ofState post.state) := by
  exact (C.xinstForeignSome_observed (fun _ => ([] : List Unit)) rfl spawn frameRun
    resumeRun target_ne hfork protection sum_nof (child := [])
    fun committed => (body committed).imp fun _ replay => ⟨replay, rfl⟩).imp
    fun _ replay => replay.1

end SettlementCarrier

/-- A monoid-homomorphic observation of a carrier's step lists, with what one
settled frame contributes and a credit law observed as nothing.

`obs` reads a replay's step list as a list of observations, turning `++` into
`++`; `frameObs` is what one settled frame is expected to contribute; `credit`
is the carrier's own credit law with the produced steps observed as nothing.
`ReplayObservation.trivial` observes nothing at all, and every seam and rung
without an observation is the observed one read through it. -/
structure ReplayObservation {ca : Adr} (C : ReplayCarrier ca) where
  O : Type
  obs : List C.Step → List O
  obs_nil : obs [] = []
  obs_append : ∀ left right, obs (left ++ right) = obs left ++ obs right
  frameObs : Exec.Frame → List O
  credit : ∀ (_tag : C.Tag) {pre post : State} {amount : Nat},
    post.getStor ca = pre.getStor ca →
    (post.bal ca).toNat = (pre.bal ca).toNat + amount →
    0 < amount →
    ∃ steps, C.Replay (C.ofState pre) steps (C.ofState post) ∧ obs steps = []

/-- The observation that sees nothing: the carrier's own credit law suffices. -/
def ReplayObservation.trivial {ca : Adr} (C : ReplayCarrier ca) :
    ReplayObservation C where
  O := Unit
  obs := fun _ => []
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs := fun _ => []
  credit := fun tag _ _ _ storage_eq balance_eq positive =>
    (C.credit tag storage_eq balance_eq positive).imp
      fun _ replay => ⟨replay, rfl⟩

namespace ReplayCarrier

variable {ca : Adr}

/-! The seams restated at an account-local carrier.  They are the parent
`SettlementCarrier` seams verbatim; they keep their names here because
consumers and the repository audit cite them at `ReplayCarrier`. -/

/-- Equal boundaries contribute no step. -/
theorem nilOfEq (C : ReplayCarrier ca) {pre post : C.Snap} (eq : post = pre) :
    C.Replay pre [] post := by
  rw [eq]
  exact C.nil pre

/-- `SettlementCarrier.processMessage_of_body` at an account-local carrier. -/
theorem processMessage_of_body (C : ReplayCarrier ca)
    {msg : Msg} {post : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (process : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256)
    (body : ∀ committed : Execution.commits out = true, ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost out committed).state)) :
    ∃ steps,
      C.Replay (C.ofState msg.benv.state) steps (C.ofState post.state) :=
  C.toSettlementCarrier.processMessage_of_body process caller_ne value_zero
    (fun owner observed transfers _ => Or.inl (by rw [observed.1]; exact caller_ne transfers))
    sum_nof body

/-- `SettlementCarrier.processCreateMessage_of_body` at an account-local
carrier. -/
theorem processCreateMessage_of_body (C : ReplayCarrier ca)
    {msg : Msg} {post : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (process : ProcessCreateMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (targetAway : C.readsStorage = true → msg.currentTarget ≠ ca)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256)
    (body : ∀ committed : Execution.commits out = true, ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost out committed).state)) :
    ∃ steps,
      C.Replay (C.ofState msg.benv.state) steps (C.ofState post.state) :=
  C.toSettlementCarrier.processCreateMessage_of_body process caller_ne
    value_zero (fun owner observed => by rw [observed.1]; exact targetAway observed.2)
    (fun owner observed transfers _ => Or.inl (by rw [observed.1]; exact caller_ne transfers))
    sum_nof body

/-- `SettlementCarrier.xinstForeignSome` at an account-local carrier. -/
theorem xinstForeignSome (C : ReplayCarrier ca)
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    {cevm : Evm} {raw : Execution} {settled : Devm}
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (frameRun : RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled))
    (resumeRun : resume.run (.ok settled) = .ok post)
    (target_ne : sevm.currentTarget ≠ ca)
    (hfork : CoveredFork sevm.benvStat.fork)
    (protection : C.readsStorage = true → State.Protected pre.state ca)
    (sum_nof : sum pre.state.bal < 2 ^ 256)
    (body : ∀ committed : Execution.commits raw = true, ∃ steps,
      C.Replay (C.frameEntry cevm.sta cevm.dyna.state) steps
        (C.ofState (Execution.committedPost raw committed).state)) :
    ∃ steps,
      C.Replay (C.ofState pre.state) steps (C.ofState post.state) :=
  C.toSettlementCarrier.xinstForeignSome spawn frameRun resumeRun target_ne hfork
    (fun owner observed => by rw [observed.1]; exact protection observed.2) sum_nof body

/-- A transition invisible to this account contributes no step. -/
theorem silentReplay (C : ReplayCarrier ca) {pre post : State}
    (storage_eq : post.getStor ca = pre.getStor ca)
    (balance_eq : (post.bal ca).toNat = (pre.bal ca).toNat) :
    C.Replay (C.ofState pre) [] (C.ofState post) :=
  C.nilOfEq (C.silent (fun _ => storage_eq) balance_eq)

/-- `ofStorageEqBalanceMono`, observed: the one credit it may produce is
observed as nothing. -/
theorem ofStorageEqBalanceMono_observed (C : ReplayCarrier ca)
    (V : ReplayObservation C) (tag : C.Tag) {pre post : State}
    (storage_eq : post.getStor ca = pre.getStor ca)
    (balance_mono : (pre.bal ca).toNat ≤ (post.bal ca).toNat) :
    ∃ steps, C.Replay (C.ofState pre) steps (C.ofState post) ∧
      V.obs steps = [] := by
  let amount := (post.bal ca).toNat - (pre.bal ca).toNat
  have balance_eq :
      (post.bal ca).toNat = (pre.bal ca).toNat + amount := by
    dsimp only [amount]
    omega
  by_cases positive : 0 < amount
  · exact V.credit tag storage_eq balance_eq positive
  · have zero : amount = 0 := Nat.eq_zero_of_not_pos positive
    exact ⟨[], C.silentReplay storage_eq (by omega), V.obs_nil⟩

/-- Any projected transition that fixes this account's storage and cannot lower
its balance is either one positive credit or no step at all.  This endpoint
lemma lets a foreign-opcode proof expose only its two relevant facts instead of
restating the four-way classifier. -/
theorem ofStorageEqBalanceMono (C : ReplayCarrier ca) (tag : C.Tag)
    {pre post : State}
    (storage_eq : post.getStor ca = pre.getStor ca)
    (balance_mono : (pre.bal ca).toNat ≤ (post.bal ca).toNat) :
    ∃ steps, C.Replay (C.ofState pre) steps (C.ofState post) := by
  exact (C.ofStorageEqBalanceMono_observed (ReplayObservation.trivial C) tag
    storage_eq balance_mono).imp fun _ replay => replay.1

end ReplayCarrier

/-! ### A second, deliberately un-ledger-shaped carrier

The seams above are only a hoist if their interface is weaker than the one
contract that first needed them.  `balanceCarrier` is the witness: its boundary
is a bare `Nat`, it records no storage at all, its steps are the credit amounts
themselves, and its replay relation is an arithmetic equation rather than an
inductive family.  It nevertheless has to offset the entry boundary by the
message's own value credit, exactly as a ledger-shaped carrier does, because
that offset is a fact about EVM message entry rather than about ledgers.

Both `balanceEntry_eq_ofState` and the seam restated at it below are ordinary
theorems about retained messages; nothing in this section mentions a contract. -/

/-- The balance boundary at an entered instruction frame: a frame executing
`ca` is viewed immediately *before* its value credit, every foreign frame at its
ordinary balance. -/
def balanceEntry (ca : Adr) (sevm : Sevm) (state : State) : Nat :=
  if sevm.currentTarget = ca then (state.bal ca).toNat - sevm.value.toNat
  else (state.bal ca).toNat

/-- A successful message transfer connects the entered frame's balance boundary
exactly to the ordinary balance of the pre-transfer world. -/
theorem balanceEntry_eq_ofState {ca : Adr} {msg : Msg} {entry : Benv}
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (transfer : msg.benvAfterTransfer = .ok entry)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256) :
    balanceEntry ca (initSevm (msg.withBenv entry)) entry.state =
      (msg.benv.state.bal ca).toNat := by
  have targetEq : (initSevm (msg.withBenv entry)).currentTarget =
      msg.currentTarget := rfl
  have valueEq : (initSevm (msg.withBenv entry)).value = msg.value := rfl
  rw [balanceEntry, targetEq, valueEq]
  cases shouldTransfer : msg.shouldTransferValue with
  | false =>
      have noTransfer : ¬ msg.shouldTransferValue = true := by
        simp only [shouldTransfer, Bool.false_eq_true, not_false_eq_true]
      have entry_eq := of_benvAfterTransfer_no noTransfer transfer
      subst entry
      by_cases target_eq : msg.currentTarget = ca
      · have valueNat : msg.value.toNat = 0 := by
          rw [value_zero shouldTransfer target_eq]
          rfl
        simp only [target_eq, ↓reduceIte, valueNat, tsub_zero]
      · simp only [target_eq, ↓reduceIte]
  | true =>
      by_cases hzero : msg.value = 0
      · rw [Msg.benvAfterTransfer_of_value_zero hzero] at transfer
        cases transfer
        simp only [hzero, B256.toNat_zero, tsub_zero, ite_self]
      rcases of_benvAfterTransfer shouldTransfer hzero transfer with
        ⟨debit, sub, rfl⟩
      by_cases target_eq : msg.currentTarget = ca
      · subst ca
        rw [ite_eq_left rfl]
        change ((debit.addBal msg.currentTarget msg.value).bal
            msg.currentTarget).toNat - msg.value.toNat = _
        rw [of_transfer_bal_target sub (caller_ne shouldTransfer) sum_nof]
        exact Nat.add_sub_cancel _ _
      · rw [ite_eq_right target_eq]
        change ((debit.addBal msg.currentTarget msg.value).bal ca).toNat = _
        exact congrArg B256.toNat
          (of_transfer_bal_other sub (caller_ne shouldTransfer) target_eq)

/-- The bare-balance carrier: boundaries are `Nat`, steps are credit amounts,
and a replay is the arithmetic statement that the credits account for the whole
move.  It reads no storage and records no provenance. -/
def balanceCarrier (ca : Adr) : ReplayCarrier ca where
  readsStorage := false
  Snap := Nat
  Step := Nat
  Tag := Unit
  Replay pre steps post := pre + steps.sum = post
  ofState state := (state.bal ca).toNat
  frameEntry := balanceEntry ca
  nil := by
    intro boundary
    simp only [List.sum_nil, add_zero]
  silent := by
    intro _ _ _ balance_eq
    exact balance_eq
  credit := by
    intro _ _ _ amount _ balance_eq _
    exact ⟨[amount], by simpa only [List.sum_cons, List.sum_nil, add_zero] using balance_eq.symm⟩
  entry_eq_ofState := by
    intro _ _ caller_ne value_zero transfer sum_nof
    exact balanceEntry_eq_ofState caller_ne value_zero transfer sum_nof

/-- A settled CALL message raises `ca`'s balance by exactly the credits its
committed body raised it by, measured from the frame's pre-credit entry
boundary.  This is `ReplayCarrier.processMessage_of_body` at `balanceCarrier`,
and it is the seam's whole content at a carrier with no ledger in it. -/
theorem ProcessMessage.targetBalanceCredits_of_body {ca : Adr}
    {msg : Msg} {post : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (process : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256)
    (body : ∀ committed : Execution.commits out = true, ∃ credits : List Nat,
      balanceEntry ca sevm pre.state + credits.sum =
        (((Execution.committedPost out committed).state).bal ca).toNat) :
    ∃ credits : List Nat,
      (msg.benv.state.bal ca).toNat + credits.sum =
        (post.state.bal ca).toNat :=
  (balanceCarrier ca).processMessage_of_body process caller_ne value_zero
    sum_nof body

/-- A storage-fixed balance-monotone transition is accounted for by exactly one
credit at `balanceCarrier`.  This is `ReplayCarrier.ofStorageEqBalanceMono` at
the second carrier, and it is what shows the `credit` field is not obliged to
produce a ledger-shaped step. -/
theorem targetBalanceCredits_of_balance_mono {ca : Adr} {pre post : State}
    (storage_eq : post.getStor ca = pre.getStor ca)
    (balance_mono : (pre.bal ca).toNat ≤ (post.bal ca).toNat) :
    ∃ credits : List Nat,
      (pre.bal ca).toNat + credits.sum = (post.bal ca).toNat :=
  (balanceCarrier ca).ofStorageEqBalanceMono () storage_eq balance_mono

end ExecutionAccountingReplay

end Blanc
