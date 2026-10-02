import Blanc.Lift.UniswapV2Pair.TransferEntries
import Blanc.Lift.UniswapV2Pair.ApproveSource

/-! Finite tagged storage and the existing immediate transfer handler. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def transferTouched (owner recipient : Adr) : List WriterKey :=
  [.balance owner, .balance recipient]

def balanceSourceState (st : State) (owner : Adr) (value : B256) : State :=
  { st with balanceOf := Function.update st.balanceOf owner value }

def transferSourceState (st : State) (owner recipient : Adr) (amount : B256) : State :=
  { st with balanceOf := (Blanc.ledgerCredit (Blanc.ledgerDebit st.balanceOf owner amount)
      recipient amount) }

theorem balanceSourceState_value (st : State) (owner : Adr) (value : B256) (k : WriterKey) :
    k.value (balanceSourceState st owner value) =
      if k = .balance owner then value else k.value st := by
  cases k with
  | allowance a p => rfl
  | nonce a => rfl
  | balance a =>
    dsimp only [WriterKey.value, balanceSourceState]
    by_cases same : a = owner
    · subst a
      rw [Function.update_self, ite_eq_left rfl]
    · have different : WriterKey.balance a ≠ .balance owner :=
        fun eq => same (WriterKey.balance.inj eq)
      rw [Function.update_of_ne same, ite_eq_right different]

/-- A tracked balance store preserves fixed physical rows and the other tagged logical maps. -/
theorem WriterRep.balance_store {K : WriterKey → Prop} {s : Stor} {st : State}
    {owner : Adr} {value : B256} (rep : WriterRep K s st) (tracked : K (.balance owner)) :
    WriterRep K (s.set (WriterKey.slot (.balance owner)) value)
      (balanceSourceState st owner value) := by
  have off := rep.apart (.balance owner) tracked
  have unchanged (n : B256) (fixed : n ∈ writerFixedSlots) :
      (s.set (WriterKey.slot (.balance owner)) value).get n = s.get n :=
    Stor.get_set_ne s (k := WriterKey.slot (.balance owner)) (a := n)
      (fun eq => off (eq.symm ▸ fixed)) value
  refine ⟨rep.finite, ?_, rep.support.set tracked value, rep.inj, rep.apart, ?_, ?_⟩
  · dsimp only [WriterFixedMatches, balanceSourceState]
    rw [unchanged 0 (by decide), unchanged 3 (by decide), unchanged 5 (by decide),
      unchanged 6 (by decide), unchanged 7 (by decide), unchanged 8 (by decide),
      unchanged 9 (by decide), unchanged 10 (by decide), unchanged 11 (by decide),
      unchanged 12 (by decide)]
    exact rep.fixed
  · intro k member
    by_cases same : k = .balance owner
    · subst k
      rw [Stor.get_set_self, balanceSourceState_value, ite_eq_left rfl]
    · have separate : WriterKey.slot (.balance owner) ≠ k.slot :=
        fun eq => same (rep.inj k (.balance owner) member tracked eq.symm)
      rw [Stor.get_set_ne s separate value, balanceSourceState_value, ite_eq_right same]
      exact rep.selected k member
  · intro k outside
    have different : k ≠ .balance owner := by
      intro eq
      subst k
      exact outside tracked
    rw [balanceSourceState_value, ite_eq_right different]
    exact rep.logicalZero k outside

theorem WriterRep.transfer_store {K : WriterKey → Prop} {s : Stor} {st : State}
    {owner recipient : Adr} {amount : B256} (rep : WriterRep K s st)
    (fresh : WriterFreshKeys K (transferTouched owner recipient)) :
    WriterRep (WriterExtend K (transferTouched owner recipient))
      ((s.set (WriterKey.slot (.balance owner)) (st.balanceOf owner - amount)).set
        (WriterKey.slot (.balance recipient))
        (Blanc.ledgerDebit st.balanceOf owner amount recipient + amount))
      (transferSourceState st owner recipient amount) := by
  have extended := rep.extend fresh
  have ownerKey : WriterExtend K (transferTouched owner recipient) (.balance owner) :=
    .inr (List.mem_cons.mpr (.inl rfl))
  have recipientKey : WriterExtend K (transferTouched owner recipient) (.balance recipient) :=
    .inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl)))
  have debited := extended.balance_store (value := st.balanceOf owner - amount) ownerKey
  exact debited.balance_store
    (value := Blanc.ledgerDebit st.balanceOf owner amount recipient + amount) recipientKey

theorem transfer_source_reads {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (transferTouched sevm.caller (transferRecipient sevm))) :
    transferSourceWord sevm b sevm.caller = st.balanceOf sevm.caller ∧
      transferCreditWord sevm b =
        Blanc.ledgerDebit st.balanceOf sevm.caller (transferAmount sevm) (transferRecipient sevm) := by
  have extended := rep.extend fresh
  have ownerKey : WriterExtend K (transferTouched sevm.caller (transferRecipient sevm))
      (.balance sevm.caller) := .inr (List.mem_cons.mpr (.inl rfl))
  have recipientKey : WriterExtend K (transferTouched sevm.caller (transferRecipient sevm))
      (.balance (transferRecipient sevm)) :=
    .inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl)))
  have source : transferSourceWord sevm b sevm.caller = st.balanceOf sevm.caller :=
    extended.selected (.balance sevm.caller) ownerKey
  refine ⟨source, ?_⟩
  change ((transferDebitBase sevm (transferLoadedBase sevm b) sevm.caller
    (transferDebitedWord sevm b)).getStor sevm.currentTarget).get
    (transferBalanceSlot (transferRecipient sevm)) = _
  rw [transferDebitBase, afterSstore_getStor_self, transferLoadedBase, afterSload_getStor]
  unfold transferDebitedWord
  rw [source]
  exact (extended.balance_store (value := st.balanceOf sevm.caller - transferAmount sevm)
    ownerKey).selected (.balance (transferRecipient sevm)) recipientKey

def transferDecodedEntry (sevm : Sevm) : Entry :=
  .transfer (transferRecipient sevm) (transferAmount sevm)

def transferRawLog (pair owner recipient : Adr) (amount : B256) : Jaune.Log :=
  ⟨pair, [transferTopic, owner.toB256, recipient.toB256], amount.toBytes⟩

def transferSourceFrame (current : Checkpoint) (ctx : Context)
    (recipient : Adr) (amount : B256) : Frame :=
  (Frame.enter current ctx (.transfer recipient amount)).withEvents
    (transferSourceState current.state ctx.sender recipient amount)
    [.transfer ctx.sender recipient amount]

def transferSourceDone (current : Checkpoint) (ctx : Context)
    (recipient : Adr) (amount : B256) : RunResult :=
  { status := .success (encodeWords [1]),
    frame := transferSourceFrame current ctx recipient amount,
    remaining := .done, childReturns := [] }

theorem transferLP_accept {st : State} {ctx : Context} {owner recipient : Adr} {amount : B256}
    (nonstatic : ctx.isStatic = false) (cover : amount ≤ st.balanceOf owner)
    (nowrap : (Blanc.ledgerDebit st.balanceOf owner amount recipient).toNat + amount.toNat < 2 ^ 256) :
    st.transferLP ctx owner recipient amount =
      .ok (transferSourceState st owner recipient amount, [.transfer owner recipient amount]) := by
  rw [State.transferLP, ite_eq_left cover, nonstatic]
  rw [ite_eq_left nowrap]
  rfl

theorem transfer_startImmediate_done {current : Checkpoint} {ctx : Context}
    {recipient : Adr} {amount : B256}
    (value : ctx.value = 0) (nonstatic : ctx.isStatic = false)
    (cover : amount ≤ current.state.balanceOf ctx.sender)
    (nowrap : (Blanc.ledgerDebit current.state.balanceOf ctx.sender amount recipient).toNat + amount.toNat < 2 ^ 256) :
    startImmediate current ctx (.transfer recipient amount) =
      some (.finished (transferSourceFrame current ctx recipient amount) (encodeWords [1])) := by
  simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value), getterResult,
    transferLP_accept nonstatic cover nowrap, Frame.finishLP]
  rfl

theorem transfer_drive_done {current : Checkpoint} {ctx : Context}
    {recipient : Adr} {amount : B256}
    (value : ctx.value = 0) (nonstatic : ctx.isStatic = false)
    (cover : amount ≤ current.state.balanceOf ctx.sender)
    (nowrap : (Blanc.ledgerDebit current.state.balanceOf ctx.sender amount recipient).toNat + amount.toNat < 2 ^ 256) :
    drive 2 (startTyped current ctx (.transfer recipient amount)) .done =
      transferSourceDone current ctx recipient amount := by
  rw [startTyped, transfer_startImmediate_done value nonstatic cover nowrap]
  rfl

theorem transferSourceFrame_prefix (current : Checkpoint) (ctx : Context)
    (recipient : Adr) (amount : B256) :
    (transferSourceFrame current ctx recipient amount).context = ctx ∧
    (transferSourceFrame current ctx recipient amount).checkpoint = current ∧
    (transferSourceFrame current ctx recipient amount).current.logs =
      current.logs ++ [.owned (writerEntryOrigin ctx) (.transfer ctx.sender recipient amount)] ∧
    (transferSourceFrame current ctx recipient amount).current.updates = current.updates ∧
    (transferSourceFrame current ctx recipient amount).segment = 0 ∧
    (transferSourceFrame current ctx recipient amount).afterCall = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem transferPublicPost_facts {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} (mem : PtrMem 128 96 M) :
    (transferPublicPost sevm b R M G).output = encodeWords [1] ∧
    (transferPublicPost sevm b R M G).logs = b.logs ++
      [transferRawLog sevm.currentTarget sevm.caller (transferRecipient sevm) (transferAmount sevm)] ∧
    (transferPublicPost sevm b R M G).getStor sevm.currentTarget =
      ((b.getStor sevm.currentTarget).set (transferBalanceSlot sevm.caller)
        (transferDebitedWord sevm b)).set (transferBalanceSlot (transferRecipient sevm))
        (transferCreditWord sevm b + transferAmount sevm) ∧
    (∀ a, a ≠ sevm.currentTarget → (transferPublicPost sevm b R M G).getStor a = b.getStor a) ∧
    (transferPublicPost sevm b R M G).gasLeft = G := by
  unfold transferPublicPost
  have memory := transferCoreMemory_ptr (owner := sevm.caller)
    (recipient := transferRecipient sevm) (amount := transferAmount sevm) mem
  have facts := getterWordPost_facts
    (b := transferCoreBase sevm b sevm.caller (transferRecipient sevm) (transferAmount sevm))
    (R := R) (v := 1) (G := G) memory.wf
  refine ⟨?_, ?_, ?_, ?_, facts.2.2.2⟩
  · simpa only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil] using facts.1
  · have creditLogs (base : Devm) (owner recipient : Adr) (amount credited : B256) :
        (transferCreditBase sevm base owner recipient amount credited).logs = base.logs ++
          [transferRawLog sevm.currentTarget owner recipient amount] := by
      change (afterSstore sevm base (transferBalanceSlot recipient) credited).logs ++
        [transferRawLog sevm.currentTarget owner recipient amount] = _
      rw [afterSstore_logs]
    rw [facts.2.2.1]
    simp only [transferCoreBase, creditLogs, afterSload_logs, transferDebitBase, afterSstore_logs]
  · rw [facts.2.1 sevm.currentTarget]
    simp only [transferCoreBase, transferCreditBase, Devm.addLog_getStor,
      afterSstore_getStor_self, afterSload_getStor, transferDebitBase]
    rfl
  · intro a different
    rw [facts.2.1 a]
    simp only [transferCoreBase, transferCreditBase, Devm.addLog_getStor,
      afterSstore_getStor_ne _ _ _ _ _ different.symm, afterSload_getStor, transferDebitBase]

theorem WriterRep.transfer_public_post {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (transferTouched sevm.caller (transferRecipient sevm))) :
    WriterRep (WriterExtend K (transferTouched sevm.caller (transferRecipient sevm)))
      ((transferPublicPost sevm b [0xa9059cbb] getterInitMemory G).getStor sevm.currentTarget)
      (transferSourceState st sevm.caller (transferRecipient sevm) (transferAmount sevm)) := by
  have reads := transfer_source_reads rep fresh
  have facts := transferPublicPost_facts (sevm := sevm) (b := b)
    (R := [0xa9059cbb]) (G := G) getterInitMemory_ptr
  rw [facts.2.2.1]
  unfold transferDebitedWord
  rw [reads.1, reads.2]
  exact rep.transfer_store fresh

/-- Both selected balance stores preserve whole physical fixed-slot words, including upper bits. -/
theorem WriterRep.transfer_public_fixed {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (transferTouched sevm.caller (transferRecipient sevm))) :
    ∀ n, n ∈ writerFixedSlots →
      ((transferPublicPost sevm b [0xa9059cbb] getterInitMemory G).getStor sevm.currentTarget).get n =
        (b.getStor sevm.currentTarget).get n := by
  have extended := rep.extend fresh
  have ownerKey : WriterExtend K (transferTouched sevm.caller (transferRecipient sevm))
      (.balance sevm.caller) := .inr (List.mem_cons.mpr (.inl rfl))
  have recipientKey : WriterExtend K (transferTouched sevm.caller (transferRecipient sevm))
      (.balance (transferRecipient sevm)) :=
    .inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl)))
  have ownerOff := extended.apart (.balance sevm.caller) ownerKey
  have recipientOff := extended.apart (.balance (transferRecipient sevm)) recipientKey
  change transferBalanceSlot sevm.caller ∉ writerFixedSlots at ownerOff
  change transferBalanceSlot (transferRecipient sevm) ∉ writerFixedSlots at recipientOff
  have facts := transferPublicPost_facts (sevm := sevm) (b := b)
    (R := [0xa9059cbb]) (G := G) getterInitMemory_ptr
  intro n fixed
  rw [facts.2.2.1]
  rw [Stor.get_set_ne _ (k := transferBalanceSlot (transferRecipient sevm)) (a := n)
    (fun eq => recipientOff (eq.symm ▸ fixed))]
  exact Stor.get_set_ne _ (k := transferBalanceSlot sevm.caller) (a := n)
    (fun eq => ownerOff (eq.symm ▸ fixed)) _


theorem transfer_startImmediate_inv {current : Checkpoint} {ctx : Context}
    {recipient : Adr} {amount : B256} {sourceFrame : Frame} {returndata : Bytes}
    (accepted : startImmediate current ctx (.transfer recipient amount) =
      some (.finished sourceFrame returndata)) :
    ctx.value = 0 ∧ amount ≤ current.state.balanceOf ctx.sender ∧ ctx.isStatic = false ∧
      (Blanc.ledgerDebit current.state.balanceOf ctx.sender amount recipient).toNat + amount.toNat < 2 ^ 256 ∧
      sourceFrame = transferSourceFrame current ctx recipient amount ∧ returndata = encodeWords [1] := by
  have value : ctx.value = 0 := by
    by_contra paid
    simp only [startImmediate, ite_eq_left paid, Frame.fail, Option.some.injEq] at accepted
    cases accepted
  have cover : amount ≤ current.state.balanceOf ctx.sender := by
    by_contra uncovered
    simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value),
      getterResult, State.transferLP, ite_eq_right uncovered, Frame.finishLP,
      Frame.fail, Option.some.injEq] at accepted
    cases accepted
  have nonstatic : ctx.isStatic = false := by
    cases static : ctx.isStatic with
    | false => rfl
    | true =>
      simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value),
        getterResult, State.transferLP, ite_eq_left cover, static, ite_true, Frame.finishLP,
        Frame.fail, Option.some.injEq] at accepted
      cases accepted
  have nowrap : (Blanc.ledgerDebit current.state.balanceOf ctx.sender amount recipient).toNat +
      amount.toNat < 2 ^ 256 := by
    by_contra wrapped
    simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value),
      getterResult, State.transferLP, ite_eq_left cover, nonstatic,
      ite_eq_right wrapped, Frame.finishLP, Frame.fail, Option.some.injEq] at accepted
    cases accepted
  rw [transfer_startImmediate_done value nonstatic cover nowrap] at accepted
  have fields := SegmentResult.finished.inj (Option.some.inj accepted)
  exact ⟨value, cover, nonstatic, nowrap, fields.1.symm, fields.2.symm⟩


theorem transferSourceState_self (st : State) (owner : Adr) (amount : B256) :
    transferSourceState st owner owner amount = st := by
  have balances : Blanc.ledgerCredit (Blanc.ledgerDebit st.balanceOf owner amount) owner amount =
      st.balanceOf := by
    funext a
    by_cases same : a = owner
    · subst a
      rw [Blanc.ledgerCredit_self, Blanc.ledgerDebit_self, B256.sub_add_cancel]
    · rw [Blanc.ledgerCredit_ne amount same, Blanc.ledgerDebit_ne amount same]
  unfold transferSourceState
  rw [balances]

theorem transferSourceState_zero (st : State) (owner recipient : Adr) :
    transferSourceState st owner recipient 0 = st := by
  have debit : Blanc.ledgerDebit st.balanceOf owner 0 = st.balanceOf := by
    funext a
    by_cases same : a = owner
    · subst a
      rw [Blanc.ledgerDebit_self, B256.sub_zero]
    · exact Blanc.ledgerDebit_ne 0 same
  have credit : Blanc.ledgerCredit st.balanceOf recipient 0 = st.balanceOf := by
    funext a
    by_cases same : a = recipient
    · subst a
      rw [Blanc.ledgerCredit_self, B256.add_zero]
    · exact Blanc.ledgerCredit_ne 0 same
  unfold transferSourceState
  rw [debit, credit]

/-- Local source and physical facts; the history producer supplies the incoming checkpoint. -/
structure TransferSourceResult (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (sevm : Sevm) (b post : Devm) (residual : Nat) : Prop where
  rawPost : post = transferPublicPost sevm b [0xa9059cbb] getterInitMemory residual
  representation : WriterRep (WriterExtend K (transferTouched sevm.caller (transferRecipient sevm)))
    (post.getStor sevm.currentTarget)
    (transferSourceState current.state sevm.caller (transferRecipient sevm) (transferAmount sevm))
  accepted : startImmediate current (writerContext sevm invocation) (transferDecodedEntry sevm) =
    some (.finished (transferSourceFrame current (writerContext sevm invocation)
      (transferRecipient sevm) (transferAmount sevm)) (encodeWords [1]))
  done : drive 2 (startTyped current (writerContext sevm invocation) (transferDecodedEntry sevm)) .done =
    transferSourceDone current (writerContext sevm invocation) (transferRecipient sevm) (transferAmount sevm)
  context : (transferSourceFrame current (writerContext sevm invocation)
    (transferRecipient sevm) (transferAmount sevm)).context = writerContext sevm invocation
  checkpoint : (transferSourceFrame current (writerContext sevm invocation)
    (transferRecipient sevm) (transferAmount sevm)).checkpoint = current
  sourceLogs : (transferSourceFrame current (writerContext sevm invocation)
    (transferRecipient sevm) (transferAmount sevm)).current.logs = current.logs ++
      [.owned (writerEntryOrigin (writerContext sevm invocation))
        (.transfer sevm.caller (transferRecipient sevm) (transferAmount sevm))]
  updates : (transferSourceFrame current (writerContext sevm invocation)
    (transferRecipient sevm) (transferAmount sevm)).current.updates = current.updates
  sourceState : (transferSourceFrame current (writerContext sevm invocation)
    (transferRecipient sevm) (transferAmount sevm)).current.state =
      transferSourceState current.state sevm.caller (transferRecipient sevm) (transferAmount sevm)
  segment : (transferSourceFrame current (writerContext sevm invocation)
    (transferRecipient sevm) (transferAmount sevm)).segment = 0
  afterCall : (transferSourceFrame current (writerContext sevm invocation)
    (transferRecipient sevm) (transferAmount sevm)).afterCall = none
  output : post.output = encodeWords [1]
  logs : post.logs = b.logs ++ [transferRawLog sevm.currentTarget sevm.caller
    (transferRecipient sevm) (transferAmount sevm)]
  storage : post.getStor sevm.currentTarget =
    ((b.getStor sevm.currentTarget).set (transferBalanceSlot sevm.caller)
      (transferDebitedWord sevm b)).set (transferBalanceSlot (transferRecipient sevm))
      (transferCreditWord sevm b + transferAmount sevm)
  foreign : ∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a
  gas : post.gasLeft = residual
  fixed : ∀ n, n ∈ writerFixedSlots → (post.getStor sevm.currentTarget).get n =
    (b.getStor sevm.currentTarget).get n
  movement : Blanc.Transfer current.state.balanceOf sevm.caller (transferAmount sevm)
    (transferRecipient sevm)
    (transferSourceState current.state sevm.caller (transferRecipient sevm) (transferAmount sevm)).balanceOf
  self : transferRecipient sevm = sevm.caller →
    transferSourceState current.state sevm.caller (transferRecipient sevm) (transferAmount sevm) = current.state
  zero : transferAmount sevm = 0 →
    transferSourceState current.state sevm.caller (transferRecipient sevm) (transferAmount sevm) = current.state

theorem transfer_public_source_result {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (transferTouched sevm.caller (transferRecipient sevm)))
    (value : sevm.value = 0) (nonstatic : sevm.isStatic = false)
    (cover : transferAmount sevm ≤ transferSourceWord sevm b sevm.caller)
    (nowrap : transferCreditSafe sevm b) :
    TransferSourceResult K current invocation sevm b
      (transferPublicPost sevm b [0xa9059cbb] getterInitMemory G) G := by
  have reads := transfer_source_reads rep fresh
  have covered : transferAmount sevm ≤ current.state.balanceOf sevm.caller := by
    rwa [reads.1] at cover
  have safe : (Blanc.ledgerDebit current.state.balanceOf sevm.caller (transferAmount sevm)
      (transferRecipient sevm)).toNat + (transferAmount sevm).toNat < 2 ^ 256 := by
    unfold transferCreditSafe at nowrap
    rwa [reads.2] at nowrap
  have sourceFacts := transferSourceFrame_prefix current (writerContext sevm invocation)
    (transferRecipient sevm) (transferAmount sevm)
  have facts := transferPublicPost_facts (sevm := sevm) (b := b)
    (R := [0xa9059cbb]) (G := G) getterInitMemory_ptr
  refine {
    rawPost := rfl
    representation := rep.transfer_public_post fresh
    accepted := transfer_startImmediate_done value nonstatic covered safe
    done := transfer_drive_done value nonstatic covered safe
    context := sourceFacts.1
    checkpoint := sourceFacts.2.1
    sourceLogs := sourceFacts.2.2.1
    updates := sourceFacts.2.2.2.1
    sourceState := rfl
    segment := sourceFacts.2.2.2.2.1
    afterCall := sourceFacts.2.2.2.2.2
    output := facts.1
    logs := facts.2.1
    storage := facts.2.2.1
    foreign := facts.2.2.2.1
    gas := facts.2.2.2.2
    fixed := rep.transfer_public_fixed fresh
    movement := Blanc.ledgerDebit_credit_transfer covered
    self := ?_
    zero := ?_ }
  · intro same
    rw [same]
    exact transferSourceState_self _ _ _
  · intro zero
    rw [zero]
    exact transferSourceState_zero _ _ _


/-- Successful raw pc0 execution derives the existing handler's acceptance and finite result. -/
theorem transfer_bytecode_refines_source {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (transferTouched sevm.caller (transferRecipient sevm)))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 68 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      ∃ residual, TransferSourceResult K current invocation sevm b post residual := by
  obtain ⟨value, size, guard, cover, nonstatic, nowrap, residual, eq⟩ :=
    transfer_bytecode_refines_raw codeEq fork selector run
  refine ⟨value, (approve_word_guards_iff representable).mp ⟨size, guard⟩,
    nonstatic, residual, ?_⟩
  rw [eq]
  exact transfer_public_source_result rep fresh value nonstatic cover nowrap

/-- Actual handler acceptance yields the literal pc0 run with both incoming store sentries. -/
theorem transfer_source_bytecode_exact {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b : Devm} {G : Nat}
    {sourceFrame : Frame} {returndata : Bytes}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (transferTouched sevm.caller (transferRecipient sevm)))
    (representable : sevm.data.length < 2 ^ 256) (length : 68 ≤ sevm.data.length)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (debitSentry : gCallStipend < G + transferDebitCharge sevm b +
      transferRecipientCharge sevm b + transferCreditCharge sevm b + 2153)
    (creditSentry : gCallStipend < G + transferCreditCharge sevm b + 1913)
    (accepted : startImmediate current (writerContext sevm invocation) (transferDecodedEntry sevm) =
      some (.finished sourceFrame returndata)) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty
      (G + transferSourceCharge sevm b + transferDebitCharge sevm b +
        transferRecipientCharge sevm b + transferCreditCharge sevm b + 2740))
      (transferPublicPost sevm b [0xa9059cbb] getterInitMemory G) ∧
    Nonempty (Exec 0 sevm (St b [] Mem.empty
      (G + transferSourceCharge sevm b + transferDebitCharge sevm b +
        transferRecipientCharge sevm b + transferCreditCharge sevm b + 2740))
      (.ok (transferPublicPost sevm b [0xa9059cbb] getterInitMemory G))) ∧
    sourceFrame = transferSourceFrame current (writerContext sevm invocation)
      (transferRecipient sevm) (transferAmount sevm) ∧ returndata = encodeWords [1] ∧
    TransferSourceResult K current invocation sevm b
      (transferPublicPost sevm b [0xa9059cbb] getterInitMemory G) G := by
  obtain ⟨value, covered, nonstatic, safe, frameEq, dataEq⟩ := transfer_startImmediate_inv accepted
  obtain ⟨size, guard⟩ := (approve_word_guards_iff representable).mpr length
  have reads := transfer_source_reads rep fresh
  have cover : transferAmount sevm ≤ transferSourceWord sevm b sevm.caller := by
    rw [reads.1]
    exact covered
  have nowrap : transferCreditSafe sevm b := by
    unfold transferCreditSafe
    rw [reads.2]
    exact safe
  exact ⟨transfer_pc0_exact fork value size selector guard debitSentry creditSentry nonstatic cover nowrap,
    transfer_bytecode_live_raw codeEq fork value size selector guard debitSentry creditSentry nonstatic cover nowrap,
    frameEq, dataEq, transfer_public_source_result rep fresh value nonstatic cover nowrap⟩

/-- Finite coalition accounting consumes the logical movement, with sum boundedness kept external. -/
theorem TransferSourceResult.ledger_coalition {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {residual : Nat}
    (result : TransferSourceResult K current invocation sevm b post residual)
    (sumNof : Blanc.SumNof current.state.balanceOf) (coalition : Finset Adr) :
    Blanc.ledgerSumOn coalition
        (transferSourceState current.state sevm.caller (transferRecipient sevm) (transferAmount sevm)).balanceOf +
        (if sevm.caller ∈ coalition then (transferAmount sevm).toNat else 0) =
      Blanc.ledgerSumOn coalition current.state.balanceOf +
        (if transferRecipient sevm ∈ coalition then (transferAmount sevm).toNat else 0) := by
  exact Blanc.ledgerSumOn_transfer sumNof result.movement

end Blanc.Lift.UniswapV2Pair
