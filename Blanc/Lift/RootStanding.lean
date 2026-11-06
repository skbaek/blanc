import Blanc.Lift.RootReady
import Blanc.ExecutionSettledRootEntry
import Blanc.ExecutionRetainedDeletionSafety
import Blanc.ExecutionNoDelProducer

/-!
# A cell naming accounts that stand: a state-level invariant through a mid history

`MidHistoryTraceIn.outputNotDeleted_of_cell` carries a property of one cell, so a root law cannot read at a root's
entry that the account the cell names holds its code. `MidHistoryTraceIn.live_of_roots` carries that too: code at `wa`,
and a list of accounts witnessing the cell's word, each standing. A root may move the word to a list standing at its
entry; each account's own law keeps it out of the deletion set.

An account's code seen at a root's entry was there when its transaction began (`*.code_back`): authorizations write
only empty or delegation code.
-/

namespace Blanc.ExecutionTrace

open Jaune Blanc

/-! ## Code at a root's entry was there before it -/

/-- The code an authorization writes is a delegation. -/
theorem delegationCode_valid (t : Adr) : isValidDelegation (eoaDelegationMarker ++ t.toBytes).toByteArray :=
  of_decide_eq_true rfl

/-- Code neither empty nor a delegation after one authorization was there before it. -/
theorem setDelegationStep_code_back {a : Adr} {auth : Auth} {msg msg' : Msg} {refund refund' : B256}
    (run : setDelegationStep auth msg refund = .ok ⟨msg', refund'⟩)
    (ne : (msg'.benv.state.getCode a).toList ≠ []) (del : ¬ isValidDelegation (msg'.benv.state.getCode a)) :
    msg.benv.state.getCode a = msg'.benv.state.getCode a := by
  unfold setDelegationStep at run
  dsimp only at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, _⟩
    rfl
  · split at run
    · simp only [Except.ok.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, _⟩
      rfl
    · split at run
      · simp only [Except.ok.injEq, Prod.mk.injEq] at run
        rcases run with ⟨rfl, _⟩
        rfl
      · cases run
      · rename_i authority heqAuth
        split at run
        · simp only [Except.ok.injEq, Prod.mk.injEq] at run
          rcases run with ⟨rfl, _⟩
          rfl
        · split at run
          · simp only [Except.ok.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            rfl
          · simp only [Except.ok.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            by_cases same : authority = a
            · subst same
              have after : ∀ c : ByteArray, (((msg.benv.state.setCode authority c).incrNonce authority).get
                  authority).code = c := fun c => by
                rw [State.incrNonce_get_code]
                simp only [State.setCode, State.setAccount_get_self, Acct.clearIfEmpty_code]
              change ((((msg.benv.state.setCode authority _).incrNonce authority).get authority).code).toList ≠ [] at ne
              change ¬ isValidDelegation (((msg.benv.state.setCode authority _).incrNonce authority).get
                authority).code at del
              rw [after] at ne del
              split at ne
              · exact (ne ByteArray.toList_empty).elim
              · rename_i nonzero
                simp only [nonzero, ↓reduceIte] at del
                exact (del (delegationCode_valid _)).elim
            · show (msg.benv.state.get a).code = (((msg.benv.state.setCode authority
                (if auth.address = 0 then ByteArray.empty
                  else (eoaDelegationMarker ++ auth.address.toBytes).toByteArray)).incrNonce
                authority).get a).code
              rw [State.incrNonce_get_code, State.setCode_get_code_ne same]

theorem setDelegationLoop_code_back {a : Adr} {auths : List Auth} {msg msg' : Msg} {refund refund' : B256}
    (run : setDelegationLoop auths msg refund = .ok ⟨msg', refund'⟩)
    (ne : (msg'.benv.state.getCode a).toList ≠ []) (del : ¬ isValidDelegation (msg'.benv.state.getCode a)) :
    msg.benv.state.getCode a = msg'.benv.state.getCode a := by
  induction auths generalizing msg refund with
  | nil =>
      unfold setDelegationLoop at run
      simp only [Except.ok.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, _⟩
      rfl
  | cons auth auths ih =>
      unfold setDelegationLoop at run
      simp only [bind, Except.bind] at run
      split at run
      · cases run
      · rename_i pair step
        obtain ⟨stepMsg, stepRefund⟩ := pair
        have later := ih run
        exact (setDelegationStep_code_back step (by rw [later]; exact ne) (by rw [later]; exact del)).trans later

theorem messageCallDelegation_code_back {a : Adr} {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (ne : (delegated.benv.state.getCode a).toList ≠ [])
    (del : ¬ isValidDelegation (delegated.benv.state.getCode a)) :
    msg.benv.state.getCode a = delegated.benv.state.getCode a := by
  unfold messageCallDelegation processMessageCall.legacyAuthorization at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    rfl
  · rcases Except.bind_eq_ok run with ⟨⟨middle, refundWord⟩, hdel, rest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, rfl⟩
    unfold setDelegation at hdel
    rcases Except.bind_eq_ok hdel with ⟨⟨loopMsg, loopRefund⟩, loop, rest⟩
    cases codeAddress : loopMsg.codeAddress with
    | none => simp only [codeAddress, Except.bind_error, reduceCtorEq] at rest
    | some address =>
        simp only [codeAddress, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at rest
        rcases rest with ⟨rfl, rfl⟩
        exact setDelegationLoop_code_back (msg' := loopMsg) loop ne del

theorem RetainedXlot.settledRoots_entry_getCode {slot : Xlot} (retained : RetainedXlot slot)
    {frame : Frame} {out : Except (EvmError × State × AdrSet × Tra) Devm} (process : RunFrame frame slot out)
    (a : Adr) : ∀ R ∈ retained.settledRoots, R.pre.getCode a = frame.inner.benv.state.getCode a := by
  cases retained with
  | none => intro R member; cases member
  | some run =>
    intro R member
    simp only [RetainedXlot.settledRoots] at member
    split at member
    · rw [List.mem_singleton] at member
      subst R
      exact Frame.enter_run_getCode (RunFrame.some_inv process).1 a
    · cases member

theorem ProcessMessageTrace.settledRoots_entry_getCode {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} (trace : ProcessMessageTrace msg out) (a : Adr) :
    ∀ R ∈ trace.settledRoots, R.pre.getCode a = msg.benv.state.getCode a := by
  rcases trace with ⟨slot, retained, process⟩
  have entry := RetainedXlot.settledRoots_entry_getCode retained process a
  cases retained with
  | none => intro R member; cases member
  | some run =>
    intro R member
    simp only [ProcessMessageTrace.settledRoots] at member
    split at member
    · exact entry R member
    · cases member

theorem ProcessCreateMessageTrace.settledRoots_entry_getCode {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} (trace : ProcessCreateMessageTrace msg out) (a : Adr) :
    ∀ R ∈ trace.settledRoots, R.pre.getCode a = msg.benv.state.getCode a := by
  rcases trace with ⟨slot, retained, process⟩
  have entry := RetainedXlot.settledRoots_entry_getCode retained process a
  cases retained with
  | none => intro R member; cases member
  | some run =>
    intro R member
    simp only [ProcessCreateMessageTrace.settledRoots] at member
    split at member
    · exact (entry R member).trans (processCreateMessage.msg_getCode msg a)
    · cases member

theorem MessageCallTrace.code_back {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) {a : Adr} {C : ByteArray} (ne : C.toList ≠ [])
    (del : ¬ isValidDelegation C) :
    ∀ R ∈ trace.settledRoots, R.pre.getCode a = C → msg.benv.state.getCode a = C := by
  cases trace with
  | createCollision => intro R member; cases member
  | createRun target collision evm core retained result =>
    exact fun R member code => (ProcessCreateMessageTrace.settledRoots_entry_getCode retained a R member).symm.trans code
  | callRun target delegated refund delegation execMsg execution evm core retained result =>
    intro R member code
    have atExec := (ProcessMessageTrace.settledRoots_entry_getCode retained a R member).symm.trans code
    rw [execution, messageCallExecutionMessage_getCode] at atExec
    rw [messageCallDelegation_code_back delegation (by rw [atExec]; exact ne) (by rw [atExec]; exact del)]
    exact atExec

theorem TransactionTrace.code_back {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State}
    {bout' : BlockOutput} (trace : TransactionTrace benv bout tx index state bout') {a : Adr} {C : ByteArray}
    (ne : C.toList ≠ []) (del : ¬ isValidDelegation C) :
    ∀ R ∈ trace.settledRoots, R.pre.getCode a = C → benv.state.getCode a = C := fun R member code => by
  have atMsg := trace.message.code_back ne del R member code
  rw [prepareMessage_benv trace.prepared] at atMsg
  have debitCode : trace.debitState.getCode a = benv.state.getCode a := by
    rw [State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  exact debitCode.symm.trans atMsg

end Blanc.ExecutionTrace

namespace Blanc.Lift

open Jaune Blanc Blanc.ExecutionTrace ContractSpecSem

/-! ## The invariant -/

/-- An account's code, with the certified semantics a root's entry reads it by. -/
structure StandingCode where
  adr : Adr
  code : ByteArray
  sem : CodeSem
  image : sem.image = some code.toList

theorem StandingCode.ne (p : StandingCode) : p.code.toList ≠ [] := p.sem.ne_nil p.image

theorem StandingCode.del (p : StandingCode) : ¬ isValidDelegation p.code := p.sem.not_delegation p.image.symm

/-- Every listed account holds its code. -/
def Stands (l : List StandingCode) (w : State) : Prop := ∀ p ∈ l, w.getCode p.adr = p.code

/-- `wa` holds `C`, and its cell's word has a witness list that stands. -/
def StateLive (wa : Adr) (C : ByteArray) (k : B256) (W : B256 → List StandingCode → Prop) (w : State) : Prop :=
  w.getCode wa = C ∧ ∃ l, W ((w.getStor wa).get k) l ∧ Stands l w

/-- A root's law: reading a standing witness at its entry, it keeps `wa` out of the deletion set and leaves a word whose
witness list stood at its entry. -/
def RootStep (F : Fork → Prop) (wa : Adr) (sem : CodeSem) (k : B256) (W : B256 → List StandingCode → Prop)
    (R : Exec.Frame) : Prop :=
  RootReady F wa sem (fun _ _ => True) R → ∀ l, W ((R.pre.getStor wa).get k) l → Stands l R.pre.state →
    (Devm.NoDel wa R.pre → Devm.NoDel wa R.post) ∧ ∃ l', W ((R.post.getStor wa).get k) l' ∧ Stands l' R.pre.state

/-- Each witness list's own law: no root that finds the list standing deletes one of its accounts. -/
def WitnessStays (F : Fork → Prop) (W : B256 → List StandingCode → Prop) : Prop :=
  ∀ (R : Exec.Frame) (v : B256) (l : List StandingCode), W v l → Stands l R.pre.state → ∀ p ∈ l,
    RootReady F p.adr p.sem (fun _ _ => True) R → Devm.NoDel p.adr R.pre → Devm.NoDel p.adr R.post

section Levels

variable {F : Fork → Prop} {wa : Adr} {sem : CodeSem} {C : ByteArray} {k : B256}
  {W : B256 → List StandingCode → Prop}

local notation "Live" => StateLive wa C k W
local notation "Step" => RootStep F wa sem k W

theorem StateLive.map {w w' : State} (code : ∀ a D, w.getCode a = D → D.toList ≠ [] → w'.getCode a = D)
    (cell : w.getCode wa = C → (w'.getStor wa).get k = (w.getStor wa).get k) (ne : C.toList ≠ [])
    (h : Live w) : Live w' := by
  obtain ⟨hC, l, hW, hS⟩ := h
  exact ⟨code _ _ hC ne, l, by rw [cell hC]; exact hW, fun p hp => code _ _ (hS p hp) p.ne⟩

theorem StateLive.roots {w : State} {rs : List Exec.Frame}
    (entry : ∀ a D, w.getCode a = D → D.toList ≠ [] → ¬ isValidDelegation D → ∀ R ∈ rs,
      R.pre.getCode a = D ∧ (R.pre.getStor a).get k = (w.getStor a).get k)
    (ne : C.toList ≠ []) (del : ¬ isValidDelegation C) (h : Live w) : ∀ R ∈ rs, Live R.pre.state := by
  obtain ⟨hC, l, hW, hS⟩ := h
  intro R member
  have here := entry wa C hC ne del R member
  refine ⟨here.1, l, ?_, fun p hp => (entry p.adr p.code (hS p hp) p.ne p.del R member).1⟩
  change W ((R.pre.getStor wa).get k) l
  rw [here.2]
  exact hW

/-- A stage's exit from the facts at its roots. -/
theorem StateLive.exit {w w' : State} {rs : List Exec.Frame}
    (step : ∀ R ∈ rs, ∃ l', W ((R.post.getStor wa).get k) l' ∧ Stands l' R.pre.state)
    (back : ∀ R ∈ rs, ∀ p : StandingCode, R.pre.getCode p.adr = p.code → w.getCode p.adr = p.code)
    (carry : ∀ v l, W v l → Stands l w → Stands l w')
    (cell : ∀ Q : B256 → Prop, (∀ R ∈ rs, Q ((R.pre.getStor wa).get k) → Q ((R.post.getStor wa).get k)) →
      Q ((w.getStor wa).get k) → Q ((w'.getStor wa).get k) ∧ w'.getCode wa = C)
    (h : Live w) : Live w' := by
  obtain ⟨-, l, hW, hS⟩ := h
  have result := cell (fun v => ∃ l, W v l ∧ Stands l w') (fun R member _ => ?_) ⟨l, hW, carry _ l hW hS⟩
  · obtain ⟨cellPost, code⟩ := result
    exact ⟨code, cellPost⟩
  · obtain ⟨l', hW', hS'⟩ := step R member
    exact ⟨l', hW', carry _ l' hW' fun p hp => back R member p (hS' p hp)⟩

theorem transaction_live {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State}
    {bout' : BlockOutput} (trace : TransactionTrace benv bout tx index state bout')
    (image : sem.image = some C.toList) (hsg : benv.stat.rules.stateGas = none)
    (ne : C.toList ≠ []) (del : ¬ isValidDelegation C) (notCreated : ∀ a, a ∉ benv.createdAccounts)
    (hF : F benv.stat.fork) (sumNof : sum benv.state.bal < 2 ^ 256)
    (law : ∀ R ∈ trace.settledRoots, Step R) (stays : WitnessStays F W) (h : Live benv.state) :
    wa ∉ trace.messageOut.accountsToDelete ∧ Live state ∧ ∀ R ∈ trace.settledRoots, Live R.pre.state := by
  have entry : ∀ a D, benv.state.getCode a = D → D.toList ≠ [] → ¬ isValidDelegation D → ∀ R ∈ trace.settledRoots,
      R.pre.getCode a = D ∧ (R.pre.getStor a).get k = (benv.state.getStor a).get k :=
    fun a D hD neD delD => trace.settledRoots_entry_code_cell hD neD delD k
  have roots := StateLive.roots (W := W) entry ne del h
  have facts : ∀ R ∈ trace.settledRoots, (Devm.NoDel wa R.pre → Devm.NoDel wa R.post) ∧
      ∃ l', W ((R.post.getStor wa).get k) l' ∧ Stands l' R.pre.state := fun R member => by
    obtain ⟨-, l, hW, hS⟩ := roots R member
    exact law R member (transaction_rootsReady (P := fun _ => True) trace image h.1 (notCreated wa) hF sumNof
      trivial R member).1 l hW hS
  have nd := trace.noDel_of_settledRoots del ne hsg h.1 (notCreated wa) fun R member => (facts R member).1
  have carry : ∀ v l, W v l → Stands l benv.state → Stands l state := fun v l hW hS p hp =>
    (trace.noDel_of_settledRoots p.del p.ne hsg (hS p hp) (notCreated _) fun R member =>
      stays R v l hW (fun q hq => (entry q.adr q.code (hS q hq) q.ne q.del R member).1) p hp
        (transaction_rootsReady (P := fun _ => True) trace p.image (hS p hp) (notCreated _) hF sumNof
          trivial R member).1).2.2
  exact ⟨nd.1, StateLive.exit (fun R member => (facts R member).2)
    (fun R member p => trace.code_back p.ne p.del R member) carry
    (fun Q roots initial => trace.cell_property_of_settledRoots k hsg h.1 ne del nd.1 Q roots initial) h, roots⟩

theorem applyTransactions_live {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (image : sem.image = some C.toList)
    (hsg : benv.stat.rules.stateGas = none) (ne : C.toList ≠ []) (del : ¬ isValidDelegation C)
    (notCreated : ∀ a, a ∉ benv.createdAccounts) (hF : F benv.stat.fork) (sumNof : sum benv.state.bal < 2 ^ 256)
    (law : ∀ R ∈ trace.settledRoots, Step R) (stays : WitnessStays F W) (h : Live benv.state) :
    trace.OutputNotDeleted wa ∧ Live finalBenv.state ∧ ∀ R ∈ trace.settledRoots, Live R.pre.state := by
  induction trace with
  | nil => exact ⟨trivial, h, fun _ member => absurd member List.not_mem_nil⟩
  | cons head tail ih =>
      obtain ⟨nd, live, roots⟩ := transaction_live head image hsg ne del notCreated hF sumNof
        (fun R member => law R (List.mem_append_left _ member)) stays h
      obtain ⟨later, final, rootsLater⟩ := ih hsg notCreated hF
        (Nat.lt_of_le_of_lt (by simpa only [Benv.withState] using processTransaction_sum_le head.result hsg) sumNof)
        (fun R member => law R (List.mem_append_right _ member)) live
      exact ⟨⟨nd, later⟩, final, fun R member => (List.mem_append.mp member).elim (roots R) (rootsLater R)⟩

theorem systemMessage_live {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) (image : sem.image = some C.toList)
    (hsg : benv.stat.rules.stateGas = none) (ne : C.toList ≠ []) (del : ¬ isValidDelegation C)
    (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork) (sumNof : sum benv.state.bal < 2 ^ 256)
    (law : ∀ R ∈ trace.settledRoots, Step R) (h : Live benv.state) :
    Live state ∧ ∀ R ∈ trace.settledRoots, Live R.pre.state := by
  have roots := StateLive.roots (W := W) (rs := trace.settledRoots) (w := benv.state)
    (fun a D hD neD delD => trace.message.settledRoots_entry_code_cell hD neD delD k) ne del h
  refine ⟨StateLive.exit (fun R member => ?_) (fun R member p => trace.message.code_back p.ne p.del R member)
    (fun _ _ _ hS p hp => (trace.cell_property_of_settledRoots 0 hsg (hS p hp) p.ne p.del (fun _ => True)
      (fun _ _ _ => trivial) trivial).2)
    (fun Q roots initial => trace.cell_property_of_settledRoots k hsg h.1 ne del Q roots initial) h, roots⟩
  obtain ⟨-, l, hW, hS⟩ := roots R member
  exact (law R member (systemMessage_rootsReady (P := fun _ => True) trace image h.1 notCreated hF sumNof
    trivial R member).1 l hW hS).2

theorem beacon_live {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) (image : sem.image = some C.toList)
    (hsg : benv.stat.rules.stateGas = none) (ne : C.toList ≠ []) (del : ¬ isValidDelegation C)
    (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork) (sumNof : sum benv.state.bal < 2 ^ 256)
    (law : ∀ R ∈ trace.settledRoots, Step R) (h : Live benv.state) :
    Live state ∧ ∀ R ∈ trace.settledRoots, Live R.pre.state := by
  cases trace with
  | skipped => exact ⟨h, fun _ member => absurd member List.not_mem_nil⟩
  | called _ _ message _ _ => exact systemMessage_live message image hsg ne del notCreated hF sumNof law h

theorem history_live {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) (image : sem.image = some C.toList)
    (hsg : benv.stat.rules.stateGas = none) (ne : C.toList ≠ []) (del : ¬ isValidDelegation C)
    (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork) (sumNof : sum benv.state.bal < 2 ^ 256)
    (law : ∀ R ∈ trace.settledRoots, Step R) (h : Live benv.state) :
    Live state ∧ ∀ R ∈ trace.settledRoots, Live R.pre.state := by
  cases trace with
  | skipped => exact ⟨h, fun _ member => absurd member List.not_mem_nil⟩
  | called _ _ _ _ message _ _ => exact systemMessage_live message image hsg ne del notCreated hF sumNof law h

theorem requestStage_live {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} (trace : RequestStageTrace rules benv bout state bout')
    (image : sem.image = some C.toList) (hsg : benv.stat.rules.stateGas = none) (ne : C.toList ≠ [])
    (del : ¬ isValidDelegation C) (notCreated : wa ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (sumNof : sum benv.state.bal < 2 ^ 256) (law : ∀ R ∈ trace.settledRoots, Step R) (h : Live benv.state) :
    Live state ∧ ∀ R ∈ trace.settledRoots, Live R.pre.state := by
  cases trace with
  | skipped => exact ⟨h, fun _ member => absurd member List.not_mem_nil⟩
  | called _ message _ =>
      obtain ⟨first, firstRoots⟩ := systemMessage_live message.withdrawal image hsg ne del notCreated hF sumNof
        (fun R member => law R (List.mem_append_left _ member)) h
      obtain ⟨last, lastRoots⟩ := systemMessage_live message.consolidation image hsg ne del notCreated hF
        (Nat.lt_of_le_of_lt (message.withdrawal.sum_le_noStateGas hsg) sumNof)
        (fun R member => law R (List.mem_append_right _ member)) first
      exact ⟨by rw [message.state_eq_consolidationState]; exact last, fun R member => (List.mem_append.mp member).elim (firstRoots R) (lastRoots R)⟩

/-- Withdrawals, the request stage and rewards. -/
theorem afterTransactions_live {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (image : sem.image = some C.toList)
    (hsg : benv.stat.rules.stateGas = none) (ne : C.toList ≠ []) (del : ¬ isValidDelegation C)
    (notCreated : wa ∉ trace.transactionBenv.createdAccounts) (hF : F benv.stat.fork)
    (txBound : sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256)
    (law : ∀ R ∈ trace.requests.settledRoots, Step R) (h : Live trace.transactionBenv.state) :
    Live state ∧ ∀ R ∈ trace.requests.settledRoots, Live R.pre.state := by
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have withdrawn : Live trace.withdrawalState :=
    StateLive.map (fun _ _ hD _ => trace.withdrawalCode_of_code hD)
      (fun hC => trace.withdrawalCell_of_code hC ne k) ne h
  obtain ⟨requested, roots⟩ := requestStage_live trace.requests image
    (by change trace.transactionBenv.stat.rules.stateGas = none; rw [txStat]; exact hsg) ne del notCreated
    (by change F trace.transactionBenv.stat.fork; rw [txStat]; exact hF)
    (Nat.lt_of_le_of_lt (StagedBodyTrace.withdrawal_sum_le trace txBound) txBound) law withdrawn
  refine ⟨?_, roots⟩
  rw [trace.finalState_eq, trace.rewardState_eq]
  split
  · exact requested
  · exact StateLive.map (fun _ _ hD _ => (payRewards_getCode ..).trans hD)
      (fun hC => payRewards_getStor _ _ _ _ _ (by rw [hC]; exact ne) ▸ rfl) ne requested

theorem stagedBody_live {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (image : sem.image = some C.toList)
    (hsg : benv.stat.rules.stateGas = none) (ne : C.toList ≠ []) (del : ¬ isValidDelegation C)
    (notCreated : ∀ a, a ∉ benv.createdAccounts) (hF : F benv.stat.fork)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256) (law : ∀ R ∈ trace.settledRoots, Step R)
    (stays : WitnessStays F W) (h : Live benv.state) :
    trace.transactions.OutputNotDeleted wa ∧ Live state ∧ ∀ R ∈ trace.settledRoots, Live R.pre.state := by
  have beaconLe : sum trace.beaconState.bal ≤ sum benv.state.bal := trace.beacon.sum_le_noStateGas hsg
  have historyLe : sum trace.historyState.bal ≤ sum trace.beaconState.bal :=
    trace.history.sum_le_noStateGas (by simpa only [Benv.withState] using hsg)
  have txLe : sum trace.transactionBenv.state.bal ≤ sum trace.historyState.bal :=
    trace.transactions.sum_le_noStateGas (by simpa only [Benv.withState] using hsg)
  obtain ⟨beaconLive, beaconRoots⟩ := beacon_live trace.beacon image hsg ne del (notCreated wa) hF (by omega)
    (fun R member => law R (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))) h
  obtain ⟨historyLive, historyRoots⟩ := history_live trace.history image hsg ne del (notCreated wa) hF
    (by change sum trace.beaconState.bal < _; omega)
    (fun R member => law R (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member))))
    beaconLive
  obtain ⟨nd, txLive, txRoots⟩ := applyTransactions_live trace.transactions image hsg ne del notCreated hF
    (by change sum trace.historyState.bal < _; omega)
    (fun R member => law R (List.mem_append_left _ (List.mem_append_right _ member))) stays historyLive
  obtain ⟨final, requestRoots⟩ := afterTransactions_live trace image hsg ne del
    (by rw [trace.transactions.createdAccounts_eq]; exact notCreated wa) hF (by omega)
    (fun R member => law R (List.mem_append_right _ member)) txLive
  refine ⟨nd, final, fun R member => ?_⟩
  simp only [StagedBodyTrace.settledRoots, List.mem_append] at member
  rcases member with ((here | here) | here) | here
  · exact beaconRoots R here
  · exact historyRoots R here
  · exact txRoots R here
  · exact requestRoots R here

end Levels

/-- **The state-level sibling of `outputNotDeleted_of_cell`.** From a start where `wa` holds `C` and its cell's word has
a standing witness: the deletion exclusions, and at every settled root's entry and at the end, the code and a standing
witness. Each root law reads its own witness at its entry, so there is no circle with `wa`'s own deletion. -/
theorem MidHistoryTraceIn.live_of_roots {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (history : MidHistoryTraceIn F cfg start future)
    (capabilities : BodyStageCapabilities F) {wa : Adr} {sem : CodeSem} {C : ByteArray}
    (image : sem.image = some C.toList) (ne : C.toList ≠ []) (del : ¬ isValidDelegation C) {k : B256}
    {W : B256 → List StandingCode → Prop} (law : ∀ R ∈ history.settledRoots, RootStep F wa sem k W R)
    (stays : WitnessStays F W) (h : StateLive wa C k W start.state) :
    history.OutputNotDeleted wa ∧ StateLive wa C k W future.state ∧
      ∀ R ∈ history.settledRoots, StateLive wa C k W R.pre.state := by
  induction history with
  | tail block cut =>
      have stat := block.txSplit_stat cut
      have afterF : F cut.afterBenv.stat.fork := by rw [stat]; exact block.forkIn
      have afterSg : cut.afterBenv.stat.rules.stateGas = none := by
        rw [stat]
        exact capabilities.stateGas_none block.forkIn
      have afterBound : sum cut.afterBenv.state.bal + wdsum block.block.wds < 2 ^ 256 :=
        block.txSplit_bound cut capabilities
      have notCreated := block.txSplit_notCreated cut
      obtain ⟨nd, live, roots⟩ := applyTransactions_live cut.after image afterSg ne del notCreated afterF
        (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) afterBound)
        (fun R member => law R (List.mem_append_left _ member)) stays h
      have txLe : sum block.bodyTrace.transactionBenv.state.bal ≤ sum cut.afterBenv.state.bal :=
        cut.after.sum_le_noStateGas afterSg
      obtain ⟨final, requestRoots⟩ := afterTransactions_live block.bodyTrace image
        (capabilities.stateGas_none block.forkIn) ne del
        (by rw [cut.after.createdAccounts_eq]; exact notCreated wa) block.forkIn (by omega)
        (fun R member => law R (List.mem_append_right _ member)) live
      rw [congrArg BlockChain.state block.postEq]
      exact ⟨nd, final, fun R member => (List.mem_append.mp member).elim (roots R) (requestRoots R)⟩
  | step prior block ih =>
      obtain ⟨nd, live, roots⟩ := ih (fun R member => law R (List.mem_append_left _ member)) h
      obtain ⟨blockNd, final, blockRoots⟩ := stagedBody_live block.bodyTrace image
        (capabilities.stateGas_none block.forkIn) ne del (fun _ => AdrSet.not_mem_empty) block.forkIn
        block.withdrawalsBound (fun R member => law R (List.mem_append_right _ member)) stays live
      rw [congrArg BlockChain.state block.postEq]
      exact ⟨⟨nd, blockNd⟩, final, fun R member => (List.mem_append.mp member).elim (roots R) (blockRoots R)⟩

/-! ## One account standing -/

section Stands

variable {F : Fork → Prop} (capabilities : BodyStageCapabilities F) {a : Adr} {sem : CodeSem} {C : ByteArray}

include capabilities in
/-- A root that finds code with the safety bundle keeps its account out of the deletion set. -/
theorem root_noDel_of_safety (K : InstalledRuntimeSafety C) (image : sem.image = some C.toList) {R : Exec.Frame}
    (ready : RootReady F a sem (fun _ _ => True) R) (initial : Devm.NoDel a R.pre) : Devm.NoDel a R.post := by
  obtain ⟨fork, at_, -, -, pcZero⟩ := ready
  rcases R with ⟨pc, sevm, pre, out, run, committed⟩
  dsimp only at fork at_ initial pcZero
  subst pcZero
  have hsg := capabilities.stateGas_none fork
  have result := Exec.inv_noDel_of_retained_terminal_safe run committed hsg
    (fun N retained => K.safe run hsg (bytes_eq_of_image (at_.1.trans image))
      (fun t => ⟨rfl, bytes_eq_of_image ((at_.2 t).1.trans image)⟩) N
      ((Exec.retainedNodes_sublist_rawNodes run).subset retained)) initial
  cases out with
  | error error => cases committed
  | ok post => exact result

variable {cfg : ChainConfig} {start : Benv} {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future)

include capabilities in
/-- Code standing at the start stands at every settled root, when no root that finds it deletes its account. -/
theorem stands_of_law (image : sem.image = some C.toList) (ne : C.toList ≠ []) (del : ¬ isValidDelegation C)
    (installed : start.state.getCode a = C)
    (law : ∀ R ∈ trace.settledRoots, RootReady F a sem (fun _ _ => True) R →
      Devm.NoDel a R.pre → Devm.NoDel a R.post) :
    ∀ R ∈ trace.settledRoots, R.pre.state.getCode a = C := fun R member =>
  bytes_eq_of_image (((MidHistoryTraceIn.rootsReady trace capabilities image installed ne del
    (MidHistoryTraceIn.outputNotDeleted_of_ready trace capabilities image installed ne del law).1 R member).2.1.1).trans
      image)

include capabilities in
/-- Code with the safety bundle, standing at the start, stands at every settled root. -/
theorem stands_of_safety (K : InstalledRuntimeSafety C) (image : sem.image = some C.toList)
    (installed : start.state.getCode a = C) : ∀ R ∈ trace.settledRoots, R.pre.state.getCode a = C :=
  stands_of_law capabilities trace image K.nonempty K.notDelegation installed
    fun _ _ ready => root_noDel_of_safety capabilities K image ready

end Stands

end Blanc.Lift
