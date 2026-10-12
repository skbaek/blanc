import Blanc.ExecutionMessageEffects
import Blanc.ExecutionAccountingAdmission

namespace Blanc.Drip.RepinBridge
open Jaune

/-- Parent hoist debt: generic authorization nonce transport for the zero-entry bridge. -/
theorem setDelegationStep_nonce_ne_zero
    {auth : Auth} {msg msg' : Msg} {refund refund' : B256}
    (run : setDelegationStep auth msg refund = .ok ⟨msg', refund'⟩) (owner : Adr)
    (nonce : (msg.benv.state.get owner).nonce ≠ 0) :
    (msg'.benv.state.get owner).nonce ≠ 0 := by
  unfold setDelegationStep at run
  dsimp only at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, _⟩
    exact nonce
  · split at run
    · simp only [Except.ok.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, _⟩
      exact nonce
    · split at run
      · simp only [Except.ok.injEq, Prod.mk.injEq] at run
        rcases run with ⟨rfl, _⟩
        exact nonce
      · cases run
      · split at run
        · simp only [Except.ok.injEq, Prod.mk.injEq] at run
          rcases run with ⟨rfl, _⟩
          exact nonce
        · split at run
          · simp only [Except.ok.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            exact nonce
          · rename_i authority recovered acceptedCode nonceMatch
            simp only [Except.ok.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            by_cases equal : authority = owner
            · subst owner
              have matched : (msg.benv.state.get authority).nonce = auth.nonce := by
                simpa only [bne_iff_ne, not_not] using nonceMatch
              have nonwrap : auth.nonce + 1 ≠ 0 :=
                UInt64.add_one_ne_zero_of_ne_max ‹auth.nonce ≠ UInt64.max›
              dsimp only [Msg.incrNonce, Msg.setCode, Benv.incrNonce,
                Benv.clearStorageWritesIfEmpty]
              rw [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce,
                State.setCode, State.setAccount_get_self, Acct.clearIfEmpty_nonce]
              simpa only [matched] using nonwrap
            · dsimp only [Msg.incrNonce, Msg.setCode, Benv.incrNonce,
                Benv.clearStorageWritesIfEmpty]
              rw [State.incrNonce, State.setAccount_get_ne _ equal,
                State.setCode, State.setAccount_get_ne _ equal]
              exact nonce

theorem setDelegationLoop_nonce_ne_zero
    {auths : List Auth} {msg msg' : Msg} {refund refund' : B256}
    (run : setDelegationLoop auths msg refund = .ok ⟨msg', refund'⟩) (owner : Adr)
    (nonce : (msg.benv.state.get owner).nonce ≠ 0) :
    (msg'.benv.state.get owner).nonce ≠ 0 := by
  induction auths generalizing msg refund with
  | nil =>
      unfold setDelegationLoop at run
      cases run
      exact nonce
  | cons auth auths ih =>
      unfold setDelegationLoop at run
      cases step : setDelegationStep auth msg refund with
      | error error => simp only [step, bind, Except.bind] at run; cases run
      | ok pair =>
          rcases pair with ⟨next, nextRefund⟩
          simp only [step, bind, Except.bind] at run
          exact ih run (setDelegationStep_nonce_ne_zero step owner nonce)

theorem setDelegation_nonce_ne_zero
    {msg msg' : Msg} {refund' : B256}
    (run : setDelegation msg = .ok ⟨msg', refund'⟩) (owner : Adr)
    (nonce : (msg.benv.state.get owner).nonce ≠ 0) :
    (msg'.benv.state.get owner).nonce ≠ 0 := by
  unfold setDelegation at run
  cases loop : setDelegationLoop msg.tenv.stat.auths msg 0 with
  | error error => simp only [loop, bind, Except.bind] at run; cases run
  | ok pair =>
      rcases pair with ⟨next, nextRefund⟩
      have inherited := setDelegationLoop_nonce_ne_zero loop owner nonce
      simp only [loop, bind, Except.bind] at run
      split at run
      · cases run
      · cases run
        exact inherited

theorem messageCallDelegation_nonce_ne_zero
    {msg delegated : Msg} {refund : Nat}
    (run : ExecutionTrace.messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (owner : Adr) (nonce : (msg.benv.state.get owner).nonce ≠ 0) :
    (delegated.benv.state.get owner).nonce ≠ 0 := by
  unfold ExecutionTrace.messageCallDelegation at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    exact nonce
  · rcases Except.bind_eq_ok run with
      ⟨⟨delegated', refundWord⟩, delegatedRun, rest⟩
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, rfl⟩
    exact setDelegation_nonce_ne_zero delegatedRun owner nonce

open Std.DTreeMap.Internal in
/-- Exact representation identity, rather than extensional tree equivalence. -/
theorem insert_same_raw {α β : Type} [Ord α] [Std.LawfulEqOrd α]
    (tree : Impl α (fun _ => β)) (balanced : tree.Balanced) (key : α) (value : β)
    (found : Impl.Const.get? tree key = some value) :
    (Impl.insert key value tree balanced).impl = tree := by
  induction tree with
  | leaf => simp only [Impl.Const.get?] at found; cases found
  | inner size k v left right ihLeft ihRight =>
      cases compared : compare key k with
      | lt =>
          simp only [Impl.Const.get?, compared] at found
          simp only [Impl.insert, compared]
          simp only [ihLeft balanced.left found, Impl.balanceL_eq_balance,
            Impl.balance_eq_inner balanced]
      | gt =>
          simp only [Impl.Const.get?, compared] at found
          simp only [Impl.insert, compared]
          simp only [ihRight balanced.right found, Impl.balanceR_eq_balance,
            Impl.balance_eq_inner balanced]
      | eq =>
          have same : key = k := Std.LawfulEqOrd.eq_of_compare compared
          subst k
          simp only [Impl.Const.get?, compared, Option.some.injEq] at found
          subst value
          simp only [Impl.insert, compared]

theorem treeMap_insert_same {α β : Type} [Ord α] [Std.LawfulEqOrd α]
    (tree : Std.TreeMap α β) (key : α) (value : β)
    (found : tree[key]? = some value) : tree.insert key value = tree := by
  cases tree with
  | mk inner =>
      cases inner with
      | mk raw wf =>
          change Std.DTreeMap.Internal.Impl.Const.get? raw key = some value at found
          simp only [Std.TreeMap.insert, Std.DTreeMap.insert,
            insert_same_raw raw wf.balanced key value found]

theorem setBal_current_of_protected {state : State} {owner : Adr}
    (hp : State.Protected state owner) :
    state.setBal owner (state.bal owner) = state := by
  have notEmpty : ¬ (state.get owner).Empty := by
    intro empty
    rcases hp with nonce | code
    · exact nonce empty.2.1
    · exact code empty.1
  have notNil : state.get owner ≠ Acct.nil := by
    intro nil
    apply notEmpty
    rw [nil]
    exact ⟨rfl, rfl, rfl⟩
  have found : state[owner]? = some (state.get owner) := by
    cases lookup : state[owner]? with
    | none =>
        have nil : state.get owner = Acct.nil := by
          rw [State.get_eq_getD, lookup]
          rfl
        exact (notNil nil).elim
    | some account =>
        rw [State.get_eq_getD, lookup]
        rfl
  have unchanged : (state.get owner).withBal (state.bal owner) = state.get owner := by
    unfold State.bal
    cases state.get owner
    rfl
  unfold State.setBal
  rw [unchanged]
  unfold State.setAccount
  rw [Acct.clearIfEmpty, if_neg notEmpty]
  unfold State.set
  rw [if_neg notNil]
  exact treeMap_insert_same state owner (state.get owner) found

theorem addBal_zero_of_protected {state : State} {owner : Adr}
    (hp : State.Protected state owner) : state.addBal owner 0 = state := by
  unfold State.addBal
  rw [B256.add_zero]
  exact setBal_current_of_protected hp

theorem subBal_zero_of_protected {state : State} {owner : Adr}
    (hp : State.Protected state owner) : state.subBal owner 0 = some state := by
  unfold State.subBal
  simp only [B256.lt_iff_toNat_lt_toNat, B256.toNat_zero, Nat.not_lt_zero, if_false, B256.sub_zero,
    setBal_current_of_protected hp]

theorem transaction_msg_caller_nonce_ne_zero
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : ExecutionTrace.TransactionTrace benv bout tx index state bout') :
    (trace.msg.benv.state.get trace.msg.caller).nonce ≠ 0 := by
  rw [trace.msg_caller, prepareMessage_benv trace.prepared]
  change (trace.debitState.get trace.sender).nonce ≠ 0
  rcases State.of_subBal trace.debit with ⟨_, debitEq⟩
  rw [debitEq, State.setBal_get_nonce]
  have nonceEq := ExecutionTrace.checkTransaction_sender_nonce trace.checked
  have nonceBound : (benv.state.get trace.sender).nonce ≠ UInt64.max := by
    simpa only [Benv.beginTransaction] using
      (nonceEq.trans_ne (ExecutionTrace.validateTransaction_nonce_ne_max trace.validation))
  have nonzero := UInt64.add_one_ne_zero_of_ne_max nonceBound
  simpa only [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce] using nonzero

theorem messageCallExecutionMessage_state (msg : Msg) :
    (ExecutionTrace.messageCallExecutionMessage msg).benv.state = msg.benv.state := by
  unfold ExecutionTrace.messageCallExecutionMessage
  split <;> rfl

/-- Parent hoist debt: project before unfolding a concrete write tower. -/
theorem setStorVal_createdAccounts (machine : Devm) (address : Adr) (key value : B256) :
    (machine.setStorVal address key value).createdAccounts = machine.createdAccounts := rfl

theorem withRefundCounter_createdAccounts (machine : Devm) (refund : Int) :
    (machine.withRefundCounter refund).createdAccounts = machine.createdAccounts := rfl

end Blanc.Drip.RepinBridge
