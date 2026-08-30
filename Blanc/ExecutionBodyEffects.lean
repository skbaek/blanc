-- ExecutionBodyEffects.lean : contract-invariant block-body facts.

import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionBodyStateTrace

/-!
Contract-neutral block-body facts.

`Blanc/ExecutionMessageEffects.lean` and
`Blanc/ExecutionTransactionEffects.lean` say what one message and one whole
transaction do to an installed contract address `ca` carrying an *arbitrary*
`ContractSpec` invariant.  This module is the body level of the same seam: the
two pre-transaction system messages, the decoded transaction list, the direct
consensus withdrawals, and the two checked request messages.  Nothing here
interprets a particular contract, so no contract has to re-derive its own copy.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

variable {c : ContractSpec}

/-! ## System messages -/

/-- The four Jaune system messages are ordinary calls: `target` is present, so
a message-call wrapper's code premise activates rather than a CREATE's. -/
theorem systemTransactionMessage_target
    (benv : Benv) (target : Adr) (data : Bytes) :
    (systemTransactionMessage benv target data).target = some target := rfl

theorem systemTransactionMessage_target_isNone
    (benv : Benv) (target : Adr) (data : Bytes) :
    (systemTransactionMessage benv target data).target.isNone = false := rfl

theorem systemTransactionMessage_currentTarget
    (benv : Benv) (target : Adr) (data : Bytes) :
    (systemTransactionMessage benv target data).currentTarget = target := rfl

/-- Every system message is sent by the one fixed system address. -/
theorem systemTransactionMessage_caller
    (benv : Benv) (target : Adr) (data : Bytes) :
    (systemTransactionMessage benv target data).caller = systemAddress := rfl

/-- Opening a system transaction only refreshes the original-state record, so
the message's world is the block environment's own. -/
theorem systemTransactionMessage_benv_state
    (benv : Benv) (target : Adr) (data : Bytes) :
    (systemTransactionMessage benv target data).benv.state = benv.state := rfl

theorem systemTransactionMessage_benv_createdAccounts
    (benv : Benv) (target : Adr) (data : Bytes) :
    (systemTransactionMessage benv target data).benv.createdAccounts =
      benv.createdAccounts := rfl

/-- A system message carries whatever contract invariant its opening world
carries.  It runs the target's own installed code and transfers no value, so
every message field of the invariant is discharged from the state invariant
alone -- in particular without excluding a system target equal to `ca`. -/
theorem systemTransactionMessage_msgInv
    {ca : Adr} {benv : Benv} {target : Adr} {data : Bytes}
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts) :
    c.MsgInv ca (systemTransactionMessage benv target data) := by
  have state : c.StateInv ca
      (systemTransactionMessage benv target data).benv.state := by
    simpa [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using inv
  refine ⟨state, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa [systemTransactionMessage, processSystemTransactionMsg,
        Benv.beginTransaction] using notCreated
    · exact fun empty => Prog.compile_ne_nil
        (state.code.symm.trans (congrArg some empty))
  · intro _ current
    have htarget : target = ca := by
      simpa [systemTransactionMessage, processSystemTransactionMsg] using
        current
    subst target
    simpa [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using state.code
  · intro _ current
    have htarget : target = ca := by
      simpa [systemTransactionMessage, processSystemTransactionMsg] using
        current
    subst target
    simp [systemTransactionMessage, processSystemTransactionMsg]
  · intro transfer
    simp [systemTransactionMessage, processSystemTransactionMsg] at transfer
  · intro _ _
    simp [systemTransactionMessage, processSystemTransactionMsg]

/-- A retained system message preserves an arbitrary contract invariant and
cannot increase the world's total balance. -/
theorem SystemMessageTrace.stateInv_and_sum_le
    {ca : Adr} {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (preserves : c.Preserves ca)
    (inv : c.BenvInv ca benv) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal :=
  ContractSpec.processUncheckedSystemTransaction_preserves_inv_sum_le ca
    preserves benv target data state out trace.run inv

/-- The block-environment form of the same fact: a system message never
creates an account, so the whole `BenvInv` moves to its post-state. -/
theorem SystemMessageTrace.benvInv
    {ca : Adr} {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (preserves : c.Preserves ca)
    (inv : c.BenvInv ca benv) :
    c.BenvInv ca (benv.withState state) :=
  ⟨(trace.stateInv_and_sum_le preserves inv).1,
    by simpa [Benv.withState] using inv.ca⟩

/-! ## Transaction lists -/

/-- Wei conservation along a retained transaction list. -/
theorem ApplyTransactionsTrace.sum_le
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    sum finalBenv.state.bal ≤ sum benv.state.bal := by
  induction trace with
  | nil => exact le_rfl
  | cons head tail ih =>
      have hhead := processTransaction_sum_le head.result
      exact le_trans (by simpa [Benv.withState] using ih) hhead

/-- A transaction list threads its block environment by state alone, so the
created-account set at the end is the one it started with. -/
theorem ApplyTransactionsTrace.createdAccounts_eq
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    finalBenv.createdAccounts = benv.createdAccounts := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
      simpa [Benv.withState] using ih

/-- The transaction list the trace retains is exactly the one the semantics
ran, so every list-level ladder rung applies to a trace unchanged. -/
theorem ApplyTransactionsTrace.run
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    applyTransactions txs benv bout = .ok (finalBenv, finalBout) := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
      rw [applyTransactions, head.result]
      exact ih

/-- An arbitrary contract invariant survives a whole retained transaction
list. -/
theorem ApplyTransactionsTrace.benvInv
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (preserves : c.Preserves ca)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv) :
    c.BenvInv ca finalBenv :=
  ContractSpec.applyTransactions_preserves_inv ca preserves txs benv finalBenv
    bout finalBout trace.run sumNof inv

/-! ## Direct withdrawals -/

/-- One consensus withdrawal credits exactly its gwei amount converted to
wei, as long as that product itself does not wrap.  The premise is not
cosmetic: `Withdrawal.amount` is a full 256-bit word. -/
theorem withdrawalCredit_toNat {wd : Withdrawal}
    (bound : wd.amount.toNat * 10 ^ 9 < 2 ^ 256) :
    (wd.amount * (10 ^ 9).toB256).toNat = wd.amount.toNat * 10 ^ 9 := by
  have h9 : (10 : Nat) ^ 9 ↾ 256 = 10 ^ 9 := Nat.lo_eq_of_lt (by omega)
  rw [B256.toNat_mul, B256.toNat_toB256, h9, Nat.lo_eq_of_lt bound]

/-- The two bounds an induction over the direct-withdrawal fold needs: the
head credit does not wrap the balance sum, and the tail inherits the same
global bound over the credited world. -/
theorem withdrawalCredit_bounds
    {st : State} {wd : Withdrawal} {wds : List Withdrawal}
    (bound : sum st.bal + wdsum (wd :: wds) < 2 ^ 256) :
    sum st.bal + (wd.amount * (10 ^ 9).toB256).toNat < 2 ^ 256 ∧
      sum (st.addBal wd.recipient (wd.amount * (10 ^ 9).toB256)).bal +
        wdsum wds < 2 ^ 256 := by
  have cons : wdsum (wd :: wds) = wd.amount.toNat * 10 ^ 9 + wdsum wds := by
    simp [wdsum]
  rw [cons] at bound
  have value := withdrawalCredit_toNat (wd := wd) (by omega)
  have head : sum st.bal + (wd.amount * (10 ^ 9).toB256).toNat < 2 ^ 256 := by
    omega
  refine ⟨head, ?_⟩
  rw [sum_addBal_eq st wd.recipient _ head]
  omega

/-- The direct withdrawals never create an account, so an arbitrary contract
invariant moves across the whole credit fold under the block bound. -/
theorem benvInv_processWithdrawalsState
    {ca : Adr} {benv : Benv} {wds : List Withdrawal}
    (inv : c.BenvInv ca benv)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256) :
    c.BenvInv ca (benv.withState (processWithdrawalsState benv.state wds)) :=
  ⟨ContractSpec.processWithdrawalsState_preserves_inv ca benv.state wds bound
      inv.state,
    by simpa [Benv.withState] using inv.ca⟩

/-! ## Request messages -/

/-- The two checked request messages preserve an arbitrary contract invariant
and cannot increase the world's total balance. -/
theorem RequestsTrace.stateInv_and_sum_le
    {ca : Adr} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (preserves : c.Preserves ca)
    (inv : c.BenvInv ca benv) :
    c.StateInv ca state ∧ sum state.bal ≤ sum benv.state.bal :=
  ContractSpec.processGeneralPurposeRequests_preserves_inv_sum_le ca preserves
    benv bout state bout' trace.run inv

end ExecutionTrace

end Blanc
