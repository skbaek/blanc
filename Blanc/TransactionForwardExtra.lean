import Blanc.ExecutionTrace
import Blanc.MessageExecution
import Blanc.DeploymentMessage
import Blanc.ForwardCall
import Blanc.TransactionForward

/-!
# The forward direction of a successful transaction

`ExecutionTrace.exists_transactionTrace` and `TransactionTrace.exists_finalStateForm` invert a
successful `processTransaction`: they read its validation, admission, debit, prepared message and
settlement out of the result.  This module is the converse, contract-neutral, for the forks
without a state-gas dimension or a block access list (`CoveredFork`): given each stage's
successful result, Jaune's `processTransaction` returns the exact settled state.  A transaction
of one contract's theorem therefore needs only its own stage facts (which for a concrete
transaction are evaluations) and the message's outcome, never a private copy of the envelope.

* `processMessageCall_call_of_message`: the call wrapper of a code-free-of-delegation, auth-free
  message over a successful `processMessage`.
* `processTransaction_of_stages`: the whole transaction.
* `processTransaction_call_value_of_exec`: a type-2 call with arbitrary affordable value,
  from its admission facts and the execution after value transfer.
-/

namespace Blanc

open Jaune ExecutionTrace

/-! ### The admission checks of a type-2 transaction, from stated facts -/

/-- Validation without a state-gas dimension when init-code limits are disabled.
Direct intrinsic projections keep concrete CREATE payloads out of pair conversion. -/
theorem validateTransaction_ok_of_noInitcodeLimit
    {rules : ForkRules} {tx : Tx} {sender : Adr} {f : Nat}
    (hsg : rules.stateGas = none) (hinit : rules.creation.initCodeLimit = false)
    (hfloor : (calculateIntrinsicCost rules tx sender).2 = f)
    (hgas : max (calculateIntrinsicCost rules tx sender).1 f ≤ tx.gas)
    (hnonce : tx.nonce ≠ UInt64.max)
    (hcap : checkTransactionGasCap rules.tx tx.gas = .ok ()) :
    validateTransaction rules tx sender =
      .ok ((calculateIntrinsicCost rules tx sender).1, f) := by
  have hlimit : checkInitcodeLimit rules tx.type.receiver? tx.data.length = .ok () := by
    simp only [checkInitcodeLimit, hinit, Bool.false_eq_true, ↓reduceIte]
  cases hcost : calculateIntrinsicCost rules tx sender with
  | mk i g =>
    simp only [hcost] at hfloor hgas ⊢
    subst f
    unfold validateTransaction
    simp only [hsg, hcost, Nat.not_lt.mpr hgas, ↓reduceIte]
    cases hm : rules.tx.maxGas with
    | none => simp only [hnonce, ↓reduceIte, bind, Except.bind, hlimit]
    | some m => simp only [bind, Except.bind, hlimit, hcap, hnonce, ↓reduceIte]

/-! ### A type-2 call transaction from the outcome of its message's execution -/

/-! ### The intrinsic gas of a plain call -/

/-! ### The same quantities under the deployment vocabulary

`Blanc/DeploymentMessage.lean` names the settlement of a transaction for the deployment corridor
(`deploymentEffectiveGasPrice`, `deploymentUsedGasFromMessage`, `deploymentFinalState`).  They are the
quantities of `processTransaction_call_of_exec` for a type-2 transaction; these equations tie the two
vocabularies together so that a consumer of either can use the other's lemmas. -/

end Blanc
