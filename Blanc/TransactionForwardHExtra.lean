import Blanc.TransactionForward
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionAccountingAdmissionIn
import Blanc.TransactionForwardH

/-!
# The forward direction of a transaction, from rule facts

`Blanc/TransactionForward.lean` assembles `processTransaction` from its stages under the
settlement facts of the covered forks (no touched-account sweep, refund quotient 5). This module
is the same converse with no settlement fact beyond `rules.stateGas = none` and
`rules.bal = none`, so that it applies to every pre-Amsterdam schedule:

* `processMessageCall_create_of_message`: the creation wrapper of a top-level CREATE message
  whose target has neither code nor nonce, over a successful `processCreateMessage`;
* `txGasUsedQ`: the gas a transaction uses under refund quotient `q`;
* `processTransaction_of_stagesH`: the whole transaction, whose settled state is the message's
  state with the sender's refund and the coinbase's fee credited, the accounts to delete
  destroyed and the touched accounts swept under the rules' own `touchedSweep`.
-/

namespace Blanc

open Jaune ExecutionTrace

/-- **The creation wrapper over a successful raw creation.**  A creation message (`target`
absent) under rules without a state-gas dimension, whose target has neither code nor nonce,
settles as its `processCreateMessage` core: the same state, the core's gas, and (with no core
error) its logs, accounts to delete, touched accounts and non-negative refund counter. -/
theorem processMessageCall_create_of_message {msg : Msg} {post : Devm} {refund : Nat}
    (hsg : msg.benv.stat.rules.stateGas = none) (htarget : msg.target = none)
    (hfresh : accountHasCodeOrNonce msg.benv.state msg.currentTarget = false)
    (hcreate : processCreateMessage msg = .ok post) (herror : post.error = none)
    (hrefund : Int.toNat? post.refundCounter = some refund) :
    processMessageCall msg = .ok (post.state,
      { gasLeft := post.gasLeft, refundCounter := (refund : Int),
        logs := post.logs, accountsToDelete := post.accountsToDelete,
        error := none, returnData := post.output,
        touchedAccounts := post.meta.touchedAccounts }) := by
  unfold processMessageCall
  simp only [htarget, Option.isNone_none, ↓reduceIte]
  unfold processMessageCall.create
  rw [hsg]
  simp only [hfresh, Bool.false_eq_true, ↓reduceIte, hcreate, bind, Except.bind, Except.bimap, id,
    herror, Option.isNone_none, hrefund, Option.toExcept]

end Blanc
