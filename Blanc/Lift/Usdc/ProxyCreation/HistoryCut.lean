import Blanc.Lift.Usdc.ProxyCreation.Transaction
import Blanc.ExecutionHistoryCommittedCuts
import Blanc.Lift.Usdc.Slots

/-!
# Original constructor seed at the actual transaction cut

The supplied configured block and its actual index-22 transaction split are
the candidate C occurrence. Transaction identity and successful receipt lookup
remain explicit inputs. Identifying this block with historical C, authenticating
its receipt commitment, and placing it in the consumed history are provenance
obligations of the caller. No endpoint state or synthetic execution is assumed.

Every conclusion concerns `cut.afterBenv.state`, immediately after the selected
transaction's complete settlement, before any later transaction or body stage.
No governance or allowance-continuity condition before D is introduced here.
-/

namespace Blanc.Lift.Usdc.ProxyCreation

open Jaune Blanc.ExecutionTrace

/-- Constructor-produced facts consumed at the start of the C-to-D history.
Slot separation remains a premise of its producer, rather than a hash axiom. -/
structure OriginalConstructorSeed (state : State) (pair : Adr) (tracked : Adr → Prop) : Prop where
  runtime : state.getCode usdcProxy = Proxy.code
  storage : state.getStor usdcProxy =
    (Stor.empty.set implSlot initialImplementation).set adminSlot originalCreator.toB256
  allowance : ∀ spender, tracked spender → (state.getStor usdcProxy).get (allowSlot pair spender) = 0

section Cut

variable {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post)
    (cut : block.bodyTrace.transactions.TxSplit 22)
    (hsg : block.fork.ruleSet.stateGas = none)
    (receiver : cut.tx.type.receiver? = none)
    (input : cut.tx.data = code.toList) (value : cut.tx.value = 0)
    (sender : cut.head.sender = originalCreator) (nonce : cut.tx.nonce = 20)

include hsg receiver input value sender nonce

/-- The original constructor's actual settled transaction supplies the code
and entire storage at the after-C seed, rather than at block end. -/
theorem original_constructor_effects_after_cut22
    (clean : cut.head.messageOut.error = none) :
    cut.afterBenv.state.getCode usdcProxy = Proxy.code ∧
      cut.afterBenv.state.getStor usdcProxy =
        (Stor.empty.set implSlot initialImplementation).set adminSlot originalCreator.toB256 := by
  have headSg : cut.benv.stat.rules.stateGas = none := by
    change cut.afterBenv.stat.rules.stateGas = none
    rw [block.txSplit_stat cut]
    exact hsg
  exact original_constructor_effects_of_transactionTrace cut.head headSg
    receiver input value sender nonce clean

/-- The same actual constructor provides the protected zero allowance rows.
The explicit apartness input excludes the two words written by the constructor. -/
theorem original_constructor_seed_after_cut22
    (clean : cut.head.messageOut.error = none) {pair : Adr} {tracked : Adr → Prop}
    (apart : ∀ spender, tracked spender →
      allowSlot pair spender ≠ implSlot ∧ allowSlot pair spender ≠ adminSlot) :
    OriginalConstructorSeed cut.afterBenv.state pair tracked := by
  obtain ⟨runtime, storage⟩ := original_constructor_effects_after_cut22 block cut hsg
    receiver input value sender nonce clean
  refine ⟨runtime, storage, ?_⟩
  intro spender member
  obtain ⟨implementation, admin⟩ := apart spender member
  rw [storage, Stor.get_set_ne _ admin.symm, Stor.get_set_ne _ implementation.symm]
  simp only [Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc, Std.TreeMap.getD_emptyc]

/-- A successful receipt at the actual final body output supplies the clean
outcome of this same index-22 constructor. The bounded receipt API preserves it
through the real suffix and body stages, without using the block-end state as
the seed. The caller still authenticates C, its inclusion and receipt commitment. -/
theorem original_constructor_seed_of_receipt_cut22
    {receipt : Fin 5 × Receipt}
    (receiptAt : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (22 : Nat).toBytes)]? =
      some receipt)
    (succeeded : receipt.2.succeeded = true) {pair : Adr} {tracked : Adr → Prop}
    (apart : ∀ spender, tracked spender →
      allowSlot pair spender ≠ implSlot ∧ allowSlot pair spender ≠ adminSlot) :
    cut.head.messageOut.error = none ∧
      OriginalConstructorSeed cut.afterBenv.state pair tracked := by
  have actual := block.receipt_of_txSplit_settledRoots cut hsg (by decide) (by decide)
  rw [← cut.putIndex_eq.1] at receiptAt
  have same := Option.some.inj (actual.symm.trans receiptAt)
  have status := congrArg (fun r : Fin 5 × Receipt => r.2.succeeded) same
  change cut.head.messageOut.error.isNone = receipt.2.succeeded at status
  have clean : cut.head.messageOut.error = none := by
    rw [succeeded] at status
    cases error : cut.head.messageOut.error with
    | none => rfl
    | some halt =>
        rw [error] at status
        contradiction
  exact ⟨clean, original_constructor_seed_after_cut22 block cut hsg
    receiver input value sender nonce clean apart⟩

end Cut

end Blanc.Lift.Usdc.ProxyCreation
