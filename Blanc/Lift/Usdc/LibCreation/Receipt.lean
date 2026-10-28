import Blanc.Lift.Usdc.LibCreation.SignedInput
import Blanc.Lift.Usdc.LibCreation.Settlement
import Blanc.Lift.ConstructorTransaction
import Blanc.ExecutionBodyTransactionCut
import Blanc.ExecutionMidHistoryInFacts

/-! Original successful library creation through transaction settlement.
The configured block, indexed slot and receipt correspondence remain explicit. -/
namespace Blanc.Lift.Usdc.LibCreation.SignedInput

open Jaune ExecutionTrace

/-- The decoder-certified signed envelope and its original successful receipt
install the ADDRESS-patched runtime and empty storage after transaction settlement. -/
theorem effects_of_original_slot
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 14)
    (atIndex : block.block.txs[14]? = some envelope.entry)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (14 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode usdcLib = Lib.code ∧
      cut.afterBenv.state.getStor usdcLib = Stor.empty := by
  obtain ⟨index, same⟩ := block.bodyTrace.txSplit_tx_eq_of_slot cut atIndex (tx := tx) rfl
  have recovered := SignedInput.recovered
  rw [← same] at recovered
  have sender := block.txSplit_sender_of_recovery cut recovered
  have receiver : cut.tx.type.receiver? = none := by rw [same]; rfl
  have input : cut.tx.data = code.toList := by rw [same]; rfl
  have target : cut.head.msg.currentTarget = usdcLib := by
    rw [cut.head.creation_target_eq receiver, sender, same]
    exact create_address
  have stateGas : cut.benv.beginTransaction.stat.rules.stateGas = none := by
    change cut.benv.stat.rules.stateGas = none
    have stat : cut.benv.stat = (initBenv block.fork pre block.block.header).stat :=
      block.txSplit_stat cut
    rw [stat]
    exact block.forkIn.stateGas_none
  have clean := block.txSplit_error_eq_none_of_receipt cut block.forkIn.stateGas_none
    (by simpa only [index] using lookup) succeeded
  have fields := cut.head.creation_message_fields receiver input
  have msgStateGas : cut.head.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv cut.head.prepared]
    exact stateGas
  have nonempty : Lib.code.toList ≠ [] := by
    rw [ByteArray.toList_eq_toList_data]
    decide +kernel
  have effects := cut.head.getCode_getStor_of_create_effects stateGas receiver input
    clean nonempty (storage := Stor.empty) (by
      intro installed retained innerClean
      have deleted := constructor_deletions_of_createTrace retained innerClean fields.2.1
        fields.2.2.1 msgStateGas
      have installed := constructor_effects_of_createTrace retained innerClean fields.2.1
        target fields.2.2.1 msgStateGas
      exact ⟨deleted, congrArg ByteArray.toList installed.1, installed.2⟩)
  rw [target] at effects
  change cut.txState.getCode usdcLib = Lib.code ∧ cut.txState.getStor usdcLib = Stor.empty
  refine ⟨?_, effects.2⟩
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simpa only [ByteArray.toList_eq_toList_data] using effects.1

end Blanc.Lift.Usdc.LibCreation.SignedInput
