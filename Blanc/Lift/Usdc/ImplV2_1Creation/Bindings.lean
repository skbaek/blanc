import Blanc.Lift.Usdc.ImplV2_1Creation.Check
import Blanc.Lift.Usdc.ImplV2_1.Cert
import Blanc.Lift.ConstructorTransaction
import Blanc.Lift.Usdc.GovernanceHistory

/-! Unadopted constructor preview; original transaction and receipt witnesses remain explicit. -/

namespace Blanc.Lift.Usdc.ImplV2_1Creation

open Jaune ExecutionTrace

/-- The certified creation entry is the shared modern owner constructor. -/
theorem constructor_entry : cert.prog[0]? = some solcOwnerConstructor := by
  rfl

/-- The certified owner initializer is the shared modern helper. -/
theorem owner_entry : cert.prog[1]? = some SolcStorageReturn.ownerInit := by
  rfl

/-- The certified return entry selects this implementation's exact runtime. -/
theorem return_entry : cert.prog[2]? = some
    (solcRuntimeReturn [0x53, 0xeb] [0x00, 0x00, 0x67] (by decide) (by decide)) := by
  rfl

/-- Byte identity only; no historical execution or inclusion is inferred. -/
theorem runtime_window : code.sliceD 103 21483 0 = ImplV2_1.code.toList := by
  rw [ByteArray.sliceD_eq, ByteArray.toList_eq_toList_data,
    ByteArray.toList_eq_toList_data]
  apply eq_of_beq
  decide +kernel

/-- The exact constructor installs the registered runtime and owner storage
at its original transaction cut. Original fields, CREATE address and successful
receipt remain explicit; no installed-code or deletion premise is assumed. -/
theorem effects_of_original_receipt
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 8)
    (receiver : cut.tx.type.receiver? = none) (input : cut.tx.data = code.toList)
    (addressEq : computeContractAddress cut.head.sender cut.tx.nonce = F2prime.implementationV2_1)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (8 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode F2prime.implementationV2_1 = ImplV2_1.code ∧
      cut.afterBenv.state.getStor F2prime.implementationV2_1 =
        solcOwnerConstructorStorage Stor.empty cut.head.sender := by
  have actualLookup :
      block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? = some receipt := by
    rw [cut.putIndex_eq.1]
    exact lookup
  exact solcOwnerConstructor_runtime_of_txSplit_receipt
    (size := 21483) (offset := 103) cert_check constructor_entry owner_entry return_entry
    (by decide +kernel) (by decide +kernel) (by decide) runtime_window block cut
    (HistFork.stateGas_none block.forkIn) receiver input addressEq actualLookup succeeded

end Blanc.Lift.Usdc.ImplV2_1Creation
