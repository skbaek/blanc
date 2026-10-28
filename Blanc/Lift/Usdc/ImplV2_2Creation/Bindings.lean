import Blanc.Lift.Usdc.ImplV2_2Creation.Check
import Blanc.Lift.Usdc.Impl.Cert
import Blanc.Lift.ConstructorTransaction
import Blanc.Lift.Usdc.GovernanceHistory

/-! Unadopted constructor preview; original transaction and receipt witnesses remain explicit. -/

namespace Blanc.Lift.Usdc.ImplV2_2Creation

open Jaune ExecutionTrace

/-- The certified creation entry is the shared modern owner constructor. -/
theorem constructor_entry : cert.prog[0]? = some solcOwnerConstructor := by
  rfl

/-- The certified owner initializer is the shared modern helper. -/
theorem owner_entry : cert.prog[1]? = some SolcStorageReturn.ownerInit := by
  rfl

/-- The certified return entry selects this implementation's exact runtime. -/
theorem return_entry : cert.prog[2]? = some
    (solcRuntimeReturn [0x5b, 0xa8] [0x00, 0x00, 0x67] (by decide) (by decide)) := by
  rfl

/-- Bounded Boolean comparison for runtime chunk 0. -/
theorem runtime_chunk0 :
    (code.data.toList.sliceD 103 4096 0 == Impl.codeChunk0) = true := by
  decide +kernel

/-- Bounded Boolean comparison for runtime chunk 1. -/
theorem runtime_chunk1 :
    (code.data.toList.sliceD 4199 4096 0 == Impl.codeChunk1) = true := by
  decide +kernel

/-- Bounded Boolean comparison for runtime chunk 2. -/
theorem runtime_chunk2 :
    (code.data.toList.sliceD 8295 4096 0 == Impl.codeChunk2) = true := by
  decide +kernel

/-- Bounded Boolean comparison for runtime chunk 3. -/
theorem runtime_chunk3 :
    (code.data.toList.sliceD 12391 4096 0 == Impl.codeChunk3) = true := by
  decide +kernel

/-- Bounded Boolean comparison for runtime chunk 4. -/
theorem runtime_chunk4 :
    (code.data.toList.sliceD 16487 4096 0 == Impl.codeChunk4) = true := by
  decide +kernel

/-- Bounded Boolean comparison for runtime chunk 5. -/
theorem runtime_chunk5 :
    (code.data.toList.sliceD 20583 2984 0 == Impl.codeChunk5) = true := by
  decide +kernel

/-- Byte identity only; no historical execution or inclusion is inferred. -/
theorem runtime_window : code.sliceD 103 23464 0 = Impl.code.toList := by
  rw [ByteArray.sliceD_eq, ByteArray.toList_eq_toList_data,
    ByteArray.toList_eq_toList_data]
  change code.data.toList.sliceD 103 (4096 + (4096 + (4096 + (4096 + (4096 + 2984))))) 0 =
    Impl.codeChunk0 ++ Impl.codeChunk1 ++ Impl.codeChunk2 ++
      Impl.codeChunk3 ++ Impl.codeChunk4 ++ Impl.codeChunk5
  simp only [List.append_assoc]
  rw [Blanc.List.sliceD_split _ _ 4096 103,
    Blanc.List.sliceD_split _ _ 4096 4199,
    Blanc.List.sliceD_split _ _ 4096 8295,
    Blanc.List.sliceD_split _ _ 4096 12391,
    Blanc.List.sliceD_split _ _ 4096 16487,
    eq_of_beq runtime_chunk0, eq_of_beq runtime_chunk1, eq_of_beq runtime_chunk2,
    eq_of_beq runtime_chunk3, eq_of_beq runtime_chunk4, eq_of_beq runtime_chunk5]

/-- The exact constructor installs the registered runtime and owner storage
at its original transaction cut. Original fields, CREATE address and successful
receipt remain explicit; no installed-code or deletion premise is assumed. -/
theorem effects_of_original_receipt
    {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed)
    (cut : block.bodyTrace.transactions.TxSplit 26)
    (receiver : cut.tx.type.receiver? = none) (input : cut.tx.data = code.toList)
    (addressEq : computeContractAddress cut.head.sender cut.tx.nonce = F2prime.implementationV2_2)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (26 : Nat).toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.afterBenv.state.getCode F2prime.implementationV2_2 = Impl.code ∧
      cut.afterBenv.state.getStor F2prime.implementationV2_2 =
        solcOwnerConstructorStorage Stor.empty cut.head.sender := by
  have actualLookup :
      block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? = some receipt := by
    rw [cut.putIndex_eq.1]
    exact lookup
  exact solcOwnerConstructor_runtime_of_txSplit_receipt
    (size := 23464) (offset := 103) cert_check constructor_entry owner_entry return_entry
    (by decide +kernel) (by decide +kernel) (by decide) runtime_window block cut
    (HistFork.stateGas_none block.forkIn) receiver input addressEq actualLookup succeeded

end Blanc.Lift.Usdc.ImplV2_2Creation
