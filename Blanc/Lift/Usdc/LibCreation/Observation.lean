import Blanc.Lift.Usdc.LibCreation.ObservationData
import Blanc.Lift.Usdc.LibCreation.Receipt
import Blanc.Lift.ConstructorTransaction

/-! Unadopted finite observation binding for the original library deployment.
The supplied block and receipt must correspond to the observed original history;
these equalities do not authenticate consensus, transactions or receipt roots. -/
namespace Blanc.Lift.Usdc.LibCreation

open Jaune ExecutionTrace

/-- The observed signed wire is exactly the decoder-certified proof input. -/
theorem observed_signed_bytes : SignedInput.signedBytes = ObservationData.signedBytes := by
  unfold SignedInput.signedBytes SignedInput.payload
  rw [ByteArray.toList_eq_toList_data]
  apply eq_of_beq
  decide +kernel

/-- The exact observed bytes pass Jaune's strict signed transaction decoder. -/
theorem observed_signed_decode :
    ObservationData.signedBytes.toBLT?.bind (fun blt => blt.toExTx.toOption) =
      some SignedInput.tx := by
  rw [← observed_signed_bytes]
  exact SignedInput.signed_decode

/-- The recorded coordinates select Shanghai in the pinned mainnet schedule. -/
theorem observed_fork :
    mainnetChainConfig.forkAt ObservationData.blockNumber ObservationData.blockTimestamp =
      .ok .shanghai := by
  decide +kernel

/-- The fetched receipt is successful; its gas counter is cumulative. -/
theorem observed_receipt_success : ObservationData.receipt.2.succeeded = true := rfl

/-- Explicit correspondence to the original block, selected signed slot and
receipt. This is an unresolved fetched-data boundary, not an adopted ENV premise. -/
structure OriginalObservation {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed) where
  number : block.block.header.number = ObservationData.blockNumber
  timestamp : block.block.header.timestamp = ObservationData.blockTimestamp
  hash : block.block.header.hash = ObservationData.blockHash
  stateRoot : block.block.header.stateRoot = ObservationData.stateRoot
  transactionRoot : block.block.header.txsRoot = ObservationData.transactionRoot
  receiptRoot : block.block.header.receiptRoot = ObservationData.receiptRoot
  slot : block.block.txs[14]? = some SignedInput.envelope.entry
  receipt : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (14 : Nat).toBytes)]? =
    some ObservationData.receipt

/-- The observed slot constructs its cut inside the supplied original trace. -/
noncomputable def OriginalObservation.cut {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : OriginalObservation block) : block.bodyTrace.transactions.TxSplit 14 :=
  block.bodyTrace.txSplitOfSlot observed.slot (tx := SignedInput.tx) rfl

/-- The same original cut gets installed code and empty storage from the exact
observed receipt; no constructor effect or success premise is supplied separately. -/
theorem OriginalObservation.installed {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : OriginalObservation block)
    (cut : block.bodyTrace.transactions.TxSplit 14) :
    cut.afterBenv.state.getCode usdcLib = Lib.code ∧
      cut.afterBenv.state.getStor usdcLib = Stor.empty := by
  exact SignedInput.effects_of_original_slot block cut observed.slot observed.receipt
    observed_receipt_success

/-- Every retained node of the original observed creation stays away from the
USDC proxy. The signed input determines the target; no success premise is needed. -/
theorem OriginalObservation.retainedNodes_target_ne_proxy {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : OriginalObservation block) :
    ∀ R ∈ observed.cut.head.settledRoots, ∀ n ∈ Exec.retainedNodes R.run,
      n.sevm.currentTarget ≠ usdcProxy := by
  let cut := observed.cut
  obtain ⟨_, same⟩ := block.bodyTrace.txSplit_tx_eq_of_slot cut observed.slot
    (tx := SignedInput.tx) rfl
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
  apply cut.head.retainedNodes_currentTarget_ne_of_create_noExecs
    receiver input cert_check (by decide +kernel) stateGas
  rw [target]
  decide +kernel

end Blanc.Lift.Usdc.LibCreation
