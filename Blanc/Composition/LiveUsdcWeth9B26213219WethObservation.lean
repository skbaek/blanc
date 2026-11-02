import Blanc.Composition.LiveUsdcWeth9B26213219History
import Blanc.Lift.Weth9.Creation.SignedInput
import Blanc.Lift.Weth9.Creation.ObservationData
import Blanc.Lift.Weth9.Creation.SigningHash
import Blanc.ExecutionTrieBinding

/-! Original WETH deployment observations. The supplied block's number and
timestamp, the signed transaction at its slot 85 and the receipt at key 85 are
the observed correspondence consumed here. No consensus inclusion, trie
authentication or new history assumption is adopted. -/
namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Weth9.Creation

/-- Fetched correspondence for the actual original block and receipt: the
header's number and timestamp, an already-decoded legacy transaction at slot 85
with the signed creation transaction's RLP item, and the receipt at key 85. The
slot is fixed only up to leading zero bytes of the signature scalars, which
`Tx.toBLT` trims and `recoverSender` does not read. Each field is consumed by
`WethOriginalObservation.deployment`. -/
structure WethOriginalObservation {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed) where
  number : block.block.header.number = ObservationData.blockNumber
  timestamp : block.block.header.timestamp = ObservationData.blockTimestamp
  slot : ∃ tx gasPrice receiver, block.block.txs[85]? = some (.inr tx) ∧
    tx.type = .zero gasPrice receiver ∧ tx.toBLT = SignedInput.tx.toBLT
  receipt : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes (85 : Nat).toBytes)]? =
    some ObservationData.receipt

/-- The legacy transaction at the observed slot. -/
noncomputable def WethOriginalObservation.tx {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : WethOriginalObservation block) : Tx :=
  observed.slot.choose

theorem WethOriginalObservation.atSlot {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : WethOriginalObservation block) :
    block.block.txs[85]? = some (.inr observed.tx) := by
  obtain ⟨_, _, atSlot, _⟩ := observed.slot.choose_spec
  exact atSlot

/-- The observed slot carries the creation's fields, and the checked signing
hash recovers the deployer from it: equal legacy RLP items give equal fields and
equal signature words (`legacy_fields_of_toBLT_eq`). -/
theorem WethOriginalObservation.fields {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : WethOriginalObservation block)
    (hashed : signingPayload.keccak =
      0x1e62afdbf54076edd8083f93eab1bf693f2a5a3675886b669d13d9b3e6221235) :
    observed.tx.type = .zero 21000000000 none ∧ observed.tx.data = code.toList ∧
      observed.tx.value = 0 ∧ observed.tx.nonce = 446 ∧
      recoverSender 1 observed.tx = .ok deployer ∧ observed.tx.gas = 1500000 := by
  obtain ⟨_, _, _, type, same⟩ := observed.slot.choose_spec
  obtain ⟨nonce, price, gas, receiver, value, data, v, r, s⟩ :=
    legacy_fields_of_toBLT_eq type (rfl : SignedInput.tx.type = _) same
  have type : observed.tx.type = .zero 21000000000 none := by
    rw [WethOriginalObservation.tx, type, price, receiver]
  have recovered := recoveredSender_of_fields type nonce gas value data v
    (r.trans (B256.toB256_toBytes _)) (s.trans (B256.toB256_toBytes _)) hashed
  exact ⟨type, data, value, nonce, recovered, gas⟩

noncomputable def WethOriginalObservation.cut {pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : WethOriginalObservation block) : block.bodyTrace.transactions.TxSplit 85 :=
  block.bodyTrace.txSplitOfSlot observed.atSlot (tx := observed.tx) rfl

/-- The observed slot and successful receipt construct the deployment input.
The exact hash computation, subsequent actual history and HASH-T remain
explicit; no final footprint, funding, collision or allowance premise is supplied. -/
noncomputable def WethOriginalObservation.deployment
    {checkpoint pre completed : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed}
    (observed : WethOriginalObservation block)
    (hashed : signingPayload.keccak =
      0x1e62afdbf54076edd8083f93eab1bf693f2a5a3675886b669d13d9b3e6221235)
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed checkpoint)
    (fresh : Weth9.KeysFresh (fun _ => False)
      (Weth9.midTouchedKeysIn Weth9.Creation.weth9Address
        ((MidHistoryTraceIn.tail block observed.cut).append history))) :
    WethDeploymentTo checkpoint :=
  .of_original_creation_receipt block observed.number observed.timestamp
    observed.atSlot (tx := observed.tx) rfl (observed.fields hashed).1
    (observed.fields hashed).2.1 (observed.fields hashed).2.2.1 (observed.fields hashed).2.2.2.1
    (observed.fields hashed).2.2.2.2.1 (observed.fields hashed).2.2.2.2.2 observed.receipt rfl
    history fresh

/-- The observed original WETH9 creation block joined to a configured history ending at
`checkpoint`, with trace-local freshness of the keys that history touches. No installed code,
`SumNof`, footprint, funding, collision or signing-hash premise is an input. -/
structure WethObservedHistory (checkpoint : BlockChain) where
  pre : BlockChain
  completed : BlockChain
  block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre completed
  observed : WethOriginalObservation block
  history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed checkpoint
  fresh : Weth9.KeysFresh (fun _ => False)
    (Weth9.midTouchedKeysIn Weth9.Creation.weth9Address
      ((MidHistoryTraceIn.tail block observed.cut).append history))

/-- The deployment record, from the observation and the checked signing hash. -/
noncomputable def WethObservedHistory.deployment {checkpoint : BlockChain}
    (h : WethObservedHistory checkpoint) : WethDeploymentTo checkpoint :=
  h.observed.deployment Weth9.Creation.signingPayload_hash h.history h.fresh

end Blanc.Composition.LiveUsdcWeth9B26213219
