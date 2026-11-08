import Blanc.SystemContracts
import Blanc.WordFakeExponential
import Blanc.ExecutionKeptChain

/-!
# EIP-7251 public observers

Short observers reading a `State`, a frame or a kept history directly: the
predeploy address and code, one storage slot, the EIP fee and the quoted fee,
the queue as stored, the submissions a history commits and the records its
blocks publish, and the root the history starts from. Nothing here mentions
the delivery model; the correspondence to the model is proved in
`ConsolidationRequestPublicHeadlines` and `ConsolidationRequestPublicHistory`.
-/

namespace Blanc.Composition.ConsolidationRequestPublic

open Jaune Blanc

/-- The EIP-7251 predeploy address `0x0000BBdDc7CE488642fb579F8B00f3a590007251`. -/
abbrev addr : Adr := consolidationRequestPredeployAddress

/-- The 414 canonical runtime bytes (SHA-256 `99e3d84d…d661`). -/
abbrev code : ByteArray := Blanc.consolidationRequestCode

/-- The canonical runtime sits at the predeploy. -/
def installed (w : State) : Prop := w.getCode addr = code

/-- Storage slot `k` of the predeploy in world `w`. -/
def word (w : State) (k : B256) : B256 := (w.getStor addr).get k

/-- The EIP's fee at excess `excess`: `fake_exponential(1, excess, 17)`. -/
def SpecFee (excess : B256) : Nat := fakeExp 1 excess.toNat 17

/-- The fee the bytes quote at excess `excess`: the word the fee loop leaves, divided by 17. -/
noncomputable def quotedFee (excess : B256) : Nat :=
  ((Classical.choose (Blanc.WordFakeExponential.run_exists_unique excess 17 1 17 0).exists).2 /
    (17 : B256)).toNat

/-- The loop's iteration count at `excess` (the same unique run). -/
noncomputable def quotedIterations (excess : B256) : Nat :=
  (Classical.choose (Blanc.WordFakeExponential.run_exists_unique excess 17 1 17 0).exists).1

/-- Queue entry `i`, read from slots `4 + 4i` to `4 + 4i + 3`: the source address (the first word cut to its low 20
bytes), then the 96 submitted bytes. -/
def queueRecord (s : B256 → B256) (i : Nat) : Bytes :=
  (s (4 + 4 * i).toB256).toAdr.toBytes ++ (s (4 + 4 * i + 1).toB256).toBytes ++
    (s (4 + 4 * i + 2).toB256).toBytes ++ (s (4 + 4 * i + 3).toB256).toBytes

/-- The live queue: entries from the head word (slot 2) up to, excluding, the tail word (slot 3). -/
def storedQueue (s : B256 → B256) : List Bytes :=
  (List.range ((s 3).toNat - (s 2).toNat)).map fun i => queueRecord s ((s 2).toNat + i)

/-- The queue still stored in world `w`. -/
def remainingQueue (w : State) : List Bytes := storedQueue (w.getStor addr).get

/-- A submission's record: the caller's 20 bytes, then its 96 calldata bytes (source pubkey, target pubkey). -/
def submissionRecord (f : Exec.Frame) : Bytes := f.sevm.caller.toBytes ++ f.sevm.data

/-- The records of the kept 96-byte user calls at the predeploy, in history order. -/
noncomputable def submissions (blocks : List KeptBlock) : List Bytes :=
  ((blocks.flatMap (KeptBlock.keptAt addr)).filter
    fun f => decide (f.sevm.caller ≠ systemAddress ∧ f.sevm.data.length = 96)).map submissionRecord

/-- Split request bytes into 116-byte records; a short tail is kept, never dropped, so equality detects it. -/
def records116 (bytes : Bytes) : List Bytes :=
  (List.range ((bytes.length + 115) / 116)).map fun i => (bytes.drop (116 * i)).take 116

/-- The type-2 (consolidation) payloads of one block's actual request list, in order. -/
def blockConsolidations (b : KeptBlock) : Bytes :=
  (b.output.requests.filterMap fun r => match r with | 2 :: tail => some tail | _ => none).flatten

/-- The consolidation records the history's blocks published, in order. -/
def emissions (blocks : List KeptBlock) : List Bytes := blocks.flatMap fun b => records116 (blockConsolidations b)

/-- The predeploy at the root: canonical code, the deployed words, no code at SYSTEM_ADDRESS. -/
structure CheckpointStart (w : State) : Prop where
  /-- The canonical runtime is installed. -/
  code : installed w
  /-- Slot 0 holds the inhibitor: no user call has succeeded yet. -/
  excess : word w 0 = B256.max
  /-- No submission is counted. -/
  count : word w 1 = 0
  /-- The queue head is 0. -/
  head : word w 2 = 0
  /-- The queue tail is 0: the queue is empty. -/
  tail : word w 3 = 0
  /-- No code at SYSTEM_ADDRESS, so only the block's own call can dequeue. -/
  systemEmpty : w.getCode systemAddress = ByteArray.empty

/-- An observation recorded at the pre-Prague block 22,431,083: the tip header and the account reads, as public
JSON-RPC returns them (`eth_getBlockByNumber`, `eth_getCode`, `eth_getStorageAt`). Lean does not authenticate them
against the state root. The tip is `Lift.WithdrawalRequest.WithdrawalDeploymentObservation.checkpointTip`'s block,
and `code` is that record's `consolidationAtP`. -/
structure ConsolidationCheckpointObservation (checkpoint : BlockChain) : Prop where
  /-- The checkpoint's last header: number 22431083, hash 0x28fb…f237, state root 0xab35…c0e3. -/
  tip : ∃ t, checkpoint.blocks.getLast? = some t ∧ t.header.number = 22431083 ∧
    t.header.hash = 0x28fb2c1d988435955e569451c6ad772f7fb5e61cddd7463c7b60e933ed5ff237 ∧
    t.header.stateRoot = 0xab350e0fe349aef68947ede26295f8946c34ce3af5e3ec76f4b26ddeef29c0e3
  /-- `eth_getCode(0x…7251)`: the canonical bytes. -/
  code : installed checkpoint.state
  /-- `eth_getStorageAt` slot 0: the inhibitor. -/
  excess : word checkpoint.state 0 = B256.max
  /-- `eth_getStorageAt` slot 1: 0. -/
  count : word checkpoint.state 1 = 0
  /-- `eth_getStorageAt` slot 2: 0. -/
  head : word checkpoint.state 2 = 0
  /-- `eth_getStorageAt` slot 3: 0. -/
  tail : word checkpoint.state 3 = 0
  /-- `eth_getCode(0xff…fe)` is empty. -/
  systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty

/-- Every committed submission is, in order, a record the blocks published or an entry still in the final queue. -/
def Fifo (blocks : List KeptBlock) (final : State) : Prop :=
  submissions blocks = emissions blocks ++ remainingQueue final

end Blanc.Composition.ConsolidationRequestPublic
