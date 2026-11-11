import Blanc.Corpus.Freeze.RingCommon

/-!
# G0 freeze: the EIP-2935 history-storage cells (H-S1 .. H-S10)

Each cell is a `Prop` definition; the later proof is `theorem h_sN : H_SN`. Every premise is a named binder with a
one-line comment. Statements are read from the 83 bytes of `Blanc.historyStorageCode` (`Blanc/SystemContracts.lean:46`)
as the lifted certificate splits them (`Blanc/Lift/SystemExecution/HistoryStorage/Cert.lean`):

* `0x00`: `CALLER == SYSTEM_ADDRESS` jumps to the write at `0x46`;
* write (`0x46`): `sstore((NUMBER - 1) mod 8191, calldataload(0))`, `STOP`; no `CALLDATASIZE` check;
* read: `CALLDATASIZE - 32 ≠ 0` reverts; `q = calldataload(0)`; `q > NUMBER - 1` reverts; `NUMBER - q > 8191`
  reverts (256-bit arithmetic); return the 32-byte word `sload(q mod 8191)`. No presence tag, no `CALLVALUE` check.

History statements range over kept histories and their settled frames, and take `CoveredFork` for every block:
nothing is claimed at Amsterdam except H-S10.
-/

namespace Blanc.Corpus.Freeze.HistoryStorage

open Jaune Blanc ExecutionTrace JauneConsensus
open Blanc.Corpus.Freeze
open Blanc.Lift.RequestSystem (RegularGasWithin)

/-! ## Vocabulary read from the bytes -/

/-- The contract's address. -/
abbrev addr : Adr := historyStorageAddress

/-- The slot the protocol call at block number `N` writes: `(N - 1) mod 8191`, in 256-bit arithmetic. -/
def key (N : B256) : B256 := (N - 1) % ring

/-- Storage after the system write at block number `N` of the word `v`. -/
def write (s : B256 → B256) (N v : B256) : B256 → B256 :=
  fun k => if k = key N then v else s k

/-- Storage after a list of system writes, in order. -/
def writeAll (s : B256 → B256) : List (B256 × B256) → B256 → B256
  | [] => s
  | (N, v) :: ws => writeAll (write s N v) ws

/-- The bytes' window guard at block number `N` for query `q`: `q ≤ N - 1` and `N - q ≤ 8191`, unsigned 256-bit.
For `0 < N`, exactly `N - 8191 ≤ q ≤ N - 1`. -/
def InWindow (N q : B256) : Prop := q.toNat ≤ (N - 1).toNat ∧ (N - q).toNat ≤ 8191

instance (N q : B256) : Decidable (InWindow N q) := by unfold InWindow; infer_instance

/-- What the bytes' read at block number `N` of `q` returns from storage `s`: the slot `q mod 8191` when the
window guard passes, whatever that slot holds; `none` where the bytes revert. -/
def read (s : B256 → B256) (N q : B256) : Option B256 :=
  if InWindow N q then some (s (q % ring)) else none

/-- The pair a kept block's protocol call writes: its number and its parent hash. The call's input is the hash of the
parent chain's tip (`getLast256BlockHashes`), which `validateHeader` makes equal to `header.parentHash`. -/
def blockWrite (b : KeptBlock) : B256 × B256 :=
  (b.block.header.number.toB256, b.block.header.parentHash)

/-- The protocol's own call: SYSTEM_ADDRESS, any calldata length, non-static; it stores `calldataload(0)` at
`key NUMBER`, returns nothing, emits nothing. -/
structure SystemWrite (f : Exec.Frame) : Prop where
  caller : f.sevm.caller = systemAddress
  nonstatic : f.sevm.isStatic = false
  state : f.post.state =
    f.pre.state.setStorVal f.sevm.currentTarget (key f.sevm.benvStat.number.toB256) (Sevm.dataWord f.sevm 0)
  output : f.post.output = []
  logs : f.post.logs = f.pre.logs

/-- An ordinary read: any other caller, exactly 32 bytes, the window guard passes; it returns the slot's word,
changes no account (the value it was sent stays with the contract), emits nothing. -/
structure Read (f : Exec.Frame) : Prop where
  caller : f.sevm.caller ≠ systemAddress
  length : f.sevm.data.length = 32
  accepts : ∃ w, read (frameStor f) f.sevm.benvStat.number.toB256 (Sevm.dataWord f.sevm 0) = some w ∧
    f.post.output = w.toBytes
  state : f.post.state = f.pre.state
  logs : f.post.logs = f.pre.logs

/-- The named list of successes. -/
def Frame (f : Exec.Frame) : Prop := SystemWrite f ∨ Read f

/-- The gas of one `SLOAD` of `k` at `a` from a frame's access set (EIP-2929). -/
def sloadGas (pre : Devm) (a : Adr) (k : B256) : Nat :=
  if (a, k) ∈ pre.accessedStorageKeys then gasWarmAccess else gasColdSload

/-- The exact gas of the accepted read path: 125 for its 37 non-`SLOAD` steps (no `JUMPDEST`, four `JUMPI`s, the
`MSTORE` with its one-word expansion, `RETURN` at 0), plus the `SLOAD`'s warm or cold charge. -/
def readGas (pre : Devm) (a : Adr) (q : B256) : Nat :=
  125 + sloadGas pre a (q % ring)

/-- The header of the block numbered one below block `i`'s on this history: the previous kept block's, or the
start's tip for `i = 0`. -/
def prevHeader (start : BlockChain) (blocks : List KeptBlock) (i : Nat) : Option Header :=
  if i = 0 then start.blocks.getLast?.map (·.header) else (blocks[i - 1]?).map (·.block.header)

/-! ## The observation record (H-S4) -/

/-- **H-S4's root**: what an observed pre-Prague checkpoint must hold for the H statements. Each field is a public
JSON-RPC read at block 22,431,083; Lean does not authenticate them against the state root. All underlying reads already
appear in registered records (`checkpointTip` and `historyAtP` of `WithdrawalDeploymentObservation`, `systemEmpty` of
`ConsolidationCheckpointObservation`); packaging them as `HistoryStorageCheckpointObservation` is submitted for user
adoption as registered provenance (§5/§9). The contract's storage there is not read: no H statement consumes it. -/
structure HistoryStorageCheckpointObservation (checkpoint : BlockChain) : Prop where
  /-- The checkpoint's last header (`ObservedPreTip`): number `22431083` (the last Cancun block),
  timestamp `1746612299`, hash `0x28fb2c1d988435955e569451c6ad772f7fb5e61cddd7463c7b60e933ed5ff237`,
  stateRoot `0xab350e0fe349aef68947ede26295f8946c34ce3af5e3ec76f4b26ddeef29c0e3`. -/
  tip : ObservedPreTip checkpoint
  /-- `eth_getCode(0x0000F908…2935)`: the canonical 83 bytes. -/
  code : checkpoint.state.getCode addr = historyStorageCode
  /-- `eth_getCode(0xff…fe)` is empty. -/
  systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty

abbrev CheckpointObservation := HistoryStorageCheckpointObservation

/-! ## H-S1: the protocol's own call cannot fail -/

/-- **H-S1.** From any storage, with the code installed and a parent hash to pass, the block's unchecked system call
succeeds, writes exactly its one slot, returns nothing, and uses at most 22,143 of its 30,000,000 gas; and the
block-level call `historyStorageCall` succeeds on the same state. -/
def H_S1 : Prop :=
  ∀ (benv : Benv) (bal : BalBuilder) {lastHash : B256}
    -- the block's fork is Prague, Osaka, BPO1 or BPO2
    (_fork : CoveredFork benv.stat.fork)
    -- the canonical code is at the address
    (_installed : benv.state.getCode addr = historyStorageCode)
    -- the block has a parent: the hash the call passes (every block after genesis)
    (_last : benv.stat.blockHashes.getLast? = some lastHash),
    ∃ out, processUncheckedSystemTransaction benv addr lastHash.toBytes =
        .ok (benv.state.setStorVal addr (key benv.stat.number.toB256) lastHash, out) ∧
      RegularGasWithin out.gasLeft 22143 ∧ out.returnData = [] ∧
      ∃ bal', historyStorageCall benv.stat.rules benv bal =
        .ok (benv.state.setStorVal addr (key benv.stat.number.toB256) lastHash, bal')

/-- **H-S1 control** (the write clause, not totality). With empty code the unchecked call still succeeds, and from
storage whose slot does not already hold the hash its post state is not the written one. -/
def H_S1_control : Prop :=
  ∀ (benv : Benv) {lastHash : B256}
    -- a covered fork
    (_fork : CoveredFork benv.stat.fork)
    -- no code at the address: the only premise changed
    (_empty : benv.state.getCode addr = ByteArray.empty)
    -- the block has a parent
    (_last : benv.stat.blockHashes.getLast? = some lastHash)
    -- concrete initial words the real write changes
    (_differs : storOf benv.state addr (key benv.stat.number.toB256) ≠ lastHash),
    ∃ post out, processUncheckedSystemTransaction benv addr lastHash.toBytes = .ok (post, out) ∧
      post ≠ benv.state.setStorVal addr (key benv.stat.number.toB256) lastHash

/-! ## H-S2: what succeeds -/

/-- **H-S2.** Every settled frame at the address in a kept history from installed code is the system write or an
accepted 32-byte read, with the exact effects above. Nothing else succeeds. -/
def H_S2 : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- the kept history
    (_history : KeptHistory cfg start blocks stop)
    -- every block at a covered fork (no Amsterdam claim)
    (_covered : ∀ b ∈ blocks, CoveredFork b.fork)
    -- the canonical code at the address when the history starts
    (_code : start.state.getCode addr = historyStorageCode),
    ∀ f ∈ keptAtAddr addr blocks, Frame f

/-- **H-S2 control.** A frame of the canonical code from a non-system caller that fails the real window guard with
32 bytes, or that carries 31 bytes, every other entry condition kept, has no successful execution. -/
def H_S2_control : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm}
    -- the canonical code runs
    (_code : sevm.code = historyStorageCode)
    -- a covered fork
    (_fork : CoveredFork sevm.benvStat.fork)
    -- an ordinary caller
    (_caller : sevm.caller ≠ systemAddress)
    -- a fresh frame
    (_stack : pre.stack = [])
    -- the guard fails, or the length is wrong
    (_fails : (sevm.data.length = 32 ∧ ¬ InWindow sevm.benvStat.number.toB256 (Sevm.dataWord sevm 0)) ∨
      sevm.data.length = 31),
    IsEmpty (Exec 0 sevm pre (.ok post))

/-! ## H-S3: storage is exactly the history -/

/-- The conclusion of H-S3 and H-S4: the end storage is the start storage with every block's (number, parent
hash) written, in order. -/
def StorageIsHistory (start stop : BlockChain) (blocks : List KeptBlock) : Prop :=
  storOf stop.state addr = writeAll (storOf start.state addr) (blocks.map blockWrite)

/-- **H-S3.** Over every kept history from installed code with no privileged writer, the contract's storage is its
start storage with each block's parent hash written at its number's slot, in order. Numbering and parent hashes
are connected by `validateHeader` itself; no premise states it. -/
def H_S3 : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- the kept history
    (_history : KeptHistory cfg start blocks stop)
    -- every block at a covered fork
    (_covered : ∀ b ∈ blocks, CoveredFork b.fork)
    -- the canonical code at the start
    (_code : start.state.getCode addr = historyStorageCode)
    -- no code at SYSTEM_ADDRESS at the start
    (_systemEmpty : start.state.getCode systemAddress = ByteArray.empty)
    -- no SYSTEM_ADDRESS sender, authority or creation in any block
    (_clean : HistoryClean blocks),
    StorageIsHistory start stop blocks

/-- A runtime that, called, `CALL`s the contract with one 32-byte word `v`: `PUSH32 v PUSH0 MSTORE PUSH0 PUSH0
PUSH1 32 PUSH0 PUSH0 PUSH20 addr GAS CALL STOP`. Installed at SYSTEM_ADDRESS it is a privileged writer. -/
def writerCode (v : B256) : ByteArray :=
  ⟨([0x7f] ++ v.toBytes ++ [0x5f, 0x52, 0x5f, 0x5f, 0x60, 0x20, 0x5f, 0x5f, 0x73] ++ addr.toBytes ++
    [0x5a, 0xf1, 0x00]).toArray⟩

/-- **H-S3 control.** A closed kept history keeping every H-S3 premise except the empty code at SYSTEM_ADDRESS,
where a writer is installed instead, for which the recurrence fails. -/
def H_S3_control : Prop :=
  ∃ (cfg : ChainConfig) (start stop : BlockChain) (blocks : List KeptBlock) (v : B256),
    KeptHistory cfg start blocks stop ∧ (∀ b ∈ blocks, CoveredFork b.fork) ∧
    start.state.getCode addr = historyStorageCode ∧ HistoryClean blocks ∧
    start.state.getCode systemAddress = writerCode v ∧
    ¬ StorageIsHistory start stop blocks

/-! ## H-S4: rooted in a recorded mainnet fact -/

/-- **H-S4** (observation root). From the observed pre-Prague checkpoint 22,431,083, over every kept mainnet history
after it with no privileged writer, H-S3's conclusion. -/
def H_S4 : Prop :=
  ∀ {checkpoint final : BlockChain} {blocks : List KeptBlock}
    -- a kept mainnet history from the checkpoint
    (_history : KeptHistory mainnetChainConfig checkpoint blocks final)
    -- the observation record
    (_obs : HistoryStorageCheckpointObservation checkpoint)
    -- no SYSTEM_ADDRESS sender, authority or creation in any block
    (_clean : HistoryClean blocks),
    StorageIsHistory checkpoint final blocks

/-! ## H-S6: value is kept -/

/-- **H-S6.** Over every kept history from installed code, the contract's end balance is at least its start balance
plus the value every settled frame at it carried; the bytes have no value-sending path. -/
def H_S6 : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- the kept history
    (_history : KeptHistory cfg start blocks stop)
    -- every block at a covered fork
    (_covered : ∀ b ∈ blocks, CoveredFork b.fork)
    -- the canonical code at the start
    (_code : start.state.getCode addr = historyStorageCode)
    -- no transaction is sent from the contract's address
    (_noSender : ∀ b ∈ blocks, NoSenderAt addr b.run.senders)
    -- every root message opens on a world whose balances sum below 2^256 (as B2's `value_kept`)
    (_roots : HistoryRootsFit blocks)
    -- no tip or withdrawal credit to the contract wraps its balance (as B2's `value_kept`)
    (_credits : HistoryCreditsFit addr blocks),
    (start.state.bal addr).toNat + ((keptAtAddr addr blocks).map fun f => f.sevm.value.toNat).sum ≤
      (stop.state.bal addr).toNat

/-! ## H-S7: a correct call works -/

/-- **H-S7.** A fresh frame of the canonical code from a non-system caller, 32 bytes, the window guard passing, with
at least `readGas` gas, succeeds, charging exactly `readGas`, returning the slot's word, and changing no account. -/
def H_S7 : Prop :=
  ∀ {sevm : Sevm} {pre : Devm}
    -- the canonical code runs
    (_code : sevm.code = historyStorageCode)
    -- a covered fork
    (_fork : CoveredFork sevm.benvStat.fork)
    -- an ordinary caller
    (_caller : sevm.caller ≠ systemAddress)
    -- exactly 32 bytes
    (_length : sevm.data.length = 32)
    -- a fresh frame
    (_stack : pre.stack = []) (_memory : pre.memory = .empty)
    -- the window guard passes
    (_window : InWindow sevm.benvStat.number.toB256 (Sevm.dataWord sevm 0))
    -- enough gas
    (_gas : readGas pre sevm.currentTarget (Sevm.dataWord sevm 0) ≤ pre.gasLeft),
    ∃ post, Nonempty (Exec 0 sevm pre (.ok post)) ∧
      post.gasLeft = pre.gasLeft - readGas pre sevm.currentTarget (Sevm.dataWord sevm 0) ∧
      post.output = ((Devm.getStor pre sevm.currentTarget).get (Sevm.dataWord sevm 0 % ring)).toBytes ∧
      post.state = pre.state

/-! ## H-S8: a written hash stays readable for its window -/

/-- **H-S8.** For the hash block `i`'s protocol call wrote (of block `n = number_i - 1`), under the model-fidelity
word-fit bound `number_i + 8191 < 2 ^ 256` (compare `HistoryNumbersFit`): during every later block of number at most
`n + 8191` (inclusive of block `i`), a read of `n` returns it; from block `n + 8192` on the query reverts, whatever
is stored; and an in-window read of a slot no call wrote returns that slot's contents. -/
def H_S8 : Prop :=
  (∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- the kept history
    (_history : KeptHistory cfg start blocks stop)
    -- every block at a covered fork
    (_covered : ∀ b ∈ blocks, CoveredFork b.fork)
    -- the canonical code at the start
    (_code : start.state.getCode addr = historyStorageCode)
    -- no code at SYSTEM_ADDRESS at the start
    (_systemEmpty : start.state.getCode systemAddress = ByteArray.empty)
    -- no SYSTEM_ADDRESS sender, authority or creation in any block
    (_clean : HistoryClean blocks),
    ∀ i (hi : i < blocks.length),
      -- the window's numbers fit in a word (Jaune's header validation bounds no number)
      blocks[i].block.header.number + 8191 < 2 ^ 256 →
      (∀ j (hj : j < blocks.length), i ≤ j →
        blocks[j].block.header.number ≤ blocks[i].block.header.number - 1 + 8191 →
        read (storOf blocks[j].run.preState addr) blocks[j].block.header.number.toB256
          (blocks[i].block.header.number - 1).toB256 = some blocks[i].block.header.parentHash) ∧
      (∀ (s : B256 → B256) (m : Nat), blocks[i].block.header.number - 1 + 8192 ≤ m → m < 2 ^ 256 →
        read s m.toB256 (blocks[i].block.header.number - 1).toB256 = none)) ∧
  ∀ (s : B256 → B256) (N q : B256), InWindow N q → read s N q = some (s (q % ring))

/-- **H-S8 control (retention).** A closed kept history keeping every H-S8 premise (including `HistoryNumbersFit`
so block numbers in the window do not wrap modulo `2 ^ 256`) except empty code at `SYSTEM_ADDRESS`, where a
privileged writer is installed instead, in which an in-window read of a protocol-written block number returns
`some wrongValue` with `wrongValue ≠ parentHash` (a genuine retention corruption, not an out-of-window `none`). -/
def H_S8_control : Prop :=
  ∃ (cfg : ChainConfig) (start stop : BlockChain) (blocks : List KeptBlock) (v : B256),
    KeptHistory cfg start blocks stop ∧ (∀ b ∈ blocks, CoveredFork b.fork) ∧
    start.state.getCode addr = historyStorageCode ∧ HistoryClean blocks ∧
    HistoryNumbersFit blocks ∧
    start.state.getCode systemAddress = writerCode v ∧
    ∃ (i j : Nat) (hi : i < blocks.length) (hj : j < blocks.length) (wrongValue : B256),
      blocks[i].block.header.number + 8191 < 2 ^ 256 ∧
      i ≤ j ∧
      blocks[j].block.header.number ≤ blocks[i].block.header.number - 1 + 8191 ∧
      InWindow blocks[j].block.header.number.toB256 (blocks[i].block.header.number - 1).toB256 ∧
      read (storOf blocks[j].run.preState addr) blocks[j].block.header.number.toB256
        (blocks[i].block.header.number - 1).toB256 = some wrongValue ∧
      wrongValue ≠ blocks[i].block.header.parentHash

/-! ## H-S9: what the chain reads is the history's block hash -/

/-- **H-S9, chain form.** Over a kept history with no privileged writer, during every block in the window of an
entry written by block `i`, a read of the number one below block `i`'s returns the hash of this history's block of
that number: the previous kept block, or the start's tip. No ancestry beyond this history is claimed. -/
def H_S9 : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- the kept history
    (_history : KeptHistory cfg start blocks stop)
    -- every block at a covered fork
    (_covered : ∀ b ∈ blocks, CoveredFork b.fork)
    -- the canonical code at the start
    (_code : start.state.getCode addr = historyStorageCode)
    -- no code at SYSTEM_ADDRESS at the start
    (_systemEmpty : start.state.getCode systemAddress = ByteArray.empty)
    -- no SYSTEM_ADDRESS sender, authority or creation in any block
    (_clean : HistoryClean blocks),
    ∀ i (hi : i < blocks.length),
      -- the window's numbers fit in a word
      blocks[i].block.header.number + 8191 < 2 ^ 256 →
      ∃ hdr, prevHeader start blocks i = some hdr ∧ hdr.number + 1 = blocks[i].block.header.number ∧
        ∀ j (hj : j < blocks.length), i ≤ j → blocks[j].block.header.number ≤ hdr.number + 8191 →
          read (storOf blocks[j].run.preState addr) blocks[j].block.header.number.toB256 hdr.number.toB256 =
            some hdr.hash

/-- **H-S9 control (chain form: the parent-hash input).** When a block builds on a parent chain with tip `t`
(`expectedHash = t.header.hash`, `header.number = t.header.number + 1`), mutating the parent-hash input passed to the
history-storage call to `mutatedHash ≠ t.header.hash` writes `mutatedHash` into `key header.number` so both the stored
word and the in-window read of `t.header.number` differ from `t.header.hash`, falsifying H-S9's block-hash equality. -/
def H_S9_control : Prop :=
  ∀ (parent : BlockChain) (t : Block) (fork : Jaune.Fork) (header : Header) (bal : BalBuilder) (mutatedHash : B256)
    -- the parent chain's tip block (whose hash H-S9 expects to read back)
    (_tip : parent.blocks.getLast? = some t)
    -- consecutive block number, within the word-fit bound
    (_num : header.number = t.header.number + 1)
    (_fit : header.number + 8191 < 2 ^ 256)
    -- a covered fork
    (_fork : CoveredFork fork)
    -- the canonical code at the parent
    (_installed : parent.state.getCode addr = historyStorageCode)
    -- the mutated input differs from the parent tip's hash
    (_ne : mutatedHash ≠ t.header.hash),
    let benv := initBenv fork parent header
    let mutatedBenv : Benv := { benv with stat := { benv.stat with blockHashes := [mutatedHash] } }
    ∃ st bal',
      historyStorageCall mutatedBenv.stat.rules mutatedBenv bal = .ok (st, bal') ∧
      storOf st addr (key header.number.toB256) = mutatedHash ∧
      storOf st addr (key header.number.toB256) ≠ t.header.hash ∧
      read (storOf st addr) header.number.toB256 t.header.number.toB256 = some mutatedHash ∧
      read (storOf st addr) header.number.toB256 t.header.number.toB256 ≠ some t.header.hash

/-- **H-S9, joint form.** On the joint chain, after each step the contract holds, at the slot of the step's payload
number, the execution block hash the beacon state recorded for the previous payload
(`latest_execution_payload_header.block_hash`, which `process_execution_payload` matches against the payload's
`parent_hash`). It claims no ancestry or canonicality beyond that record. -/
def H_S9_joint : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P}
    -- the joint-chain premises
    (v : RingJoint cfg ccfg bls addr historyStorageCode checkpoint anchor final),
    ∀ st ∈ v.run.steps,
      storOf st.post.exec.state addr (key (stepNumber st).toB256) =
        st.pre.beacon.latest_execution_payload_header.block_hash

/-- **H-S9 control (joint form: the consensus-recorded payload hash).** When the parent-hash input passed to the
converted payload block's history-storage call is mutated to `mutatedHash ≠ beacon.latest_execution_payload_header.block_hash`,
the call stores `mutatedHash` at `key block_number` and the stored word differs from the beacon state's recorded
previous payload hash, falsifying `H_S9_joint`'s equality. -/
def H_S9_joint_control : Prop :=
  ∀ {P : Preset} {f : CFork} (beacon : BeaconState P f) (req : NewPayloadRequest P) (fork : Jaune.Fork)
    (parent : BlockChain) (bal : BalBuilder) (mutatedHash : B256)
    -- a covered fork
    (_fork : CoveredFork fork)
    -- the canonical code at the parent
    (_installed : parent.state.getCode addr = historyStorageCode)
    -- the mutated input differs from the beacon state's recorded previous payload block_hash
    (_ne : mutatedHash ≠ beacon.latest_execution_payload_header.block_hash),
    let hdr := (payloadToBlock req).header
    let benv := initBenv fork parent hdr
    let mutatedBenv : Benv := { benv with stat := { benv.stat with blockHashes := [mutatedHash] } }
    ∃ st bal',
      historyStorageCall mutatedBenv.stat.rules mutatedBenv bal = .ok (st, bal') ∧
      storOf st addr (key req.executionPayload.block_number.toNat.toB256) = mutatedHash ∧
      storOf st addr (key req.executionPayload.block_number.toNat.toB256) ≠
        beacon.latest_execution_payload_header.block_hash

/-! ## H-S10: the next fork does not break the protocol's call -/

/-- **H-S10.** H-S1 at Amsterdam: from any storage, with the code installed and a parent hash, the unchecked call
succeeds, writes exactly its slot, and uses at most 15,000 regular gas (its state gas, at most one `STORAGE_SET`,
comes from the system reservoir); the block-level call succeeds on the same state. -/
def H_S10 : Prop :=
  ∀ (benv : Benv) (bal : BalBuilder) {lastHash : B256}
    -- the block's fork is Amsterdam
    (_fork : benv.stat.fork = .amsterdam)
    -- the canonical code is at the address
    (_installed : benv.state.getCode addr = historyStorageCode)
    -- the block has a parent
    (_last : benv.stat.blockHashes.getLast? = some lastHash),
    ∃ out, processUncheckedSystemTransaction benv addr lastHash.toBytes =
        .ok (benv.state.setStorVal addr (key benv.stat.number.toB256) lastHash, out) ∧
      RegularGasWithin out.gasLeft 15000 ∧
      ∃ bal', historyStorageCall benv.stat.rules benv bal =
        .ok (benv.state.setStorVal addr (key benv.stat.number.toB256) lastHash, bal')

end Blanc.Corpus.Freeze.HistoryStorage
