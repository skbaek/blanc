import Blanc.Corpus.Freeze.RingCommon

/-!
# G0 freeze: the EIP-4788 beacon-roots cells (R-S1 .. R-S10)

Each cell is a `Prop` definition; the later proof is `theorem r_sN : R_SN`. Every premise is a named binder with a
one-line comment. Statements are read from the 97 bytes of `Blanc.beaconRootsCode` (`Blanc/SystemContracts.lean:35`)
as the lifted certificate splits them (`Blanc/Lift/SystemExecution/BeaconRoots/Cert.lean`):

* `0x00`: `CALLER == SYSTEM_ADDRESS` jumps to the write at `0x4d`;
* write (`0x4d`): `sstore(T mod 8191, T)`, `sstore(8191 + T mod 8191, calldataload(0))`, `STOP`, with
  `T = TIMESTAMP`; no `CALLDATASIZE` check, so short input is zero-padded and excess ignored;
* read: `CALLDATASIZE == 32`, else revert; `t = calldataload(0)`; `t == 0` reverts; `sload(t mod 8191) == t`,
  else revert; return the 32-byte word `sload(8191 + t mod 8191)`. No `CALLVALUE` check anywhere and no age check.

History statements range over kept histories (`Blanc.KeptHistory`) and their settled frames (`keptAtAddr`), and
take `CoveredFork` for every block: nothing is claimed at Amsterdam except R-S10.
-/

namespace Blanc.Corpus.Freeze.BeaconRoots

open Jaune Blanc ExecutionTrace JauneConsensus
open Blanc.Corpus.Freeze
open Blanc.Lift.RequestSystem (RegularGasWithin)

/-! ## Vocabulary read from the bytes -/

/-- The contract's address. -/
abbrev addr : Adr := beaconRootsAddress

/-- The timestamp slot of a write or read at `t`: `t mod 8191`. -/
def timeKey (t : B256) : B256 := t % ring

/-- The root slot of a write or read at `t`: `8191 + t mod 8191` (the bytes' `ADD` order). -/
def rootKey (t : B256) : B256 := ring + timeKey t

/-- Storage after the system write at timestamp `T` of the word `v`: `T` at `timeKey T`, then `v` at
`rootKey T` (the two keys differ, `SystemWalk.systemKey_ne`). -/
def write (s : B256 → B256) (T v : B256) : B256 → B256 :=
  fun k => if k = rootKey T then v else if k = timeKey T then T else s k

/-- Storage after a list of system writes, in order. -/
def writeAll (s : B256 → B256) : List (B256 × B256) → B256 → B256
  | [] => s
  | (T, v) :: ws => writeAll (write s T v) ws

/-- The world after the system write: the same two stores, at the contract's address. -/
def writeState (w : State) (T v : B256) : State :=
  (w.setStorVal addr (timeKey T) T).setStorVal addr (rootKey T) v

/-- What the bytes' read at `t` returns from storage `s`: the root slot when `t ≠ 0` and the tag at
`timeKey t` is `t`; `none` where the bytes revert. -/
def read (s : B256 → B256) (t : B256) : Option B256 :=
  if t ≠ 0 ∧ s (timeKey t) = t then some (s (rootKey t)) else none

/-- The pair a kept block's protocol call writes: its header timestamp and parent beacon root, as
`initBenvStat` reads them (`time := header.timestamp.toB256`, `parentBeaconBlockRoot := ….getD 0`). -/
def blockWrite (b : KeptBlock) : B256 × B256 :=
  (b.block.header.timestamp.toB256, b.block.header.parentBeaconBlockRoot.getD 0)

/-- The protocol's own call: SYSTEM_ADDRESS, any calldata length, non-static; it stores the timestamp tag and
`calldataload(0)`, returns nothing, emits nothing. -/
structure SystemWrite (f : Exec.Frame) : Prop where
  caller : f.sevm.caller = systemAddress
  nonstatic : f.sevm.isStatic = false
  state : f.post.state =
    (f.pre.state.setStorVal f.sevm.currentTarget (timeKey f.sevm.benvStat.time) f.sevm.benvStat.time).setStorVal
      f.sevm.currentTarget (rootKey f.sevm.benvStat.time) (Sevm.dataWord f.sevm 0)
  output : f.post.output = []
  logs : f.post.logs = f.pre.logs

/-- An ordinary read: any other caller, exactly 32 bytes, the read guard passes; it returns the stored word,
changes no account (the value it was sent stays with the contract), emits nothing. -/
structure Read (f : Exec.Frame) : Prop where
  caller : f.sevm.caller ≠ systemAddress
  length : f.sevm.data.length = 32
  accepts : ∃ w, read (frameStor f) (Sevm.dataWord f.sevm 0) = some w ∧ f.post.output = w.toBytes
  state : f.post.state = f.pre.state
  logs : f.post.logs = f.pre.logs

/-- The named list of successes. -/
def Frame (f : Exec.Frame) : Prop := SystemWrite f ∨ Read f

/-- The gas of one `SLOAD` of `k` at `a` from a frame's access set (EIP-2929). -/
def sloadGas (pre : Devm) (a : Adr) (k : B256) : Nat :=
  if (a, k) ∈ pre.accessedStorageKeys then gasWarmAccess else gasColdSload

/-- The exact gas of the accepted read path: 120 for its 33 non-`SLOAD` steps (two `JUMPDEST`s, four `JUMPI`s, the
`MSTORE` with its one-word expansion, `RETURN` at 0), plus each `SLOAD`'s warm or cold charge. The second key
differs from the first, so its warmth is the frame's own. -/
def readGas (pre : Devm) (a : Adr) (t : B256) : Nat :=
  120 + sloadGas pre a (timeKey t) + sloadGas pre a (rootKey t)

/-! ## The observation record (R-S4) -/

/-- **R-S4's root**: what an observed pre-Prague checkpoint must hold for the R statements. Each field is a public
JSON-RPC read at block 22,431,083; Lean does not authenticate them against the state root. Both reads already
appear in registered records: `beaconAtP` of `WithdrawalDeploymentObservation` and `systemEmpty` of
`ConsolidationCheckpointObservation`. -/
structure CheckpointObservation (checkpoint : BlockChain) : Prop where
  /-- The checkpoint's last header: number 22,431,083 (the last Cancun block), hash 0x28fb…f237. -/
  tip : ObservedPreTip checkpoint
  /-- `eth_getCode(0x000F…Beac02)`: the canonical 97 bytes. -/
  code : checkpoint.state.getCode addr = beaconRootsCode
  /-- `eth_getCode(0xff…fe)` is empty. -/
  systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty

/-! ## R-S1: the protocol's own call cannot fail -/

/-- **R-S1.** From any storage, with the code installed, the block's unchecked system call with the parent beacon
root succeeds, writes exactly its two slots and nothing else, returns nothing, and uses at most 44,251 of its
30,000,000 gas; and the block-level call `beaconRootsCall` succeeds on the same state. -/
def R_S1 : Prop :=
  ∀ (benv : Benv)
    -- the block's fork is Prague, Osaka, BPO1 or BPO2
    (_fork : CoveredFork benv.stat.fork)
    -- the canonical code is at the address
    (_installed : benv.state.getCode addr = beaconRootsCode),
    ∃ out, processUncheckedSystemTransaction benv addr benv.stat.parentBeaconBlockRoot.toBytes =
        .ok (writeState benv.state benv.stat.time benv.stat.parentBeaconBlockRoot, out) ∧
      RegularGasWithin out.gasLeft 44251 ∧ out.returnData = [] ∧
      ∃ bal, beaconRootsCall benv.stat.rules benv =
        .ok (writeState benv.state benv.stat.time benv.stat.parentBeaconBlockRoot, bal)

/-- **R-S1 control** (the write clause, not totality). With empty code at the address the unchecked call still
succeeds, and from storage whose tag slot does not already hold `T` its post state is not the written one. -/
def R_S1_control : Prop :=
  ∀ (benv : Benv)
    -- a covered fork
    (_fork : CoveredFork benv.stat.fork)
    -- no code at the address: the only premise changed
    (_empty : benv.state.getCode addr = ByteArray.empty)
    -- concrete initial words the real write changes
    (_differs : storOf benv.state addr (timeKey benv.stat.time) ≠ benv.stat.time),
    ∃ post out, processUncheckedSystemTransaction benv addr benv.stat.parentBeaconBlockRoot.toBytes =
        .ok (post, out) ∧
      post ≠ writeState benv.state benv.stat.time benv.stat.parentBeaconBlockRoot

/-! ## R-S2: what succeeds -/

/-- **R-S2.** Every settled frame at the address in a kept history from installed code is the system write or an
accepted 32-byte read, with the exact effects above. Nothing else succeeds. -/
def R_S2 : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- the kept history: successful transitions at kept forks with their retained stages
    (_history : KeptHistory cfg start blocks stop)
    -- every block at a covered fork (no Amsterdam claim)
    (_covered : ∀ b ∈ blocks, CoveredFork b.fork)
    -- the canonical code at the address when the history starts
    (_code : start.state.getCode addr = beaconRootsCode),
    ∀ f ∈ keptAtAddr addr blocks, Frame f

/-- **R-S2 control.** A frame of the canonical code from a non-system caller that fails the real tag guard (or
`t = 0`) with 32 bytes, or that carries 31 bytes, every other entry condition kept, has no successful execution. -/
def R_S2_control : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm}
    -- the canonical code runs
    (_code : sevm.code = beaconRootsCode)
    -- a covered fork
    (_fork : CoveredFork sevm.benvStat.fork)
    -- an ordinary caller
    (_caller : sevm.caller ≠ systemAddress)
    -- a fresh frame
    (_stack : pre.stack = [])
    -- the guard fails, or the length is wrong
    (_fails : (sevm.data.length = 32 ∧
        read (Devm.getStor pre sevm.currentTarget).get (Sevm.dataWord sevm 0) = none) ∨
      sevm.data.length = 31),
    IsEmpty (Exec 0 sevm pre (.ok post))

/-! ## R-S3: storage is exactly the history -/

/-- The conclusion of R-S3 and R-S4: the end storage is the start storage with every block's write applied, in
order; and a positive timestamp written in the history and not overwritten reads back its root. -/
def StorageIsHistory (start stop : BlockChain) (blocks : List KeptBlock) : Prop :=
  storOf stop.state addr = writeAll (storOf start.state addr) (blocks.map blockWrite) ∧
    ∀ i (hi : i < blocks.length), (blockWrite blocks[i]).1 ≠ 0 →
      (∀ j (hj : j < blocks.length), i < j →
        timeKey (blockWrite blocks[j]).1 ≠ timeKey (blockWrite blocks[i]).1) →
      read (storOf stop.state addr) (blockWrite blocks[i]).1 = some (blockWrite blocks[i]).2

/-- **R-S3.** Over every kept history from installed code with no privileged writer, the contract's storage is
its start storage with each block's (timestamp, parent beacon root) written, in order. Root contents are carried,
not authenticated. -/
def R_S3 : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- the kept history
    (_history : KeptHistory cfg start blocks stop)
    -- every block at a covered fork
    (_covered : ∀ b ∈ blocks, CoveredFork b.fork)
    -- the canonical code at the start
    (_code : start.state.getCode addr = beaconRootsCode)
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

/-- **R-S3 control.** A closed kept history keeping every R-S3 premise except the empty code at SYSTEM_ADDRESS,
where a writer is installed instead, for which the recurrence fails: the writer stores a root no header carried. -/
def R_S3_control : Prop :=
  ∃ (cfg : ChainConfig) (start stop : BlockChain) (blocks : List KeptBlock) (v : B256),
    KeptHistory cfg start blocks stop ∧ (∀ b ∈ blocks, CoveredFork b.fork) ∧
    start.state.getCode addr = beaconRootsCode ∧ HistoryClean blocks ∧
    start.state.getCode systemAddress = writerCode v ∧
    storOf stop.state addr ≠ writeAll (storOf start.state addr) (blocks.map blockWrite)

/-! ## R-S4: rooted in a recorded mainnet fact -/

/-- **R-S4** (observation root). From the observed pre-Prague checkpoint 22,431,083, over every kept mainnet history
after it with no privileged writer, R-S3's conclusion. Mainnet's schedule names no Amsterdam activation, so the
covered-fork premise is discharged (as `ConsolidationRequestPublic.mainnet_covered`). -/
def R_S4 : Prop :=
  ∀ {checkpoint final : BlockChain} {blocks : List KeptBlock}
    -- a kept mainnet history from the checkpoint
    (_history : KeptHistory mainnetChainConfig checkpoint blocks final)
    -- the observation record
    (_obs : CheckpointObservation checkpoint)
    -- no SYSTEM_ADDRESS sender, authority or creation in any block
    (_clean : HistoryClean blocks),
    StorageIsHistory checkpoint final blocks

/-! ## R-S6: value is kept -/

/-- **R-S6.** Over every kept history from installed code, the contract's end balance is at least its start
balance plus the value every settled frame at it carried; the bytes have no value-sending path. -/
def R_S6 : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- the kept history
    (_history : KeptHistory cfg start blocks stop)
    -- every block at a covered fork
    (_covered : ∀ b ∈ blocks, CoveredFork b.fork)
    -- the canonical code at the start
    (_code : start.state.getCode addr = beaconRootsCode)
    -- no transaction is sent from the contract's address
    (_noSender : ∀ b ∈ blocks, NoSenderAt addr b.run.senders)
    -- every root message opens on a world whose balances sum below 2^256 (as B2's `value_kept`)
    (_roots : HistoryRootsFit blocks)
    -- no tip or withdrawal credit to the contract wraps its balance (as B2's `value_kept`)
    (_credits : HistoryCreditsFit addr blocks),
    (start.state.bal addr).toNat + ((keptAtAddr addr blocks).map fun f => f.sevm.value.toNat).sum ≤
      (stop.state.bal addr).toNat

/-! ## R-S7: a correct call works -/

/-- **R-S7.** A fresh frame of the canonical code from a non-system caller, 32 bytes of calldata, the read guard
passing, with at least `readGas` gas, succeeds, charging exactly `readGas`, returning the stored word, and changing
no account. -/
def R_S7 : Prop :=
  ∀ {sevm : Sevm} {pre : Devm} {w : B256}
    -- the canonical code runs
    (_code : sevm.code = beaconRootsCode)
    -- a covered fork
    (_fork : CoveredFork sevm.benvStat.fork)
    -- an ordinary caller
    (_caller : sevm.caller ≠ systemAddress)
    -- exactly 32 bytes
    (_length : sevm.data.length = 32)
    -- a fresh frame
    (_stack : pre.stack = []) (_memory : pre.memory = .empty)
    -- the read guard passes, returning `w`
    (_accepts : read (Devm.getStor pre sevm.currentTarget).get (Sevm.dataWord sevm 0) = some w)
    -- enough gas
    (_gas : readGas pre sevm.currentTarget (Sevm.dataWord sevm 0) ≤ pre.gasLeft),
    ∃ post, Nonempty (Exec 0 sevm pre (.ok post)) ∧
      post.gasLeft = pre.gasLeft - readGas pre sevm.currentTarget (Sevm.dataWord sevm 0) ∧
      post.output = w.toBytes ∧ post.state = pre.state

/-! ## R-S8: a buffered root stays readable for a stated window -/

/-- **R-S8, generic time.** A positive timestamp written by a block of a kept history reads back its root at the end
of the history, if every later block's timestamp is below it plus 8191. Timestamps strictly increase
(`validateHeader`), so no later block in that window can overwrite its index. -/
def R_S8_time : Prop :=
  ∀ {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    -- the kept history
    (_history : KeptHistory cfg start blocks stop)
    -- every block at a covered fork
    (_covered : ∀ b ∈ blocks, CoveredFork b.fork)
    -- the canonical code at the start
    (_code : start.state.getCode addr = beaconRootsCode)
    -- no code at SYSTEM_ADDRESS at the start
    (_systemEmpty : start.state.getCode systemAddress = ByteArray.empty)
    -- no SYSTEM_ADDRESS sender, authority or creation in any block
    (_clean : HistoryClean blocks),
    ∀ i (hi : i < blocks.length), (blockWrite blocks[i]).1 ≠ 0 →
      -- the window's timestamps fit in a word (Jaune's header validation bounds no timestamp)
      blocks[i].block.header.timestamp + 8191 ≤ 2 ^ 256 →
      (∀ j (hj : j < blocks.length), i < j →
        blocks[j].block.header.timestamp < blocks[i].block.header.timestamp + 8191) →
      read (storOf stop.state addr) (blockWrite blocks[i]).1 = some (blockWrite blocks[i]).2

/-- **R-S8 generic-time control.** A closed kept history meeting every R-S8 premise, with a block exactly 8191
seconds after a positive write, in which the read of that write fails. -/
def R_S8_time_control : Prop :=
  ∃ (cfg : ChainConfig) (start stop : BlockChain) (blocks : List KeptBlock),
    KeptHistory cfg start blocks stop ∧ (∀ b ∈ blocks, CoveredFork b.fork) ∧
    start.state.getCode addr = beaconRootsCode ∧ start.state.getCode systemAddress = ByteArray.empty ∧
    HistoryClean blocks ∧
    ∃ (i j : Nat) (hi : i < blocks.length) (hj : j < blocks.length), i < j ∧ (blockWrite blocks[i]).1 ≠ 0 ∧
      blocks[j].block.header.timestamp = blocks[i].block.header.timestamp + 8191 ∧
      read (storOf stop.state addr) (blockWrite blocks[i]).1 = none

/-- **R-S8, slot grid.** On a joint run, with the slot duration a whole number of seconds not divisible by 8191 (12 s
on mainnet; `gcd(12, 8191) = 1`), the root written by a step reads back at the end of the run if every later step
is fewer than 8191 slots later (98,292 s at 12 s). Both conditions are facts of the selected consensus
configuration, decided for the mainnet one. -/
def R_S8_slot : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P}
    -- the joint-chain premises
    (v : RingJoint cfg ccfg bls addr beaconRootsCode checkpoint anchor final)
    -- the configured slot duration is whole seconds
    (_whole : ccfg.SLOT_DURATION_MS % 1000 = 0)
    -- and 8191 does not divide it
    (_coprime : ¬ 8191 ∣ ccfg.SLOT_DURATION_MS / 1000),
    ∀ i (hi : i < v.run.steps.length),
      (∀ j (hj : j < v.run.steps.length), i < j → stepSlot v.run.steps[j] < stepSlot v.run.steps[i] + 8191) →
      read (storOf final.exec.state addr) (stepTime v.run.steps[i]) =
        some v.run.steps[i].block.2.message.parent_root

/-- **R-S8 slot-grid control (mechanism form).** On any slot grid of `d` whole seconds, a write 8191 slots later
lands on the same index and kills the read, whatever was stored. A joint-chain witness is out of reach (G0 report). -/
def R_S8_slot_control : Prop :=
  ∀ (s : B256 → B256) (genesis d slot : Nat) (v v' : B256),
    -- a positive timestamp on the grid
    0 < genesis + d * slot →
    -- both timestamps fit in a word
    genesis + d * (slot + 8191) < 2 ^ 64 →
    -- a positive slot duration
    0 < d →
    read (writeAll s [((genesis + d * slot).toB256, v), ((genesis + d * (slot + 8191)).toB256, v')])
      (genesis + d * slot).toB256 = none

/-! ## R-S9: consensus does what the contract recorded -/

/-- The root of a beacon state's latest block header as the next `process_slot` completes it: an unfilled
`state_root` (zero, as `process_block_header` leaves it) becomes the state's own root. -/
def filledHeaderRoot {P : Preset} {f : CFork} (s : BeaconState P f) : B256 :=
  Ssz.hashTreeRoot (if s.latest_block_header.state_root = 0 then
    { s.latest_block_header with state_root := Ssz.hashTreeRoot s } else s.latest_block_header)

/-- **R-S9.** On the joint chain, after each step the contract holds the step's payload timestamp and its beacon
block's `parent_root` (through `NewPayloadRequest.ofBlock`), so a read at that timestamp returns it; and that
`parent_root` is the root of the previous block on this anchored history, or of the anchor's latest header at the
first step (filled by the first `process_slot` when the step processes one; a crossing step from an Electra anchor
already at the Fulu fork slot, `atSlot`, processes none). Chain-relative: no canonicality is claimed. -/
def R_S9 : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P}
    -- the joint-chain premises
    (v : RingJoint cfg ccfg bls addr beaconRootsCode checkpoint anchor final),
    (∀ st ∈ v.run.steps,
      storOf st.post.exec.state addr (timeKey (stepTime st)) = stepTime st ∧
      storOf st.post.exec.state addr (rootKey (stepTime st)) = st.block.2.message.parent_root ∧
      (stepTime st ≠ 0 → read (storOf st.post.exec.state addr) (stepTime st) = some st.block.2.message.parent_root)) ∧
    (∀ h : 0 < v.run.steps.length,
      (v.run.steps[0]'h).block.2.message.parent_root =
        if anchor.beacon.slot.toNat < stepSlot (v.run.steps[0]'h) then filledHeaderRoot anchor.beacon
        else Ssz.hashTreeRoot anchor.beacon.latest_block_header) ∧
    (∀ k (hk : k + 1 < v.run.steps.length),
      v.run.steps[k + 1].block.2.message.parent_root = Ssz.hashTreeRoot v.run.steps[k].block.2.message)

/-- **R-S9 control.** The stored root is whatever the conversion passes: for any request with its parent root
replaced by `r`, the converted block's own call stores `r`. So R-S9's equation rests on `ofBlock` passing
`parent_root`. -/
def R_S9_control : Prop :=
  ∀ {P : Preset} (req : NewPayloadRequest P) (r : B256) (fork : Jaune.Fork) (parent : BlockChain)
    -- a covered fork
    (_fork : CoveredFork fork)
    -- the canonical code at the parent
    (_code : parent.state.getCode addr = beaconRootsCode),
    ∃ st bal,
      beaconRootsCall fork.ruleSet
          (initBenv fork parent (payloadToBlock { req with parentBeaconBlockRoot := r }).header) = .ok (st, bal) ∧
        storOf st addr (rootKey (payloadToBlock { req with parentBeaconBlockRoot := r }).header.timestamp.toB256) = r

/-! ## R-S10: the next fork does not break the protocol's call -/

/-- **R-S10.** R-S1 at Amsterdam: from any storage, with the code installed, the unchecked call with the parent
beacon root succeeds, writes exactly its two slots, and uses at most 30,000 regular gas (its state gas, at most two
`STORAGE_SET`s, comes from the system reservoir of 16); the block-level call succeeds on the same state. -/
def R_S10 : Prop :=
  ∀ (benv : Benv)
    -- the block's fork is Amsterdam
    (_fork : benv.stat.fork = .amsterdam)
    -- the canonical code is at the address
    (_installed : benv.state.getCode addr = beaconRootsCode),
    ∃ out, processUncheckedSystemTransaction benv addr benv.stat.parentBeaconBlockRoot.toBytes =
        .ok (writeState benv.state benv.stat.time benv.stat.parentBeaconBlockRoot, out) ∧
      RegularGasWithin out.gasLeft 30000 ∧
      ∃ bal, beaconRootsCall benv.stat.rules benv =
        .ok (writeState benv.state benv.stat.time benv.stat.parentBeaconBlockRoot, bal)

end Blanc.Corpus.Freeze.BeaconRoots
