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
JSON-RPC read at block 22,431,083; Lean does not authenticate them against the state root. All underlying reads already
appear in registered records (`checkpointTip` and `beaconAtP` of `WithdrawalDeploymentObservation`, `systemEmpty` of
`ConsolidationCheckpointObservation`); packaging them as `BeaconRootsCheckpointObservation` is submitted for user
adoption as registered provenance (§5/§9). -/
structure BeaconRootsCheckpointObservation (checkpoint : BlockChain) : Prop where
  /-- The checkpoint's last header (`ObservedPreTip`): number `22431083` (the last Cancun block),
  timestamp `1746612299`, hash `0x28fb2c1d988435955e569451c6ad772f7fb5e61cddd7463c7b60e933ed5ff237`,
  stateRoot `0xab350e0fe349aef68947ede26295f8946c34ce3af5e3ec76f4b26ddeef29c0e3`. -/
  tip : ObservedPreTip checkpoint
  /-- `eth_getCode(0x000F…Beac02)`: the canonical 97 bytes. -/
  code : checkpoint.state.getCode addr = beaconRootsCode
  /-- `eth_getCode(0xff…fe)` is empty. -/
  systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty

abbrev CheckpointObservation := BeaconRootsCheckpointObservation

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
    (_obs : BeaconRootsCheckpointObservation checkpoint)
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
of the history, if every later block's timestamp is below it plus 8191 and the window fits below `2 ^ 256`
(model-fidelity word-fit condition; compare `HistoryTimestampsFit`). Timestamps strictly increase (`validateHeader`),
so no later block in that window can overwrite its index. -/
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

/-- **R-S8 generic-time control.** A closed kept history meeting every R-S8 premise (including `HistoryTimestampsFit`
so no timestamp wraps modulo `2 ^ 256`), with a later block at timestamp `t + 8191` after a positive write at `t`,
in which the ring slot's timestamp tag at `timeKey t` was overwritten by `(t + 8191) ≠ t` and the read of `t` at the
end of the history therefore fails (`none` / reverts). -/
def R_S8_time_control : Prop :=
  ∃ (cfg : ChainConfig) (start stop : BlockChain) (blocks : List KeptBlock),
    KeptHistory cfg start blocks stop ∧ (∀ b ∈ blocks, CoveredFork b.fork) ∧
    start.state.getCode addr = beaconRootsCode ∧ start.state.getCode systemAddress = ByteArray.empty ∧
    HistoryClean blocks ∧ HistoryTimestampsFit blocks ∧
    ∃ (i j : Nat) (hi : i < blocks.length) (hj : j < blocks.length),
      i < j ∧ (blockWrite blocks[i]).1 ≠ 0 ∧
      blocks[i].block.header.timestamp + 8191 ≤ 2 ^ 256 ∧
      blocks[j].block.header.timestamp = blocks[i].block.header.timestamp + 8191 ∧
      timeKey (blockWrite blocks[j]).1 = timeKey (blockWrite blocks[i]).1 ∧
      storOf stop.state addr (timeKey (blockWrite blocks[i]).1) = (blockWrite blocks[j]).1 ∧
      (blockWrite blocks[j]).1 ≠ (blockWrite blocks[i]).1 ∧
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

/-- How the first joint step's `parent_root` relates to `anchor.beacon` across every fork pair `jointStep` admits:
* same-fork (`.electra`/`.electra` or `.fulu`/`.fulu`): `process_slots` runs from `anchor.beacon` (`anchor.slot <
  stepSlot`), giving `filledHeaderRoot anchor.beacon` whenever a single slot is processed or filling an unfilled header
  does not collide with `process_slot`'s `0 : B256` sentinel (`Ssz.hashTreeRoot anchor.beacon ≠ 0`);
* Electra → Fulu crossing (`anchor.slot ≤ forkSlot ≤ stepSlot`):
  - `anchor.slot < forkSlot`: pre-upgrade `process_slots` fills from `anchor.beacon`, giving `filledHeaderRoot
    anchor.beacon` under the corresponding single-slot (`forkSlot = anchor.slot + 1 ∧ stepSlot = forkSlot`) or
    non-zero-digest guard;
  - `anchor.slot = forkSlot = stepSlot`: neither `process_slots` runs (`atSlot`), so `parent_root =
    Ssz.hashTreeRoot anchor.beacon.latest_block_header` unconditionally;
  - `anchor.slot = forkSlot < stepSlot`: pre-upgrade `process_slots` is skipped, `upgradeToFulu` upgrades `anchor.beacon`
    to `upgraded : BeaconState P .fulu`, and post-upgrade `process_slots` fills from `upgraded`, giving
    `filledHeaderRoot upgraded` whenever `stepSlot = forkSlot + 1` or `upgraded`'s unfilled header does not hash to `0`.

Why the `Ssz.hashTreeRoot … ≠ 0` guard appears across ≥ 2 `process_slot` iterations: Phase 0's `process_slot`
(`JauneConsensus/Transition.lean:34`) tests `state.latest_block_header.state_root == 0` on every slot; if iteration 0
fills an unfilled `state_root` with a zero SHA-256 SSZ digest, iteration 1 re-enters that sentinel branch and
overwrites `state_root` with the next slot's state root (Goal §2 claims no SHA-256 preimage resistance beyond stated
premises). -/
def FirstStepAnchorRoot {P : Preset} (ccfg : Config) (anchor : JointState P)
    (firstBlock : AnySignedBlock P) (root : B256) : Prop :=
  let stepSlotNat := firstBlock.2.message.slot.toNat
  let forkSlotNat := fuluForkSlot (P := P) ccfg
  match anchor, firstBlock with
  | ⟨.electra, beacon, _⟩, ⟨.electra, _⟩ =>
    beacon.slot.toNat < stepSlotNat ∧ stepSlotNat < forkSlotNat ∧
      ((stepSlotNat = beacon.slot.toNat + 1 ∨
          (beacon.latest_block_header.state_root = 0 → Ssz.hashTreeRoot beacon ≠ 0)) →
        root = filledHeaderRoot beacon)
  | ⟨.fulu, beacon, _⟩, ⟨.fulu, _⟩ =>
    beacon.slot.toNat < stepSlotNat ∧
      ((stepSlotNat = beacon.slot.toNat + 1 ∨
          (beacon.latest_block_header.state_root = 0 → Ssz.hashTreeRoot beacon ≠ 0)) →
        root = filledHeaderRoot beacon)
  | ⟨.electra, beacon, _⟩, ⟨.fulu, _⟩ =>
    (beacon.slot.toNat < forkSlotNat ∧ forkSlotNat ≤ stepSlotNat ∧
      (((forkSlotNat = beacon.slot.toNat + 1 ∧ stepSlotNat = forkSlotNat) ∨
          (beacon.latest_block_header.state_root = 0 → Ssz.hashTreeRoot beacon ≠ 0)) →
        root = filledHeaderRoot beacon)) ∨
    (beacon.slot.toNat = forkSlotNat ∧ stepSlotNat = forkSlotNat ∧
      root = Ssz.hashTreeRoot beacon.latest_block_header) ∨
    (beacon.slot.toNat = forkSlotNat ∧ forkSlotNat < stepSlotNat ∧
      ∃ upgraded, upgradeToFulu ccfg beacon = .ok upgraded ∧
        ((stepSlotNat = forkSlotNat + 1 ∨
            (upgraded.latest_block_header.state_root = 0 → Ssz.hashTreeRoot upgraded ≠ 0)) →
          root = filledHeaderRoot upgraded))
  | _, _ => False

/-- **R-S9.** On the joint chain:
* **(a)** after each step, the contract holds the step's payload timestamp and its beacon block's `parent_root`
  (through `NewPayloadRequest.ofBlock`), and a read at a positive timestamp returns `some parent_root`;
* **(b)** at the first step, `parent_root` equals `Ssz.hashTreeRoot st.latest_block_header` for the `jointBlockInput`
  state `st` unconditionally, and satisfies `FirstStepAnchorRoot` across same-fork and all three Electra → Fulu
  crossing cases without excluding any valid anchor;
* **(c)** between consecutive steps `k` and `k + 1`, `parent_root` equals `Ssz.hashTreeRoot st.latest_block_header`
  for `jointBlockInput` from `steps[k].post` unconditionally, and equals `Ssz.hashTreeRoot steps[k].block.2.message`
  whenever `stepSlot steps[k+1] = stepSlot steps[k] + 1` or `steps[k].block.2.message.state_root ≠ 0` (excluding only
  a multi-slot Phase 0 `0 : B256` sentinel collision).
Chain-relative: no canonicality is claimed. -/
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
      let first := v.run.steps[0]'h
      (∃ st : BeaconState P first.block.1, jointBlockInput ccfg bls anchor first.block = .ok st ∧
        first.block.2.message.parent_root = Ssz.hashTreeRoot st.latest_block_header) ∧
      FirstStepAnchorRoot ccfg anchor first.block first.block.2.message.parent_root) ∧
    (∀ k (hk : k + 1 < v.run.steps.length),
      let prev := v.run.steps[k]'(Nat.lt_of_succ_lt hk)
      let curr := v.run.steps[k + 1]'hk
      (∃ st : BeaconState P curr.block.1, jointBlockInput ccfg bls prev.post curr.block = .ok st ∧
        curr.block.2.message.parent_root = Ssz.hashTreeRoot st.latest_block_header) ∧
      ((stepSlot curr = stepSlot prev + 1 ∨ prev.block.2.message.state_root ≠ 0) →
        curr.block.2.message.parent_root = Ssz.hashTreeRoot prev.block.2.message))

/-- **R-S9 control.** Mutating the converted request's `parentBeaconBlockRoot` to `mutatedRoot ≠ block.parent_root`
makes the execution block's protocol call store `mutatedRoot` and therefore falsifies R-S9's parent-root equality
(`storOf … ≠ block.parent_root`, and for positive timestamps `read … ≠ some block.parent_root`). So R-S9's equation
rests on `NewPayloadRequest.ofBlock` passing `block.parent_root`. -/
def R_S9_control : Prop :=
  ∀ {P : Preset} {f : CFork} (block : BeaconBlock P f) (req : NewPayloadRequest P) (mutatedRoot : B256)
    (fork : Jaune.Fork) (parent : BlockChain)
    -- the engine request built for the beacon block
    (_ofBlock : NewPayloadRequest.ofBlock block = .ok req)
    -- the mutated root differs from the beacon block's parent_root
    (_ne : mutatedRoot ≠ block.parent_root)
    -- a covered fork
    (_fork : CoveredFork fork)
    -- the canonical code at the parent
    (_code : parent.state.getCode addr = beaconRootsCode),
    let mutatedReq := { req with parentBeaconBlockRoot := mutatedRoot }
    let hdr := (payloadToBlock mutatedReq).header
    ∃ st bal,
      beaconRootsCall fork.ruleSet (initBenv fork parent hdr) = .ok (st, bal) ∧
      storOf st addr (rootKey hdr.timestamp.toB256) = mutatedRoot ∧
      storOf st addr (rootKey hdr.timestamp.toB256) ≠ block.parent_root ∧
      (hdr.timestamp.toB256 ≠ 0 →
        read (storOf st addr) hdr.timestamp.toB256 = some mutatedRoot ∧
        read (storOf st addr) hdr.timestamp.toB256 ≠ some block.parent_root)

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
