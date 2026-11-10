import Blanc.ExecutionKeptClean
import Blanc.ExecutionKeptValue
import Blanc.ExecutionKeptConfigured
import Blanc.JointHistory
import Blanc.Lift.RequestSystem.Call
import Blanc.SystemContracts

/-!
# G0 freeze (protocol-contract-corpus-v1, part rh): vocabulary shared by the R and H cells

A freeze record, not a landing: this module is deliberately absent from the layering classification and the
root. Every definition here is the minimal vocabulary the frozen statements of
`Blanc.Corpus.Freeze.BeaconRoots` and `Blanc.Corpus.Freeze.HistoryStorage` read. On landing, `ring` and
`keptAtAddr` go to a shared module (they name no contract), and each family owns its own observation record.

Read from Blanc main `7f2a69ba`, Jaune `c30cf0a5`.
-/

namespace Blanc.Corpus.Freeze

open Jaune Blanc ExecutionTrace

/-- The ring-buffer length both contracts use: `8191 = 0x1fff`, the `PUSH3 0x001fff` (R) and `PUSH2 0x1fff`
(H) immediates of the bytes in `Blanc/SystemContracts.lean`. -/
abbrev ring : B256 := 0x1fff

/-- The frames a kept history kept at an address, in execution order: settled frames only, nested ones
included (`KeptBlock.keptAt`, `Blanc/ExecutionKeptChain.lean`). -/
noncomputable def keptAtAddr (a : Adr) (blocks : List KeptBlock) : List Exec.Frame :=
  blocks.flatMap (KeptBlock.keptAt a)

/-- An account's storage as a function of the key. -/
def storOf (w : State) (a : Adr) : B256 → B256 := (w.getStor a).get

/-- A frame's account storage when it starts, as a function of the key. -/
def frameStor (f : Exec.Frame) : B256 → B256 := (Devm.getStor f.pre f.sevm.currentTarget).get

/-- The tip of a chain, read as the tip of the checkpoint's observation records
(`Lift.WithdrawalRequest.WithdrawalDeploymentObservation.checkpointTip`, `ConsolidationCheckpointObservation.tip`):
number 22,431,083, the last pre-Prague block. -/
def ObservedPreTip (checkpoint : BlockChain) : Prop :=
  ∃ t, checkpoint.blocks.getLast? = some t ∧ t.header.number = 22431083 ∧ t.header.timestamp = 1746612299 ∧
    t.header.hash = 0x28fb2c1d988435955e569451c6ad772f7fb5e61cddd7463c7b60e933ed5ff237 ∧
    t.header.stateRoot = 0xab350e0fe349aef68947ede26295f8946c34ce3af5e3ec76f4b26ddeef29c0e3

/-- The timestamp of the payload a joint step carries, as the execution environment reads it
(`initBenvStat`: `time := header.timestamp.toB256`; `payloadHeader`: `timestamp := payload.timestamp.toNat`). -/
def stepTime {P : JauneConsensus.Preset} {cfg : ChainConfig} {ccfg : JauneConsensus.Config} {bls : Bool}
    (st : JointRunStep (P := P) cfg ccfg bls) : B256 :=
  st.block.2.message.body.execution_payload.timestamp.toNat.toB256

/-- The block number of the payload a joint step carries, as the execution environment reads it. -/
def stepNumber {P : JauneConsensus.Preset} {cfg : ChainConfig} {ccfg : JauneConsensus.Config} {bls : Bool}
    (st : JointRunStep (P := P) cfg ccfg bls) : Nat :=
  st.block.2.message.body.execution_payload.block_number.toNat

/-- The slot of a joint step's beacon block. -/
def stepSlot {P : JauneConsensus.Preset} {cfg : ChainConfig} {ccfg : JauneConsensus.Config} {bls : Bool}
    (st : JointRunStep (P := P) cfg ccfg bls) : Nat :=
  st.block.2.message.slot.toNat

/-- **The joint-chain premises a system ring contract's S9 statement reads.** A configured (covered-fork)
execution history from a checkpoint to the anchor's execution chain, a joint run from the anchor, the contract's
code and no code at `SYSTEM_ADDRESS` at the checkpoint, and the SYSTEM_ADDRESS exclusions over every kept block
of the joint history. It is the part of `Lift.WithdrawalRequest.ValidJoint` that names no contract (its `pre` and
`run`), plus the contract's code: no deployment, no anchor invariant, no preset bound. -/
structure RingJoint {P : JauneConsensus.Preset} (cfg : ChainConfig) (ccfg : JauneConsensus.Config) (bls : Bool)
    (a : Adr) (C : ByteArray) (checkpoint : BlockChain) (anchor final : JauneConsensus.JointState P) : Type where
  /-- The configured execution history from the checkpoint to the anchor's execution chain. -/
  pre : ConfiguredHistoryTrace cfg checkpoint anchor.exec
  /-- The joint run from the anchor (Electra and Fulu steps only). -/
  run : JointRun cfg ccfg bls anchor final
  /-- The contract's canonical code at the checkpoint. -/
  code : checkpoint.state.getCode a = C
  /-- No code at `SYSTEM_ADDRESS` at the checkpoint. -/
  systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty
  /-- No `SYSTEM_ADDRESS` sender, authority or creation in any kept block of the joint history. -/
  clean : HistoryClean (run.toExec pre).kept

end Blanc.Corpus.Freeze
