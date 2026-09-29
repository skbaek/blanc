import Blanc.Lift.BeaconDeposit.CommittedHistory
import Blanc.ExecutionTraceWarmth
import Blanc.ExecutionTraceCodeAt
import Blanc.ExecutionTraceSystem

/-!
# The Beacon committed-history headlines without per-frame environment premises

`configuredHistory_solInv` and its siblings (`CommittedHistory.lean`) demand
`trace.FrameAdmitted ca beaconEntry`: at every entered frame at the deposit contract,

1. the calldata length is below `2 ^ 256`,
2. the SHA-256 precompile's account holds no EIP-7702 delegation designator,
3. the SHA-256 precompile is warm.

This module derives (2) and (3) from premises about the trace as a whole, and keeps (1) as the
per-frame premise it was.

* **Warmth** (`Blanc/ExecutionTraceWarmth.lean`).  A transaction pre-warms every precompile
  (EIP-2929) and the accessed set of a frame only grows, so every frame a transaction enters
  starts with `2` warm, including the frames of subtrees that later revert.  A system message
  starts with an empty set, so its frames are not covered: the headlines therefore exclude them.
  `systemSpawnFree` says the code every system frame runs contains no CALL-family or
  CREATE-family instruction (true of the canonical EIP-4788, EIP-2935, EIP-7002 and EIP-7251
  code, a static property of bytes), so such a frame enters no child and its only frame targets
  the system address; `notSystem` says the deposit contract is not one of the four system
  addresses.  Together they give `system`, the exclusion `beaconEntry_of_env` consumes.
* **No delegation** (`Blanc/ExecutionTraceCodeAt.lean`).  A transaction can install a code
  designator at an account only through an EIP-7702 authorization that recovers to it or
  through a frame that CREATEs it.  `checkpointEmpty` (the precompile account is empty at the
  checkpoint), `noAuthority` (no authorization of the trace recovers to `2`) and `noFrame` (no
  CREATE frame the trace enters targets `2`; a CREATE frame is a frame with no code address) leave code at `2` empty in every state of the trace, hence
  in every frame's entry.

The last two premises quantify only over the finite trace, not over all CREATE addresses or all
signatures.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc Blanc.ExecutionTrace

/-- **The system exclusion is derived** from the static fact that the code a system frame runs
spawns nothing and from the deposit contract not being a system address. -/
theorem system_of_spawnFree {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {ca : Adr}
    (systemSpawnFree : ∀ root ∈ trace.systemRawFrames, SpawnFree root.sevm.code)
    (notSystem : ca ∉ systemTargets) :
    ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ ca := by
  intro root member h
  exact notSystem (h ▸ trace.systemRawFrames_target_of_spawnFree systemSpawnFree root member)

/-- The SHA-256 precompile is a precompile of every covered fork. -/
theorem two_mem_precompiles {f : Fork} (hf : CoveredFork f) :
    (2 : Adr) ∈ (Fork.ruleSet f).precompiles :=
  hf.cases (motive := fun f => (2 : Adr) ∈ (Fork.ruleSet f).precompiles)
    (by decide) (by decide) (by decide) (by decide)

/-- Empty code is not a delegation designator. -/
theorem getDelegatedCodeAddress_empty : getDelegatedCodeAddress ByteArray.empty = none := by
  have h : ¬ isValidDelegation ByteArray.empty := fun h => absurd h.1 (by decide)
  simp [getDelegatedCodeAddress, h]

/-- **The environment part of `beaconEntry` at every deposit frame is derived.**  Warmth of `2`
from the transaction pre-warm, no delegation at `2` from empty code at the checkpoint, no
authorization recovering to `2` and no frame targeting `2`; system frames are excluded by
`system`.  Only the calldata bound stays a per-frame premise. -/
theorem beaconEntry_of_env {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {ca : Adr}
    (calldata : trace.FrameAdmitted ca (fun sevm _ => sevm.data.length < 2 ^ 256))
    (system : ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ ca)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 2) :
    trace.FrameAdmitted ca beaconEntry := by
  rw [trace.frameAdmitted_iff_rawFrames ca _] at calldata ⊢
  intro root member target
  rcases trace.rawFrames_system_or_tx root member with hsys | htx
  · exact absurd target (system root hsys)
  · obtain ⟨hcode, -⟩ := trace.codeAt_empty noAuthority noFrame checkpointEmpty
    refine ⟨calldata root member target, ?_, ?_⟩
    · show getDelegatedCodeAddress (root.devm.getCode 2) = none
      rw [hcode root htx]
      exact getDelegatedCodeAddress_empty
    · exact trace.txRawFrames_warm (fun f hf => two_mem_precompiles hf) root htx

/-- **Committed-history soundness with the environment premises derived.**  The conclusion of
`configuredHistory_solInv`, with `beaconEntry` replaced by the calldata bound and the trace-level
premises above. -/
theorem configuredHistory_solInv_env {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (calldata : trace.FrameAdmitted ca (fun sevm _ => sevm.data.length < 2 ^ 256))
    (systemSpawnFree : ∀ root ∈ trace.systemRawFrames, SpawnFree root.sevm.code)
    (notSystem : ca ∉ systemTargets)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 2)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    SolInv (future.state.getStor ca) (initialHistory ++ committedNodes ca trace) :=
  configuredHistory_solInv trace
    (beaconEntry_of_env trace calldata (system_of_spawnFree trace systemSpawnFree notSystem)
      checkpointEmpty noAuthority noFrame)
    installed invariant

/-- The final deployed count word is the length of the same exact history. -/
theorem configuredHistory_count_env {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (calldata : trace.FrameAdmitted ca (fun sevm _ => sevm.data.length < 2 ^ 256))
    (systemSpawnFree : ∀ root ∈ trace.systemRawFrames, SpawnFree root.sevm.code)
    (notSystem : ca ∉ systemTargets)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 2)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    (future.state.getStor ca).get solCountSlot =
      Nat.toB256 (initialHistory ++ committedNodes ca trace).length ∧
      (initialHistory ++ committedNodes ca trace).length < 2 ^ 32 :=
  configuredHistory_count trace
    (beaconEntry_of_env trace calldata (system_of_spawnFree trace systemSpawnFree notSystem)
      checkpointEmpty noAuthority noFrame)
    installed invariant

/-- The final mixed root belongs to the same exact extracted node sequence. -/
theorem configuredHistory_root_env {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (calldata : trace.FrameAdmitted ca (fun sevm _ => sevm.data.length < 2 ^ 256))
    (systemSpawnFree : ∀ root ∈ trace.systemRawFrames, SpawnFree root.sevm.code)
    (notSystem : ca ∉ systemTargets)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 2)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    BeaconDeposit.Acc.root Bytes.sha256 (solAcc (future.state.getStor ca)) =
      BeaconDeposit.mixedRootOf Bytes.sha256 (initialHistory ++ committedNodes ca trace) :=
  configuredHistory_root trace
    (beaconEntry_of_env trace calldata (system_of_spawnFree trace systemSpawnFree notSystem)
      checkpointEmpty noAuthority noFrame)
    installed invariant

end Blanc.Lift.BeaconDeposit
