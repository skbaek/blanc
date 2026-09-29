import Blanc.Lift.BeaconDeposit.CommittedHistory
import Blanc.ExecutionTraceWarmth
import Blanc.ExecutionTraceCodeAt
import Blanc.ExecutionTraceSystem
import Blanc.ExecutionTraceCalldata
import Blanc.ExecutionTraceSystemCode

/-!
# The Beacon committed-history headlines without per-frame environment premises

`configuredHistory_solInv` and its siblings (`CommittedHistory.lean`) demand
`trace.FrameAdmitted ca beaconEntry`: at every entered frame at the deposit contract,

1. the calldata length is below `2 ^ 256`,
2. the SHA-256 precompile's account holds no EIP-7702 delegation designator,
3. the SHA-256 precompile is warm.

This module derives (2) and (3) from premises about the trace as a whole.  The `_env` headlines keep
(1) as the per-frame premise it was; the `_envDerived` headlines discharge it from
`Blanc/ExecutionTraceCalldata.lean`.

* **Warmth** (`Blanc/ExecutionTraceWarmth.lean`).  A transaction pre-warms every precompile
  (EIP-2929) and the accessed set of a frame only grows, so every frame a transaction enters
  starts with `2` warm, including the frames of subtrees that later revert.  A system message
  starts with an empty set, so its frames are not covered: the headlines therefore exclude them.
  `systemSpawnFree` says the code every system frame runs contains no CALL-family or
  CREATE-family instruction at any offset, so such a frame enters no child and its only frame
  targets the system address; `notSystem` says the deposit contract is not one of the four system
  addresses.  Together they give `system`, the exclusion `beaconEntry_of_env` consumes.
  **`systemSpawnFree` is false of the canonical EIP-7002 code** (`0xF4` bytes inside `PUSH`
  data, `withdrawalRequestCode_not_spawnFree`), so the `_env` and `_envDerived` headlines are
  vacuous on mainnet; the `_sys` headlines at the end of this file are the satisfiable form.
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

/-! ### The calldata bound is derived too

`ConfiguredHistoryTrace.frameAdmitted_calldata` (`Blanc/ExecutionTraceCalldata.lean`) discharges
the per-frame calldata premise from the retained transaction and header validation, so the
headlines below carry no per-frame premise at all.  The variants above keep their statements. -/

/-- `configuredHistory_solInv_env` without the calldata premise. -/
theorem configuredHistory_solInv_envDerived {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (systemSpawnFree : ∀ root ∈ trace.systemRawFrames, SpawnFree root.sevm.code)
    (notSystem : ca ∉ systemTargets)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 2)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    SolInv (future.state.getStor ca) (initialHistory ++ committedNodes ca trace) :=
  configuredHistory_solInv_env trace trace.frameAdmitted_calldata systemSpawnFree notSystem
    checkpointEmpty noAuthority noFrame installed invariant

/-- `configuredHistory_count_env` without the calldata premise. -/
theorem configuredHistory_count_envDerived {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
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
  configuredHistory_count_env trace trace.frameAdmitted_calldata systemSpawnFree notSystem
    checkpointEmpty noAuthority noFrame installed invariant

/-- `configuredHistory_root_env` without the calldata premise. -/
theorem configuredHistory_root_envDerived {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
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
  configuredHistory_root_env trace trace.frameAdmitted_calldata systemSpawnFree notSystem
    checkpointEmpty noAuthority noFrame installed invariant

/-! ### The system frames run the canonical code

`systemSpawnFree` (`SpawnFree` of the code of every system frame) is false of the canonical
EIP-7002 code (`withdrawalRequestCode_not_spawnFree`), so the `_env` and `_envDerived` headlines
above are vacuous on mainnet.  The `_sys` headlines replace it by premises a real chain can meet:

* the checkpoint holds the canonical code at the four system addresses
  (`SystemCodeInstalled`, `Blanc/SystemContracts.lean`);
* no authorization of the trace recovers to one of them and no CREATE frame the trace enters
  targets one, the same trace-local form as for the SHA-256 precompile.

From these, `ConfiguredHistoryTrace.systemFrames_of_installed` shows that the code every system
message starts from is still the canonical code, which spawns nothing at any position an
execution reaches (`SpawnFreeReach`), so a system message enters no frame but its own and the
deposit contract is not among its targets.  That the deposit contract is not itself a system
address is derived too: its installed code is not a canonical system code. -/

/-- The deposit contract's runtime is 6358 bytes, more than any canonical system contract. -/
theorem code_size : code.size = 6358 := by decide +kernel

theorem not_mem_systemTargets_of_installed {w : State} {ca : Adr}
    (installed : w.getCode ca = code) (system : SystemCodeInstalled w) :
    ca ∉ systemTargets := by
  intro hmem
  simp only [systemTargets, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hsize : ∀ p ∈ systemContracts, p.1 = ca → False := by
    intro p hp hca
    have h := system p hp
    rw [hca, installed] at h
    have := congrArg ByteArray.size h
    rw [code_size] at this
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> revert this <;> decide +kernel
  rcases hmem with rfl | rfl | rfl | rfl
  · exact hsize (beaconRootsAddress, beaconRootsCode) (by simp [systemContracts]) rfl
  · exact hsize (historyStorageAddress, historyStorageCode) (by simp [systemContracts]) rfl
  · exact hsize (withdrawalRequestPredeployAddress, withdrawalRequestCode)
      (by simp [systemContracts]) rfl
  · exact hsize (consolidationRequestPredeployAddress, consolidationRequestCode)
      (by simp [systemContracts]) rfl

/-- **The system exclusion is derived** from the canonical system code being installed at the
checkpoint. -/
theorem system_of_installed {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {ca : Adr}
    (systemInstalled : SystemCodeInstalled checkpoint.state)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (systemNoFrame : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1)
    (installed : checkpoint.state.getCode ca = code) :
    ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ ca := by
  intro root member h
  obtain ⟨hframes, -⟩ := trace.systemFrames_of_installed systemInstalled systemNoAuthority
    systemNoFrame
  exact not_mem_systemTargets_of_installed installed systemInstalled
    (h ▸ hframes root member)

/-- **Committed-history soundness on mainnet.**  `configuredHistory_solInv_envDerived` with the
unsatisfiable system-code premise replaced by the canonical system code installed at the
checkpoint plus trace-local exclusions of EIP-7702 authorizations and CREATE frames at the four
system addresses. -/
theorem configuredHistory_solInv_sys {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (systemInstalled : SystemCodeInstalled checkpoint.state)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (systemNoFrame : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 2)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    SolInv (future.state.getStor ca) (initialHistory ++ committedNodes ca trace) :=
  configuredHistory_solInv trace
    (beaconEntry_of_env trace trace.frameAdmitted_calldata
      (system_of_installed trace systemInstalled systemNoAuthority systemNoFrame installed)
      checkpointEmpty noAuthority noFrame)
    installed invariant

/-- The final deployed count word is the length of the same exact history. -/
theorem configuredHistory_count_sys {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (systemInstalled : SystemCodeInstalled checkpoint.state)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (systemNoFrame : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 2)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    (future.state.getStor ca).get solCountSlot =
      Nat.toB256 (initialHistory ++ committedNodes ca trace).length ∧
      (initialHistory ++ committedNodes ca trace).length < 2 ^ 32 :=
  solCount_eq_of_solInv (configuredHistory_solInv_sys trace systemInstalled systemNoAuthority
    systemNoFrame checkpointEmpty noAuthority noFrame installed invariant)

/-- The final mixed root belongs to the same exact extracted node sequence. -/
theorem configuredHistory_root_sys {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (systemInstalled : SystemCodeInstalled checkpoint.state)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (systemNoFrame : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 2)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    BeaconDeposit.Acc.root Bytes.sha256 (solAcc (future.state.getStor ca)) =
      BeaconDeposit.mixedRootOf Bytes.sha256 (initialHistory ++ committedNodes ca trace) :=
  BeaconDeposit.root_correct _ _ _
    (configuredHistory_solInv_sys trace systemInstalled systemNoAuthority systemNoFrame
      checkpointEmpty noAuthority noFrame installed invariant).2

end Blanc.Lift.BeaconDeposit
