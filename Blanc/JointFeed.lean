import Blanc.ExecutionKeptClean
import Blanc.ExecutionKeptConfigured
import Blanc.JointHistory
import Blanc.ListChunks
import Blanc.ListFlatMapPosition

/-!
# Shared joint-history kept-block bridges, ring-contract joint carrier, and feed indexing

Contract-neutral helpers sitting above `JointHistory` and `ExecutionKeptConfigured`:

* **Ring and kept-history vocabulary (`JointFeed` / `Blanc`):** `ringModulus` (`0x1fff = 8191`, aliased as
  `JointFeed.ring`), `keptAtAddr`, `storOf`, `frameStor`, `ObservedPreTip`, `HistoryTimestampsFit`,
  `HistoryNumbersFit`, `stepTime`, `stepNumber`, `stepSlot`, and `RingJoint` (the contract-neutral joint-chain
  premise bundle shared by pre-execution system ring contracts).
* **Kept-block bridge (`JointRun.kept_toExec`, `JointRun.kept_getElem?`, `JointRunStep` header/request lemmas):**
  `(run.toExec pre).kept` is `pre.kept` followed by `run.steps.map (fun D => D.stepTrace.trace.kept)`, indexing
  joint step `j` directly to kept block `pre.kept.length + j` and exposing its header timestamp, block number,
  `parentHash`, `parentBeaconBlockRoot`, and execution-requests list.
* **Generic feed indexing (`stepRequests`, `feed`, `feedPosition`):** parameterised by any projection
  `proj : ExecutionRequests P → List α` (deposit, withdrawal, or consolidation requests), with `feed_getElem?`,
  `exists_feed_position`, and `feedPosition_inj`.
-/

namespace Blanc

open Jaune JauneConsensus ExecutionTrace

/-! ## Shared ring-contract and kept-history observers -/

/-- The 8,191-slot ring modulus (`0x1fff = 8191`) used by EIP-4788 and EIP-2935. -/
abbrev ringModulus : B256 := 0x1fff

/-- Settled frames a kept history retains at address `a`, in execution order. -/
noncomputable def keptAtAddr (a : Adr) (blocks : List KeptBlock) : List Exec.Frame :=
  blocks.flatMap (KeptBlock.keptAt a)

/-- An account's storage in world `w` as a key-to-word function. -/
def storOf (w : State) (a : Adr) : B256 → B256 := (w.getStor a).get

/-- A frame's target-account storage at entry as a key-to-word function. -/
def frameStor (f : Exec.Frame) : B256 → B256 := (Devm.getStor f.pre f.sevm.currentTarget).get

/-- The observed pre-Prague mainnet checkpoint tip header at block 22,431,083. -/
def ObservedPreTip (checkpoint : BlockChain) : Prop :=
  ∃ t, checkpoint.blocks.getLast? = some t ∧ t.header.number = 22431083 ∧ t.header.timestamp = 1746612299 ∧
    t.header.hash = 0x28fb2c1d988435955e569451c6ad772f7fb5e61cddd7463c7b60e933ed5ff237 ∧
    t.header.stateRoot = 0xab350e0fe349aef68947ede26295f8946c34ce3af5e3ec76f4b26ddeef29c0e3

/-- Word-fit bound for kept blocks' 8,191-second timestamp window. -/
def HistoryTimestampsFit (blocks : List KeptBlock) : Prop :=
  ∀ b ∈ blocks, b.block.header.timestamp + 8191 < 2 ^ 256

/-- Word-fit bound for kept blocks' 8,191-block number window. -/
def HistoryNumbersFit (blocks : List KeptBlock) : Prop :=
  ∀ b ∈ blocks, b.block.header.number + 8191 < 2 ^ 256

/-- Payload timestamp of a joint run step as the 256-bit word `benv.stat.time` reads. -/
def stepTime {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (st : JointRunStep (P := P) cfg ccfg bls) : B256 :=
  st.block.2.message.body.execution_payload.timestamp.toNat.toB256

/-- Payload block number of a joint run step. -/
def stepNumber {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (st : JointRunStep (P := P) cfg ccfg bls) : Nat :=
  st.block.2.message.body.execution_payload.block_number.toNat

/-- Beacon slot of a joint run step's signed block. -/
def stepSlot {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (st : JointRunStep (P := P) cfg ccfg bls) : Nat :=
  st.block.2.message.slot.toNat

/-- **Joint-chain premise bundle for a system contract at `(a, C)`:** a configured covered-fork execution history
from `checkpoint` to `anchor.exec`, a `JointRun` from `anchor` to `final`, the contract's code and empty
`SYSTEM_ADDRESS` code at `checkpoint`, and `HistoryClean` over all kept blocks of `run.toExec pre`. -/
structure RingJoint {P : Preset} (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    (a : Adr) (C : ByteArray) (checkpoint : BlockChain) (anchor final : JointState P) : Type where
  pre : ConfiguredHistoryTrace cfg checkpoint anchor.exec
  run : JointRun cfg ccfg bls anchor final
  code : checkpoint.state.getCode a = C
  systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty
  clean : HistoryClean (run.toExec pre).kept

/-! ## `NewPayloadRequest.ofBlock` and `JointRunStep` kept-block projections -/

theorem ofBlock_parentBeaconBlockRoot {P : Preset} {f : CFork} {block : BeaconBlock P f}
    {req : NewPayloadRequest P} (h : NewPayloadRequest.ofBlock block = .ok req) :
    req.parentBeaconBlockRoot = block.parent_root := by
  unfold NewPayloadRequest.ofBlock at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases h
  rfl

namespace JointRunStep

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-- The kept execution block that `JointRun.toExec` appends for step `D`. -/
noncomputable abbrev keptBlock (D : JointRunStep (P := P) cfg ccfg bls) : KeptBlock :=
  D.stepTrace.trace.kept

theorem keptBlock_parent (D : JointRunStep (P := P) cfg ccfg bls) :
    D.keptBlock.parent = D.pre.exec := rfl

theorem keptBlock_step (D : JointRunStep (P := P) cfg ccfg bls) :
    KeptStep cfg D.keptBlock D.post.exec := D.stepTrace.trace.keptStep

theorem keptBlock_covered (D : JointRunStep (P := P) cfg ccfg bls) :
    CoveredFork D.keptBlock.fork := D.stepTrace.trace.covered

theorem keptBlock_block (D : JointRunStep (P := P) cfg ccfg bls) :
    D.keptBlock.block = payloadToBlock D.stepTrace.req := D.stepTrace.block_eq

theorem keptBlock_requests (D : JointRunStep (P := P) cfg ccfg bls) :
    D.keptBlock.output.requests = D.stepTrace.req.executionRequests := D.stepTrace.requests_eq

theorem keptBlock_number (D : JointRunStep (P := P) cfg ccfg bls) :
    D.keptBlock.block.header.number = stepNumber D := by
  show D.stepTrace.trace.block.header.number = _
  rw [D.stepTrace.block_eq]
  simp only [payloadToBlock, payloadHeader, ofBlock_executionPayload D.stepTrace.ofBlock, stepNumber]

theorem keptBlock_timestamp (D : JointRunStep (P := P) cfg ccfg bls) :
    D.keptBlock.block.header.timestamp = D.block.2.message.body.execution_payload.timestamp.toNat := by
  show D.stepTrace.trace.block.header.timestamp = _
  rw [D.stepTrace.block_eq]
  simp only [payloadToBlock, payloadHeader, ofBlock_executionPayload D.stepTrace.ofBlock]

theorem keptBlock_parentHash (D : JointRunStep (P := P) cfg ccfg bls) :
    D.keptBlock.block.header.parentHash = D.block.2.message.body.execution_payload.parent_hash := by
  show D.stepTrace.trace.block.header.parentHash = _
  rw [D.stepTrace.block_eq]
  simp only [payloadToBlock, payloadHeader, ofBlock_executionPayload D.stepTrace.ofBlock]

theorem keptBlock_parentBeaconBlockRoot (D : JointRunStep (P := P) cfg ccfg bls) :
    D.keptBlock.block.header.parentBeaconBlockRoot = some D.block.2.message.parent_root := by
  show D.stepTrace.trace.block.header.parentBeaconBlockRoot = _
  rw [D.stepTrace.block_eq]
  simp only [payloadToBlock, payloadHeader, ofBlock_parentBeaconBlockRoot D.stepTrace.ofBlock]

theorem keptBlock_benv_time (D : JointRunStep (P := P) cfg ccfg bls) :
    D.keptBlock.benv.stat.time = stepTime D := by
  simp only [KeptBlock.benv, initBenv, initBenvStat, keptBlock_timestamp, stepTime]

theorem exists_executionRequests (D : JointRunStep (P := P) cfg ccfg bls) :
    ∃ requests : ExecutionRequests P,
      Gated.read D.block.2.message.body.execution_requests "NewPayloadRequest: execution_requests" =
        .ok requests ∧
      D.keptBlock.output.requests = getExecutionRequestsList requests := by
  obtain ⟨requests, hread, hlist⟩ := ofBlock_executionRequests D.stepTrace.ofBlock
  exact ⟨requests, hread, D.keptBlock_requests.trans hlist⟩

end JointRunStep

/-! ## `JointRun.toExec` kept-block indexing -/

theorem JointRun.kept_toExec {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) :
    {s : JointState P} → (run : JointRun cfg ccfg bls s₀ s) →
    (run.toExec pre).kept = pre.kept ++ run.steps.map JointRunStep.keptBlock
  | _, .nil => by
    simp only [JointRun.toExec_nil, JointRun.steps_nil, List.map_nil, List.append_nil]
  | _, .snoc run b step bound => by
    simp only [JointRun.toExec_snoc, ConfiguredHistoryTrace.kept, JointRun.steps_snoc,
      List.map_append, List.map_cons, List.map_nil, JointRun.kept_toExec pre run, List.append_assoc]

theorem JointRun.kept_length {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) (run : JointRun cfg ccfg bls s₀ s) :
    (run.toExec pre).kept.length = pre.kept.length + run.steps.length := by
  rw [run.kept_toExec pre, List.length_append, List.length_map]

theorem JointRun.kept_take_pre {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) (run : JointRun cfg ccfg bls s₀ s) :
    (run.toExec pre).kept.take pre.kept.length = pre.kept := by
  rw [run.kept_toExec pre, List.take_left]

theorem JointRun.kept_take_add {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) (run : JointRun cfg ccfg bls s₀ s) (j : Nat) :
    (run.toExec pre).kept.take (pre.kept.length + j) =
      pre.kept ++ (run.steps.take j).map JointRunStep.keptBlock := by
  rw [run.kept_toExec pre, List.take_append, Nat.add_sub_cancel_left,
    List.take_of_length_le (Nat.le_add_right pre.kept.length j), List.map_take]

theorem JointRun.kept_getElem?_map {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) (run : JointRun cfg ccfg bls s₀ s) (j : Nat) :
    (run.toExec pre).kept[pre.kept.length + j]? = (run.steps[j]?).map JointRunStep.keptBlock := by
  rw [run.kept_toExec pre, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map]

theorem JointRun.kept_getElem? {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) (run : JointRun cfg ccfg bls s₀ s)
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls} (h : run.steps[j]? = some D) :
    (run.toExec pre).kept[pre.kept.length + j]? = some D.keptBlock := by
  rw [run.kept_getElem?_map pre j, h]
  rfl

namespace RingJoint

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
  {a : Adr} {C : ByteArray} {checkpoint : BlockChain} {anchor final : JointState P}

noncomputable abbrev blocks (v : RingJoint cfg ccfg bls a C checkpoint anchor final) : List KeptBlock :=
  (v.run.toExec v.pre).kept

theorem keptHistory (v : RingJoint cfg ccfg bls a C checkpoint anchor final) :
    KeptHistory cfg checkpoint v.blocks final.exec :=
  (v.run.toExec v.pre).keptHistory

theorem covered (v : RingJoint cfg ccfg bls a C checkpoint anchor final) :
    ∀ b ∈ v.blocks, CoveredFork b.fork :=
  (v.run.toExec v.pre).kept_covered

theorem blocks_eq (v : RingJoint cfg ccfg bls a C checkpoint anchor final) :
    v.blocks = v.pre.kept ++ v.run.steps.map JointRunStep.keptBlock :=
  v.run.kept_toExec v.pre

theorem blocks_getElem? (v : RingJoint cfg ccfg bls a C checkpoint anchor final)
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls} (h : v.run.steps[j]? = some D) :
    v.blocks[v.pre.kept.length + j]? = some D.keptBlock :=
  v.run.kept_getElem? v.pre h

end RingJoint

/-! ## Generic consensus request-feed indexing -/

namespace JointFeed

/-- Alias for `Blanc.ringModulus` (`0x1fff = 8191`). -/
abbrev ring : B256 := ringModulus

section Feed

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {α : Type}

/-- Requests projected from one joint run step's `execution_requests` container. -/
def stepRequests (proj : ExecutionRequests P → List α) (D : JointRunStep (P := P) cfg ccfg bls) : List α :=
  match Gated.read D.block.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" with
  | .ok requests => proj requests
  | .error _ => []

/-- Concatenated projected requests across a joint run's steps, in step order. -/
noncomputable def feed {s₀ s : JointState P} (proj : ExecutionRequests P → List α)
    (run : JointRun cfg ccfg bls s₀ s) : List α :=
  run.steps.flatMap (stepRequests proj)

/-- Feed position of element `k` inside step `j` of `run`. -/
noncomputable def feedPosition {s₀ s : JointState P} (proj : ExecutionRequests P → List α)
    (run : JointRun cfg ccfg bls s₀ s) (j k : Nat) : Nat :=
  ((run.steps.take j).flatMap (stepRequests proj)).length + k

theorem stepRequests_of_read (proj : ExecutionRequests P → List α) (D : JointRunStep (P := P) cfg ccfg bls)
    {requests : ExecutionRequests P}
    (h : Gated.read D.block.2.message.body.execution_requests "NewPayloadRequest: execution_requests" =
      .ok requests) :
    stepRequests proj D = proj requests := by
  simp only [stepRequests, h]

theorem exists_stepRequests (proj : ExecutionRequests P → List α) (D : JointRunStep (P := P) cfg ccfg bls) :
    ∃ requests : ExecutionRequests P,
      Gated.read D.block.2.message.body.execution_requests "NewPayloadRequest: execution_requests" =
        .ok requests ∧
      D.keptBlock.output.requests = getExecutionRequestsList requests ∧
      stepRequests proj D = proj requests := by
  obtain ⟨requests, hread, hlist⟩ := D.exists_executionRequests
  exact ⟨requests, hread, hlist, stepRequests_of_read proj D hread⟩

theorem feed_getElem? {s₀ s : JointState P} (proj : ExecutionRequests P → List α)
    (run : JointRun cfg ccfg bls s₀ s) {j k : Nat}
    (hj : j < run.steps.length) (hk : k < (stepRequests proj run.steps[j]).length) :
    (feed proj run)[feedPosition proj run j k]? = (stepRequests proj run.steps[j])[k]? :=
  Blanc.List.getElem?_flatMap_position (stepRequests proj) run.steps hj hk

theorem feed_getElem?_of_some {s₀ s : JointState P} (proj : ExecutionRequests P → List α)
    (run : JointRun cfg ccfg bls s₀ s) {j k : Nat} {D : JointRunStep (P := P) cfg ccfg bls}
    (hD : run.steps[j]? = some D) (hk : k < (stepRequests proj D).length) :
    (feed proj run)[feedPosition proj run j k]? = (stepRequests proj D)[k]? := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hD
  exact feed_getElem? proj run hj hk

theorem exists_feed_position {s₀ s : JointState P} (proj : ExecutionRequests P → List α)
    (run : JointRun cfg ccfg bls s₀ s) {i : Nat} (hi : i < (feed proj run).length) :
    ∃ j k, ∃ hj : j < run.steps.length, k < (stepRequests proj run.steps[j]).length ∧
      feedPosition proj run j k = i :=
  Blanc.List.exists_flatMap_position (stepRequests proj) run.steps hi

theorem feedPosition_inj {s₀ s : JointState P} (proj : ExecutionRequests P → List α)
    (run : JointRun cfg ccfg bls s₀ s) {j k j' k' : Nat}
    (hj : j < run.steps.length) (hj' : j' < run.steps.length)
    (hk : k < (stepRequests proj run.steps[j]).length)
    (hk' : k' < (stepRequests proj run.steps[j']).length)
    (heq : feedPosition proj run j k = feedPosition proj run j' k') :
    j = j' ∧ k = k' :=
  Blanc.List.flatMap_position_inj (stepRequests proj) run.steps hj hj' hk hk' heq

end Feed

end JointFeed

end Blanc
