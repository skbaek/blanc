import Blanc.JointHistory
import Blanc.ExecutionKeptConfigured
import Blanc.ExecutionKeptClean
import Blanc.Composition.ConsolidationRequestPublicHistory

/-!
# Freeze record (G0, part cb): EIP-7251 across the layers, C-S9 (authorization, fate, balance)

Frozen statement definitions (`def … : Prop`) from G0 against Blanc `7f2a69ba` and Jaune `c30cf0a5`, on the
Electra/Fulu joint chain (`Blanc.JointRun`, `Blanc/JointHistory.lean`) paired with Prague to BPO2, classified in
`scripts/check-layering.py`, imported by `Blanc.lean`, and proved in `Blanc/Composition/`.

Jaune at this pin has no classification of `process_consolidation_request`. The freeze therefore carries its own
(`classify`, `applyOutcome`), transcribed from `JauneConsensus.processConsolidationRequest`
(`JauneConsensus/Block.lean:599`) in the spec's order, and names the equation that ties it to the spec function as an
obligation (`ClassifySound`). Jaune's G1a facts replace `classify` at proof time; the frozen statements do not depend
on their names.
-/

namespace Blanc.Corpus.Freeze.ConsolidationJoint

open Jaune JauneConsensus ExecutionTrace Blanc
open Blanc.Composition.ConsolidationRequestPublic

variable {P : Preset} {f : CFork}

/-! ## The classification of `process_consolidation_request` -/

/-- Why `process_consolidation_request` ignored a request: one constructor per early return of the consolidation
path, in the spec's order. The switch-to-compounding path is tried first; a request it does not accept falls through
to these checks. -/
inductive IgnoreReason where
  /-- Source and target keys are equal, and the request is no valid switch to compounding. -/
  | sourceIsTarget
  /-- The pending-consolidations queue is at `PENDING_CONSOLIDATIONS_LIMIT`. -/
  | queueFull
  /-- `get_consolidation_churn_limit(state) <= MIN_ACTIVATION_BALANCE`. -/
  | churnTooLow
  /-- The source key is no validator's. -/
  | unknownSource
  /-- The target key is no validator's. -/
  | unknownTarget
  /-- The source has no execution credential, or its address is not the request's source address. -/
  | badSourceCredentialOrAddress
  /-- The target has no compounding credential. -/
  | targetNotCompounding
  /-- The source is not active. -/
  | sourceNotActive
  /-- The target is not active. -/
  | targetNotActive
  /-- The source has started exiting. -/
  | sourceExiting
  /-- The target has started exiting. -/
  | targetExiting
  /-- The source has been active for less than `SHARD_COMMITTEE_PERIOD`. -/
  | sourceTooEarly
  /-- The source has a pending partial withdrawal. -/
  | sourcePendingWithdrawal
  deriving DecidableEq, Repr

/-- What `process_consolidation_request` does to one request. -/
inductive Outcome where
  /-- Ignored, for exactly one reason. -/
  | ignored (r : IgnoreReason)
  /-- A valid switch to compounding of the validator at `index`. -/
  | switchToCompounding (index : ValidatorIndex)
  /-- Every check passed: the source is set to exit and a pending consolidation `source → target` is appended. -/
  | pendingConsolidation (source target : ValidatorIndex)
  deriving DecidableEq, Repr

/-- Which outcome `process_consolidation_request` gives `cr`: the same reads and checked arithmetic as the function,
in the spec's order. Changes no state. -/
def classify (cfg : Config) (state : BeaconState P f) (cr : ConsolidationRequest) : M Outcome := do
  let site := "process_consolidation_request"
  if ← isValidSwitchToCompoundingRequest state cr then
    let some sourceIndex ← validatorIndexOf state cr.source_pubkey
      | throw (.assert s!"{site}: validator_pubkeys.index")
    return .switchToCompounding sourceIndex
  if cr.source_pubkey == cr.target_pubkey then return .ignored .sourceIsTarget
  if (← state.pendingConsolidations).length == P.PENDING_CONSOLIDATIONS_LIMIT then
    return .ignored .queueFull
  if (← getConsolidationChurnLimit cfg state).toNat ≤ P.MIN_ACTIVATION_BALANCE then
    return .ignored .churnTooLow
  let some sourceIndex ← validatorIndexOf state cr.source_pubkey | return .ignored .unknownSource
  let some targetIndex ← validatorIndexOf state cr.target_pubkey | return .ignored .unknownTarget
  let source ← state.validators.get sourceIndex.toNat site
  let target ← state.validators.get targetIndex.toNat site
  if !(hasExecutionWithdrawalCredential source &&
      source.withdrawal_credentials.toBytes.drop 12 == cr.source_address.toBytes) then
    return .ignored .badSourceCredentialOrAddress
  if !hasCompoundingWithdrawalCredential target then return .ignored .targetNotCompounding
  let current ← getCurrentEpoch state
  if !isActiveValidator source current then return .ignored .sourceNotActive
  if !isActiveValidator target current then return .ignored .targetNotActive
  if source.exit_epoch != FAR_FUTURE_EPOCH then return .ignored .sourceExiting
  if target.exit_epoch != FAR_FUTURE_EPOCH then return .ignored .targetExiting
  if current < (← U64.add? source.activation_epoch (← c64 cfg.SHARD_COMMITTEE_PERIOD) site) then
    return .ignored .sourceTooEarly
  if U64.zero < (← getPendingBalanceToWithdraw state sourceIndex) then
    return .ignored .sourcePendingWithdrawal
  return .pendingConsolidation sourceIndex targetIndex

/-- The state change of each outcome. -/
def applyOutcome (cfg : Config) (state : BeaconState P f) (_cr : ConsolidationRequest) :
    Outcome → M (BeaconState P f)
  | .ignored _ => pure state
  | .switchToCompounding index => switchToCompoundingValidator state index
  | .pendingConsolidation sourceIndex targetIndex => do
    let site := "process_consolidation_request"
    let source ← state.validators.get sourceIndex.toNat site
    let (state, exitEpoch) ← computeConsolidationEpochAndUpdateChurn cfg state source.effective_balance
    let withdrawable ← U64.add? exitEpoch (← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY) site
    let source ← state.validators.get sourceIndex.toNat site
    let validators ← state.validators.set sourceIndex.toNat
      { source with exit_epoch := exitEpoch, withdrawable_epoch := withdrawable } site
    let state := { state with validators }
    let pending ← (← state.pendingConsolidations).push
      { source_index := sourceIndex, target_index := targetIndex } site
    state.setPendingConsolidations pending

/-- **Obligation: the classification is the spec function.** `process_consolidation_request` is classify, then apply.
Every C-S9 statement below reads outcomes through `classify`; this equation is what makes them statements about the
spec function. (Jaune branch `claude/pcc-g1a-facts` proves it for a definition with this text.) -/
def ClassifySound : Prop :=
  ∀ {P : Preset} {f : CFork} (cfg : Config) (state : BeaconState P f) (cr : ConsolidationRequest),
    processConsolidationRequest cfg state cr = classify cfg state cr >>= applyOutcome cfg state cr

/-- What an outcome says about the state `m` it was classified in and the state `m'` it left. An ignored request
changes nothing. A switch is `switch_to_compounding_validator` of the validator the source key resolves to. A pending
consolidation resolves both keys, to distinct validators; appends exactly the entry `source → target`; and the target,
**at this acceptance state**, has a compounding credential, is active and has not started exiting. -/
def OutcomeMeans (m m' : BeaconState P f) (cr : ConsolidationRequest) : Outcome → Prop
  | .ignored _ => m' = m
  | .switchToCompounding V =>
      isValidSwitchToCompoundingRequest m cr = .ok true ∧ validatorIndexOf m cr.source_pubkey = .ok (some V) ∧
        switchToCompoundingValidator m V = .ok m'
  | .pendingConsolidation S T =>
      validatorIndexOf m cr.source_pubkey = .ok (some S) ∧ validatorIndexOf m cr.target_pubkey = .ok (some T) ∧
      S ≠ T ∧
      (∃ q q', m.pendingConsolidations = .ok q ∧ m'.pendingConsolidations = .ok q' ∧
        q'.toArray = q.toArray.push { source_index := S, target_index := T }) ∧
      (∃ target current, m.validators.toArray[T.toNat]? = some target ∧ getCurrentEpoch m = .ok current ∧
        hasCompoundingWithdrawalCredential target = true ∧ isActiveValidator target current = true ∧
        target.exit_epoch = FAR_FUTURE_EPOCH)

/-! ## The mid-list states of a joint step -/

/-- The states of a consolidation-requests fold: the state before each request, then the state after the last. -/
def consolidationTrace (cfg : Config) :
    BeaconState P f → List ConsolidationRequest → M (List (BeaconState P f))
  | st, [] => pure [st]
  | st, cr :: rest => do
    let st' ← processConsolidationRequest cfg st cr
    let tr ← consolidationTrace cfg st' rest
    pure (st :: tr)

/-- The states of a joint step's consolidation-requests fold, computed with the same calls as the `process_block` the
joint step runs: slot processing, the block up to the operations, the operations before the requests and the deposit
requests, the whole withdrawal-requests fold, then the consolidation requests one by one. Element `k` is the state at
which `process_consolidation_request` processes request `k`. -/
def jointConsolidationTrace (ccfg : Config) (bls : Bool) (s : JointState P)
    (b : AnySignedBlock P) : M (List (BeaconState P b.1)) := do
  let st ← jointBlockInput ccfg bls s b
  let st ← Facts.blockBeforeOps (jointCtx ccfg bls) st b.2.message
  let st ← Facts.preRequests (jointCtx ccfg bls) st b.2.message.body
  let requests ← Gated.read b.2.message.body.execution_requests
    "NewPayloadRequest: execution_requests"
  let st ← Facts.foldWithdrawalRequests ccfg st requests.withdrawals.toArray.toList
  consolidationTrace ccfg st requests.consolidations.toArray.toList

/-! ## The run's type-2 feed -/

variable {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-- The consolidation requests of a joint run step's beacon block. -/
def stepConsolidationRequests (D : JointRunStep (P := P) cfg ccfg bls) : List ConsolidationRequest :=
  match Gated.read D.block.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" with
  | .ok requests => requests.consolidations.toArray.toList
  | .error _ => []

/-- The run's type-2 feed: the beacon blocks' consolidation requests, over the run's steps in order. -/
noncomputable def consolidationFeed {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) :
    List ConsolidationRequest :=
  run.steps.flatMap stepConsolidationRequests

/-- The feed position of request `k` of step `j`: the requests of the earlier steps, plus `k`. -/
noncomputable def feedPosition {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) (j k : Nat) : Nat :=
  ((run.steps.take j).flatMap stepConsolidationRequests).length + k

/-! ## A valid joint chain for EIP-7251 -/

/-- The pending consolidations of a beacon state, as a list (empty where the field is absent, before Electra). -/
def pendingList (st : BeaconState P f) : List PendingConsolidation :=
  match st.pendingConsolidations with
  | .ok l => l.toArray.toList
  | .error _ => []

/-- **Anchor invariant (G1b).** No pending consolidation names one validator as both source and target. -/
def PendingDistinct (st : BeaconState P f) : Prop :=
  ∀ pc ∈ pendingList st, pc.source_index ≠ pc.target_index

/-- **A valid joint chain for EIP-7251**: from a checkpoint where the predeploy is at its start, a configured
execution history to the anchor's execution chain, then a joint run from the anchor. Every premise is a field;
`PendingDistinct` is scoped to `ValidJointCBalance` below so `C_S9_authorization` and `C_S9_fate` carry no unused
anchor invariant. -/
structure ValidJointC (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (checkpoint : BlockChain)
    (anchor final : JointState P) : Type where
  /-- root: canonical code, slots 0 to 3 at the inhibitor, 0, 0, 0, and no code at SYSTEM_ADDRESS, at the checkpoint
  (the mainnet form takes them from `ConsolidationCheckpointObservation`, block 22,431,083). -/
  root : CheckpointStart checkpoint.state
  /-- pre: the configured execution history from the checkpoint to the anchor's execution chain. -/
  pre : ConfiguredHistoryTrace cfg checkpoint anchor.exec
  /-- run: the joint run from the anchor. -/
  run : JointRun cfg ccfg bls anchor final
  /-- clean: no kept block of the joint history has SYSTEM_ADDRESS as a sender or a 7702 authority, and none
  creates it. -/
  clean : HistoryClean (run.toExec pre).kept
  /-- occurrences: at most 2^253 committed submissions over the joint history. -/
  occurrences : (submissions (run.toExec pre).kept).length ≤ 2 ^ 253

/-- **A valid joint chain for EIP-7251 balance accounting**: `ValidJointC` together with the anchor queue-distinctness
invariant `PendingDistinct anchor.beacon` (read only by `C_S9_balance`). -/
structure ValidJointCBalance (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (checkpoint : BlockChain)
    (anchor final : JointState P) : Type extends ValidJointC cfg ccfg bls checkpoint anchor final where
  /-- pendingDistinct: no pending consolidation at the anchor names the same validator as source and target. -/
  pendingDistinct : PendingDistinct anchor.beacon

variable {checkpoint : BlockChain} {anchor final : JointState P}

/-- The kept blocks of the joint history: the pre-anchor history extended by the run's execution blocks. -/
noncomputable abbrev ValidJointC.blocks (v : ValidJointC cfg ccfg bls checkpoint anchor final) : List KeptBlock :=
  (v.run.toExec v.pre).kept

/-- The kept blocks before the anchor. -/
noncomputable abbrev ValidJointC.preBlocks (v : ValidJointC cfg ccfg bls checkpoint anchor final) :
    List KeptBlock :=
  v.pre.kept

/-! ## C-S9 authorization -/

/-- **C-S9 authorization.** Along a valid joint chain, take step `j`, its beacon block's consolidation request `k`
(`cr`), and the mid-list state `m` at which `process_consolidation_request` processes it. If `cr` classifies in `m` as
acting on a source validator `V` (a switch to compounding of `V`, or a pending consolidation with source `V`), then:
`m` is where the step applies that outcome; `cr` is, position for position, the joint history's committed paid
submission number `E₀ + i` (`E₀` the records published before the anchor, `i` the feed position of `(j, k)`); its
source key resolves to `V` in `m` (first match); and the validator at `V` in `m` has an execution withdrawal
credential whose bytes 12..32 are `cr.source_address`, the caller the contract recorded for that submission (the
record's first 20 bytes). -/
def C_S9_authorization : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P}
    -- v: a valid joint chain for EIP-7251
    (v : ValidJointC cfg ccfg bls checkpoint anchor final)
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls}
    -- step: `D` is step `j` of the run
    (_step : v.run.steps[j]? = some D)
    {requests : ExecutionRequests P}
    -- read: the beacon block's execution requests
    (_read : Gated.read D.block.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests)
    {k : Nat} {cr : ConsolidationRequest}
    -- request: `cr` is consolidation request `k` of the block
    (_request : requests.consolidations.toArray[k]? = some cr)
    {tr : List (BeaconState P D.block.1)}
    -- trace: the step's mid-list states
    (_trace : jointConsolidationTrace ccfg bls D.pre D.block = .ok tr)
    {m : BeaconState P D.block.1}
    -- mid: `m` is the state at which request `k` is processed
    (_mid : tr[k]? = some m)
    {o : Outcome} {V : ValidatorIndex}
    -- class: the request's outcome in `m`
    (_class : classify ccfg m cr = .ok o)
    -- acts: the outcome acts on source validator `V`
    (_acts : o = .switchToCompounding V ∨ ∃ T, o = .pendingConsolidation V T),
    (∃ m', tr[k + 1]? = some m' ∧ applyOutcome ccfg m cr o = .ok m') ∧
    (consolidationFeed v.run)[feedPosition v.run j k]? = some cr ∧
    (submissions v.blocks)[(emissions v.preBlocks).length + feedPosition v.run j k]? =
      some (Ssz.serialize cr) ∧
    validatorIndexOf m cr.source_pubkey = .ok (some V) ∧
    ∃ validator, m.validators.toArray[V.toNat]? = some validator ∧
      hasExecutionWithdrawalCredential validator = true ∧
      validator.withdrawal_credentials.toBytes.drop 12 = cr.source_address.toBytes ∧
      validator.withdrawal_credentials.toBytes.drop 12 = (Ssz.serialize cr).take 20

/-! ### C-S9 authorization negative control -/

/-- Mutant of `isValidSwitchToCompoundingRequest` with the source-address equality check
(`source.withdrawal_credentials.toBytes.drop 12 == cr.source_address.toBytes`) deleted, retaining every other check. -/
def isValidSwitchToCompoundingRequestNoSourceCheck (state : BeaconState P f) (cr : ConsolidationRequest) :
    M Bool := do
  if !(cr.source_pubkey == cr.target_pubkey) then return false
  let some i ← validatorIndexOf state cr.source_pubkey | return false
  let source ← state.validators.get i.toNat "is_valid_switch_to_compounding_request"
  if !hasEth1WithdrawalCredential source then return false
  if !isActiveValidator source (← getCurrentEpoch state) then return false
  if source.exit_epoch != FAR_FUTURE_EPOCH then return false
  pure true

/-- Mutant of `processConsolidationRequest` identical to `JauneConsensus.processConsolidationRequest` except that the
source withdrawal-credential address equality check (`source.withdrawal_credentials.toBytes.drop 12 ==
cr.source_address.toBytes`) is deleted on both the switch-to-compounding path and the pending-consolidation path
(retaining `hasExecutionWithdrawalCredential source` and every preceding and subsequent guard). -/
def processConsolidationRequestNoSourceCheck (cfg : Config) (state : BeaconState P f)
    (cr : ConsolidationRequest) : M (BeaconState P f) := do
  let site := "process_consolidation_request"
  if ← isValidSwitchToCompoundingRequestNoSourceCheck state cr then
    let some sourceIndex ← validatorIndexOf state cr.source_pubkey
      | throw (.assert s!"{site}: validator_pubkeys.index")
    return (← switchToCompoundingValidator state sourceIndex)
  if cr.source_pubkey == cr.target_pubkey then return state
  if (← state.pendingConsolidations).length == P.PENDING_CONSOLIDATIONS_LIMIT then return state
  if (← getConsolidationChurnLimit cfg state).toNat ≤ P.MIN_ACTIVATION_BALANCE then return state
  let some sourceIndex ← validatorIndexOf state cr.source_pubkey | return state
  let some targetIndex ← validatorIndexOf state cr.target_pubkey | return state
  let source ← state.validators.get sourceIndex.toNat site
  let target ← state.validators.get targetIndex.toNat site
  if !hasExecutionWithdrawalCredential source then return state
  if !hasCompoundingWithdrawalCredential target then return state
  let current ← getCurrentEpoch state
  if !isActiveValidator source current then return state
  if !isActiveValidator target current then return state
  if source.exit_epoch != FAR_FUTURE_EPOCH then return state
  if target.exit_epoch != FAR_FUTURE_EPOCH then return state
  if current < (← U64.add? source.activation_epoch (← c64 cfg.SHARD_COMMITTEE_PERIOD) site) then
    return state
  if U64.zero < (← getPendingBalanceToWithdraw state sourceIndex) then return state
  let (state, exitEpoch) ← computeConsolidationEpochAndUpdateChurn cfg state source.effective_balance
  let withdrawable ← U64.add? exitEpoch (← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY) site
  let source ← state.validators.get sourceIndex.toNat site
  let validators ← state.validators.set sourceIndex.toNat
    { source with exit_epoch := exitEpoch, withdrawable_epoch := withdrawable } site
  let state := { state with validators }
  let pending ← (← state.pendingConsolidations).push
    { source_index := sourceIndex, target_index := targetIndex } site
  state.setPendingConsolidations pending

/-- **C-S9 authorization negative control.** Closed minimal-preset Electra witnesses on **both** acting paths where
the source validator carries an execution withdrawal credential whose address differs from `cr.source_address`, while
every preceding and subsequent guard passes:
(1) on the consolidation path (`cr.source_pubkey ≠ cr.target_pubkey`), real `processConsolidationRequest` ignores the
request (`classify = .ok (.ignored .badSourceCredentialOrAddress)`, `post = st`), whereas
`processConsolidationRequestNoSourceCheck` mutates state and appends `{ source_index := S, target_index := T }` to
`pending_consolidations`;
(2) on the switch path (`cr.source_pubkey = cr.target_pubkey`), real `processConsolidationRequest` ignores the request
(`classify = .ok (.ignored .sourceIsTarget)`, `post = stSw`), whereas `processConsolidationRequestNoSourceCheck`
switches the validator's credential (`stSw' ≠ stSw`). -/
def C_S9_auth_control : Prop :=
  (∃ (st : BeaconState Preset.minimal .electra) (cr : ConsolidationRequest)
      (S T : ValidatorIndex) (source : Validator),
    cr.source_pubkey ≠ cr.target_pubkey ∧
    validatorIndexOf st cr.source_pubkey = .ok (some S) ∧
    validatorIndexOf st cr.target_pubkey = .ok (some T) ∧
    st.validators.toArray[S.toNat]? = some source ∧
    hasExecutionWithdrawalCredential source = true ∧
    source.withdrawal_credentials.toBytes.drop 12 ≠ cr.source_address.toBytes ∧
    classify Config.minimal st cr = .ok (.ignored .badSourceCredentialOrAddress) ∧
    processConsolidationRequest Config.minimal st cr = .ok st ∧
    ∃ st', processConsolidationRequestNoSourceCheck Config.minimal st cr = .ok st' ∧
      st' ≠ st ∧ pendingList st' = pendingList st ++ [{ source_index := S, target_index := T }]) ∧
  (∃ (stSw : BeaconState Preset.minimal .electra) (crSw : ConsolidationRequest)
      (V : ValidatorIndex) (source : Validator),
    crSw.source_pubkey = crSw.target_pubkey ∧
    validatorIndexOf stSw crSw.source_pubkey = .ok (some V) ∧
    stSw.validators.toArray[V.toNat]? = some source ∧
    hasEth1WithdrawalCredential source = true ∧
    source.withdrawal_credentials.toBytes.drop 12 ≠ crSw.source_address.toBytes ∧
    classify Config.minimal stSw crSw = .ok (.ignored .sourceIsTarget) ∧
    processConsolidationRequest Config.minimal stSw crSw = .ok stSw ∧
    ∃ stSw', processConsolidationRequestNoSourceCheck Config.minimal stSw crSw = .ok stSw' ∧
      stSw' ≠ stSw)

/-! ## C-S9 fate -/

/-- **C-S9 fate.** Along a valid joint chain, every committed submission `n` of the joint history meets exactly one of
three fates (the index ranges are disjoint):
* (a) `n < E₀`: it is record `n` published before the anchor; no consensus claim;
* (b) `E₀ ≤ n < E`: it is the serialization of consolidation request `k` of the beacon block of step `j`, for the
  only `(j, k)` at feed position `n − E₀`; at its mid-list state `m` it has exactly one outcome `o` of the ordered
  classification, the step's next mid-list state `m'` is that outcome applied, and `OutcomeMeans m m' cr o`;
* (c) `E ≤ n`: it is entry `n − E` of the final stored queue. -/
def C_S9_fate : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P}
    -- v: a valid joint chain for EIP-7251
    (v : ValidJointC cfg ccfg bls checkpoint anchor final)
    {n : Nat}
    -- occurrence: `n` indexes a committed submission of the joint history
    (hn : n < (submissions v.blocks).length),
    (n < (emissions v.preBlocks).length ∧ (emissions v.preBlocks)[n]? = some (submissions v.blocks)[n]) ∨
    ((emissions v.preBlocks).length ≤ n ∧ n < (emissions v.blocks).length ∧
      ∃ j k, ∃ D : JointRunStep (P := P) cfg ccfg bls, ∃ requests : ExecutionRequests P,
      ∃ cr, ∃ tr : List (BeaconState P D.block.1), ∃ m : BeaconState P D.block.1,
        v.run.steps[j]? = some D ∧
        Gated.read D.block.2.message.body.execution_requests
          "NewPayloadRequest: execution_requests" = .ok requests ∧
        requests.consolidations.toArray[k]? = some cr ∧
        feedPosition v.run j k = n - (emissions v.preBlocks).length ∧
        Ssz.serialize cr = (submissions v.blocks)[n] ∧
        jointConsolidationTrace ccfg bls D.pre D.block = .ok tr ∧ tr[k]? = some m ∧
        ∃ o, classify ccfg m cr = .ok o ∧
          (∀ o', classify ccfg m cr = .ok o' → o' = o) ∧
          ∃ m', tr[k + 1]? = some m' ∧ applyOutcome ccfg m cr o = .ok m' ∧ OutcomeMeans m m' cr o ∧
          (∀ j' k' (D' : JointRunStep (P := P) cfg ccfg bls) (cr' : ConsolidationRequest),
            v.run.steps[j']? = some D' → (stepConsolidationRequests D')[k']? = some cr' →
              feedPosition v.run j' k' = n - (emissions v.preBlocks).length → j' = j ∧ k' = k)) ∨
    ((emissions v.blocks).length ≤ n ∧
      (remainingQueue final.exec.state)[n - (emissions v.blocks).length]? = some (submissions v.blocks)[n])

/-! ### C-S9 fate witnesses and seam negative control -/

/-- **C-S9 fate outcome and priority witnesses.**
(1) Every one of the 13 `IgnoreReason`s occurs on a closed minimal-preset Electra state and request (with
`processConsolidationRequest` returning `st`), and both acting outcomes (`switchToCompounding` and
`pendingConsolidation`) occur with actual state mutation.
(2) Competing-reason priority witnesses in the spec's exact check order, explicitly accounting for the
`isValidSwitchToCompoundingRequest` switch path running **before** ordinary consolidation guards:
* a valid switch (`source_pubkey = target_pubkey`, matching `0x01` credential, active, non-exiting) succeeds as
  `.switchToCompounding` even when `pending_consolidations` is at `PENDING_CONSOLIDATIONS_LIMIT` and
  `consolidationChurnLimit ≤ MIN_ACTIVATION_BALANCE`;
* an invalid equal-key request (`source_pubkey = target_pubkey`, not a valid switch) classifies `.ignored .sourceIsTarget`
  ahead of both `queueFull` and `churnTooLow`;
* with distinct keys, `queueFull` takes priority over `churnTooLow` and `unknownSource`;
* `unknownSource` takes priority over `unknownTarget` when neither pubkey is in the registry;
* `badSourceCredentialOrAddress` takes priority over `targetNotCompounding`. -/
def C_S9_fate_witnesses : Prop :=
  (∀ r : IgnoreReason,
    ∃ (st : BeaconState Preset.minimal .electra) (cr : ConsolidationRequest),
      classify Config.minimal st cr = .ok (.ignored r) ∧
      processConsolidationRequest Config.minimal st cr = .ok st) ∧
  (∃ (st st' : BeaconState Preset.minimal .electra) (cr : ConsolidationRequest) (v : ValidatorIndex),
    classify Config.minimal st cr = .ok (.switchToCompounding v) ∧
    processConsolidationRequest Config.minimal st cr = .ok st' ∧ st' ≠ st) ∧
  (∃ (st st' : BeaconState Preset.minimal .electra) (cr : ConsolidationRequest) (s t : ValidatorIndex),
    classify Config.minimal st cr = .ok (.pendingConsolidation s t) ∧
    processConsolidationRequest Config.minimal st cr = .ok st' ∧
    pendingList st' = pendingList st ++ [{ source_index := s, target_index := t }]) ∧
  -- Priority 1: valid switch precedes queueFull and churnTooLow
  (∃ (st : BeaconState Preset.minimal .electra) (cr : ConsolidationRequest)
      (q : SszList PendingConsolidation Preset.minimal.PENDING_CONSOLIDATIONS_LIMIT) (churn : Gwei)
      (v : ValidatorIndex),
    st.pendingConsolidations = .ok q ∧ q.length = Preset.minimal.PENDING_CONSOLIDATIONS_LIMIT ∧
    getConsolidationChurnLimit Config.minimal st = .ok churn ∧
    churn.toNat ≤ Preset.minimal.MIN_ACTIVATION_BALANCE ∧
    classify Config.minimal st cr = .ok (.switchToCompounding v)) ∧
  -- Priority 2: failed equal-key switch (`sourceIsTarget`) precedes queueFull and churnTooLow
  (∃ (st : BeaconState Preset.minimal .electra) (cr : ConsolidationRequest)
      (q : SszList PendingConsolidation Preset.minimal.PENDING_CONSOLIDATIONS_LIMIT) (churn : Gwei),
    cr.source_pubkey = cr.target_pubkey ∧
    isValidSwitchToCompoundingRequest st cr = .ok false ∧
    st.pendingConsolidations = .ok q ∧ q.length = Preset.minimal.PENDING_CONSOLIDATIONS_LIMIT ∧
    getConsolidationChurnLimit Config.minimal st = .ok churn ∧
    churn.toNat ≤ Preset.minimal.MIN_ACTIVATION_BALANCE ∧
    classify Config.minimal st cr = .ok (.ignored .sourceIsTarget)) ∧
  -- Priority 3: queueFull precedes churnTooLow and unknownSource
  (∃ (st : BeaconState Preset.minimal .electra) (cr : ConsolidationRequest)
      (q : SszList PendingConsolidation Preset.minimal.PENDING_CONSOLIDATIONS_LIMIT) (churn : Gwei),
    cr.source_pubkey ≠ cr.target_pubkey ∧
    st.pendingConsolidations = .ok q ∧ q.length = Preset.minimal.PENDING_CONSOLIDATIONS_LIMIT ∧
    getConsolidationChurnLimit Config.minimal st = .ok churn ∧
    churn.toNat ≤ Preset.minimal.MIN_ACTIVATION_BALANCE ∧
    validatorIndexOf st cr.source_pubkey = .ok none ∧
    classify Config.minimal st cr = .ok (.ignored .queueFull)) ∧
  -- Priority 4: unknownSource precedes unknownTarget
  (∃ (st : BeaconState Preset.minimal .electra) (cr : ConsolidationRequest),
    cr.source_pubkey ≠ cr.target_pubkey ∧
    validatorIndexOf st cr.source_pubkey = .ok none ∧
    validatorIndexOf st cr.target_pubkey = .ok none ∧
    classify Config.minimal st cr = .ok (.ignored .unknownSource)) ∧
  -- Priority 5: badSourceCredentialOrAddress precedes targetNotCompounding
  (∃ (st : BeaconState Preset.minimal .electra) (cr : ConsolidationRequest)
      (S T : ValidatorIndex) (source target : Validator),
    cr.source_pubkey ≠ cr.target_pubkey ∧
    validatorIndexOf st cr.source_pubkey = .ok (some S) ∧
    validatorIndexOf st cr.target_pubkey = .ok (some T) ∧
    st.validators.toArray[S.toNat]? = some source ∧
    st.validators.toArray[T.toNat]? = some target ∧
    ¬ (hasExecutionWithdrawalCredential source = true ∧
      source.withdrawal_credentials.toBytes.drop 12 = cr.source_address.toBytes) ∧
    hasCompoundingWithdrawalCredential target = false ∧
    classify Config.minimal st cr = .ok (.ignored .badSourceCredentialOrAddress))

/-- Positional fate partition over `preEmissions`, per-step execution emissions `execSteps`, consensus request lists
`feedSteps`, remaining queue `rem`, and committed submissions `subs`: the exact three-range positional alignment of
`C_S9_fate`. -/
def PositionalFate (preEmissions : List Bytes) (execSteps : List (List Bytes))
    (feedSteps : List (List ConsolidationRequest)) (rem subs : List Bytes) : Prop :=
  let E₀ := preEmissions.length
  let E := (preEmissions ++ execSteps.flatten).length
  ∀ n < subs.length,
    (n < E₀ ∧ preEmissions[n]? = subs[n]?) ∨
    (E₀ ≤ n ∧ n < E ∧
      ∃ j k crs cr,
        feedSteps[j]? = some crs ∧ crs[k]? = some cr ∧
        (feedSteps.take j).flatten.length + k = n - E₀ ∧
        subs[n]? = some (Ssz.serialize cr)) ∨
    (E ≤ n ∧ rem[n - E]? = subs[n]?)

/-- **C-S9 seam negative control.**
(1) Actual `jointStep` seam refusal: any block whose execution body produces `bout.requests` unequal to the beacon
block's `req.executionRequests` is rejected by `jointStep`.
(2) A closed one-block-late / shifted consensus seam witness falsifying the positional request-to-submission clause of
`C_S9_fate`: on a two-step trace committing `[cr₀, cr₁]` (`cr₀ ≠ cr₁`), the aligned seam `[[cr₀], [cr₁]]` satisfies
`PositionalFate`, whereas both the one-block-late seam `[[], [cr₀]]` (step `j + 1` carrying step `j`'s requests) and
the swapped/shifted seam `[[cr₁], [cr₀]]` falsify `PositionalFate`. -/
def C_S9_seam_control : Prop :=
  (∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s s' : JointState P}
      {b : AnySignedBlock P} {req : NewPayloadRequest P} {fk : Jaune.Fork} {st : State} {bout : BlockOutput},
    NewPayloadRequest.ofBlock b.2.message = .ok req →
    cfg.forkAt (payloadToBlock req).header.number (payloadToBlock req).header.timestamp = .ok fk →
    applyBody (initBenv fk s.exec (payloadToBlock req).header) (payloadToBlock req).txs
      (payloadToBlock req).ommers (payloadToBlock req).wds = .ok (st, bout) →
    bout.requests ≠ req.executionRequests →
    jointStep cfg ccfg bls s b ≠ .ok s') ∧
  ∃ (cr₀ cr₁ : ConsolidationRequest),
    cr₀ ≠ cr₁ ∧
    let r₀ := Ssz.serialize cr₀
    let r₁ := Ssz.serialize cr₁
    let execSteps := [[r₀], [r₁]]
    let subs := [r₀, r₁]
    PositionalFate [] execSteps [[cr₀], [cr₁]] [] subs ∧
    ¬ PositionalFate [] execSteps [[], [cr₀]] [] subs ∧
    ¬ PositionalFate [] execSteps [[cr₁], [cr₀]] [] subs

/-! ## C-S9 balance -/

/-- `process_epoch` up to, and excluding, `process_pending_consolidations` (Electra on): the state it hands on. -/
def epochBeforeConsolidations (ctx : Ctx) (state : BeaconState P f) : M (BeaconState P f) := do
  let cfg := ctx.cfg
  let state ← processJustificationAndFinalization cfg state
  let state ← processInactivityUpdates cfg state
  let state ← processRewardsAndPenalties cfg state
  let state ← processRegistryUpdates cfg state
  let state ← processSlashings cfg state
  let state ← processEth1DataReset cfg state
  processPendingDeposits ctx state

/-- `process_epoch` after `process_pending_consolidations` (Electra and Fulu): effective-balance updates through
`process_proposer_lookahead`. -/
def epochAfterConsolidations (ctx : Ctx) (state : BeaconState P f) : M (BeaconState P f) := do
  let cfg := ctx.cfg
  let state ← processEffectiveBalanceUpdates cfg state
  let state ← processSlashingsReset cfg state
  let state ← processRandaoMixesReset cfg state
  let state ← processHistoricalSummariesUpdate cfg state
  let state ← processParticipationFlagUpdates cfg state
  let state ← processSyncCommitteeUpdates ctx state
  if f.atLeast .fulu then processProposerLookahead cfg state else pure state

/-- `ConsolidationCall ctx st n w`: `process_slots`, run for `n` further slots from `st`, hands `w` to
`process_pending_consolidations`. The three constructors are the loop body of `processSlotsWith`
(`JauneConsensus/Transition.lean:45`): an epoch boundary now; a later one after this boundary's `process_epoch`; a
later one after a slot that is no boundary. `process_slots ctx st slot` runs `slot − st.slot` slots. -/
inductive ConsolidationCall (ctx : Ctx) : BeaconState P f → Nat → BeaconState P f → Prop
  | here {st s1 w : BeaconState P f} {n : Nat} {next spe r : U64}
      (slot : processSlot st = .ok s1)
      (succ : s1.slot.add? U64.one "process_slots: state.slot + 1" = .ok next)
      (perEpoch : u64 P.SLOTS_PER_EPOCH "SLOTS_PER_EPOCH" = .ok spe)
      (rem : next.mod? spe "process_slots: (state.slot + 1) % SLOTS_PER_EPOCH" = .ok r)
      (boundary : r.toNat = 0)
      (input : epochBeforeConsolidations ctx s1 = .ok w) :
      ConsolidationCall ctx st (n + 1) w
  | afterEpoch {st s1 s2 w : BeaconState P f} {n : Nat} {next spe r : U64}
      (slot : processSlot st = .ok s1)
      (succ : s1.slot.add? U64.one "process_slots: state.slot + 1" = .ok next)
      (perEpoch : u64 P.SLOTS_PER_EPOCH "SLOTS_PER_EPOCH" = .ok spe)
      (rem : next.mod? spe "process_slots: (state.slot + 1) % SLOTS_PER_EPOCH" = .ok r)
      (boundary : r.toNat = 0)
      (epoch : processEpoch ctx s1 = .ok s2)
      (later : ConsolidationCall ctx { s2 with slot := next } n w) :
      ConsolidationCall ctx st (n + 1) w
  | afterSlot {st s1 w : BeaconState P f} {n : Nat} {next spe r : U64}
      (slot : processSlot st = .ok s1)
      (succ : s1.slot.add? U64.one "process_slots: state.slot + 1" = .ok next)
      (perEpoch : u64 P.SLOTS_PER_EPOCH "SLOTS_PER_EPOCH" = .ok spe)
      (rem : next.mod? spe "process_slots: (state.slot + 1) % SLOTS_PER_EPOCH" = .ok r)
      (inside : r.toNat ≠ 0)
      (later : ConsolidationCall ctx { s1 with slot := next } n w) :
      ConsolidationCall ctx st (n + 1) w

/-- `SlotsConsolidationCalls ctx n st st' calls`: running `n` iterations of the `process_slots` loop from `st`
(at Electra or Fulu) reaches `st'` and makes, in exact chronological order, the `process_pending_consolidations` calls
`calls` (each `(w, w')` being the pre- and post-`BeaconState` of `processPendingConsolidations`). -/
inductive SlotsConsolidationCalls (ctx : Ctx) :
    Nat → BeaconState P f → BeaconState P f → List (BeaconState P f × BeaconState P f) → Prop
  | zero {st : BeaconState P f} :
      SlotsConsolidationCalls ctx 0 st st []
  | epoch {n : Nat} {st s1 w w' s2 st' : BeaconState P f} {next spe r : U64}
      {calls : List (BeaconState P f × BeaconState P f)}
      (slot : processSlot st = .ok s1)
      (succ : s1.slot.add? U64.one "process_slots: state.slot + 1" = .ok next)
      (perEpoch : u64 P.SLOTS_PER_EPOCH "SLOTS_PER_EPOCH" = .ok spe)
      (rem : next.mod? spe "process_slots: (state.slot + 1) % SLOTS_PER_EPOCH" = .ok r)
      (boundary : r.toNat = 0)
      (before : epochBeforeConsolidations ctx s1 = .ok w)
      (call : processPendingConsolidations ctx.cfg w = .ok w')
      (after : epochAfterConsolidations ctx w' = .ok s2)
      (rest : SlotsConsolidationCalls ctx n { s2 with slot := next } st' calls) :
      SlotsConsolidationCalls ctx (n + 1) st st' ((w, w') :: calls)
  | nonBoundary {n : Nat} {st s1 st' : BeaconState P f} {next spe r : U64}
      {calls : List (BeaconState P f × BeaconState P f)}
      (slot : processSlot st = .ok s1)
      (succ : s1.slot.add? U64.one "process_slots: state.slot + 1" = .ok next)
      (perEpoch : u64 P.SLOTS_PER_EPOCH "SLOTS_PER_EPOCH" = .ok spe)
      (rem : next.mod? spe "process_slots: (state.slot + 1) % SLOTS_PER_EPOCH" = .ok r)
      (inside : r.toNat ≠ 0)
      (rest : SlotsConsolidationCalls ctx n { s1 with slot := next } st' calls) :
      SlotsConsolidationCalls ctx (n + 1) st st' calls

/-- `ProcessSlotsCalls ctx st targetSlot st' calls`: `processSlots ctx st targetSlot = .ok st'` with exact chronological
`process_pending_consolidations` call trace `calls`. -/
def ProcessSlotsCalls (ctx : Ctx) (st : BeaconState P f) (targetSlot : Slot) (st' : BeaconState P f)
    (calls : List (BeaconState P f × BeaconState P f)) : Prop :=
  st.slot < targetSlot ∧
  processSlots ctx st targetSlot = .ok st' ∧
  SlotsConsolidationCalls ctx (targetSlot.toNat - st.slot.toNat) st st' calls

/-- One `process_pending_consolidations` call at its consensus fork (`electra` or `fulu`), recording the exact input
state `pre` and output state `post` of `processPendingConsolidations`. -/
structure AnyConsolidationCall (P : Preset) where
  fork : CFork
  pre : BeaconState P fork
  post : BeaconState P fork

/-- Lift same-fork `(pre, post)` pairs to `AnyConsolidationCall P`. -/
def liftCalls {f : CFork} (calls : List (BeaconState P f × BeaconState P f)) : List (AnyConsolidationCall P) :=
  calls.map fun (w, w') => ⟨f, w, w'⟩

/-- Step-level relation identifying the exact ordered `process_pending_consolidations` calls of a joint step's
slot-processing phase (`jointBlockInput`), across same-fork Electra, same-fork Fulu, and **both** halves
(pre-upgrade Electra `processSlots` and post-upgrade Fulu `processSlots`) of an Electra → Fulu crossing. -/
inductive StepConsolidationCalls (ccfg : Config) (bls : Bool) :
    (s : JointState P) → (b : AnySignedBlock P) → BeaconState P b.1 → List (AnyConsolidationCall P) → Prop
  | electra {beacon stIn : BeaconState P .electra} {exec : BlockChain} {sb : SignedBeaconBlock P .electra}
      {calls : List (BeaconState P .electra × BeaconState P .electra)}
      (slots : ProcessSlotsCalls (jointCtx ccfg bls) beacon sb.message.slot stIn calls) :
      StepConsolidationCalls ccfg bls ⟨.electra, beacon, exec⟩ ⟨.electra, sb⟩ stIn (liftCalls calls)
  | fulu {beacon stIn : BeaconState P .fulu} {exec : BlockChain} {sb : SignedBeaconBlock P .fulu}
      {calls : List (BeaconState P .fulu × BeaconState P .fulu)}
      (slots : ProcessSlotsCalls (jointCtx ccfg bls) beacon sb.message.slot stIn calls) :
      StepConsolidationCalls ccfg bls ⟨.fulu, beacon, exec⟩ ⟨.fulu, sb⟩ stIn (liftCalls calls)
  | cross {beacon preUp : BeaconState P .electra} {postUp stIn : BeaconState P .fulu}
      {exec : BlockChain} {sb : SignedBeaconBlock P .fulu} {forkSlot : Slot}
      {electraCalls : List (BeaconState P .electra × BeaconState P .electra)}
      {fuluCalls : List (BeaconState P .fulu × BeaconState P .fulu)}
      (hForkSlot : U64.ofNat? (fuluForkSlot (P := P) ccfg) "joint step: Fulu fork slot" = .ok forkSlot)
      (preSlots : (beacon.slot < forkSlot ∧
          ProcessSlotsCalls (jointCtx ccfg bls) beacon forkSlot preUp electraCalls) ∨
        (¬ beacon.slot < forkSlot ∧ preUp = beacon ∧ electraCalls = []))
      (upgrade : upgradeToFulu ccfg preUp = .ok postUp)
      (postSlots : ((sb.message.slot == postUp.slot) = true ∧ stIn = postUp ∧ fuluCalls = []) ∨
        ((sb.message.slot == postUp.slot) = false ∧
          ProcessSlotsCalls (jointCtx ccfg bls) postUp sb.message.slot stIn fuluCalls)) :
      StepConsolidationCalls ccfg bls ⟨.electra, beacon, exec⟩ ⟨.fulu, sb⟩ stIn
        (liftCalls electraCalls ++ liftCalls fuluCalls)

/-- **One applied pending consolidation**, from the loop state `u` to `u'`. The amount is
`min(source balance, source effective balance)`, the balance read in `u`. No validator record changes, and no
balance but the source's and the target's. For distinct source and target, the source loses exactly the amount and
the target gains exactly the amount. -/
def Transfers (u u' : BeaconState P f) (pc : PendingConsolidation) (source : Validator) : Prop :=
  ∃ sb : Gwei, u.balances.toArray[pc.source_index.toNat]? = some sb ∧
    u'.validators = u.validators ∧
    (∀ i, i ≠ pc.source_index.toNat → i ≠ pc.target_index.toNat →
      u'.balances.toArray[i]? = u.balances.toArray[i]?) ∧
    (pc.source_index ≠ pc.target_index →
      ∃ tb sb' tb' : Gwei, u.balances.toArray[pc.target_index.toNat]? = some tb ∧
        u'.balances.toArray[pc.source_index.toNat]? = some sb' ∧
        u'.balances.toArray[pc.target_index.toNat]? = some tb' ∧
        sb'.toNat = sb.toNat - min sb.toNat source.effective_balance.toNat ∧
        tb'.toNat = tb.toNat + min sb.toNat source.effective_balance.toNat)

/-- **Derived unguarded per-account balance transfer** from loop state `u` to `u'`: without any
`pc.source_index ≠ pc.target_index` guard, the source loses `min(sb, effective_balance)` and the target gains
`min(sb, effective_balance)`, while all other balances and all validator records stay unchanged. `Transfers` combined
with `PendingDistinct` (from `ValidJointCBalance`) yields `UnguardedTransfers` at every unslashed entry consumed before
stop. -/
def UnguardedTransfers (u u' : BeaconState P f) (pc : PendingConsolidation) (source : Validator) : Prop :=
  ∃ sb tb sb' tb' : Gwei,
    u.balances.toArray[pc.source_index.toNat]? = some sb ∧
    u.balances.toArray[pc.target_index.toNat]? = some tb ∧
    u'.balances.toArray[pc.source_index.toNat]? = some sb' ∧
    u'.balances.toArray[pc.target_index.toNat]? = some tb' ∧
    u'.validators = u.validators ∧
    (∀ i, i ≠ pc.source_index.toNat → i ≠ pc.target_index.toNat →
      u'.balances.toArray[i]? = u.balances.toArray[i]?) ∧
    sb'.toNat = sb.toNat - min sb.toNat source.effective_balance.toNat ∧
    tb'.toNat = tb.toNat + min sb.toNat source.effective_balance.toNat

/-- **The reusable local law of `process_pending_consolidations`**, at any state. A successful run consumes a prefix of
`n` entries of the queue, through loop states `us` (the state before each consumed entry, then the state after the
last). Each consumed entry is skipped, changing nothing, exactly when its source is slashed; otherwise its source is
withdrawable by the next epoch and it is applied (`Transfers`). The first entry not consumed, if any, has an unslashed
source that is not yet withdrawable, and nothing after it is read. The conditions name the source's record only: at
processing the target is asked for nothing, and no validator record is written. -/
def PendingConsolidationsLaw : Prop :=
  ∀ {P : Preset} {f : CFork} (cfg : Config) {w w' : BeaconState P f}
    {pending : SszList PendingConsolidation P.PENDING_CONSOLIDATIONS_LIMIT} {current nextEpoch : Epoch}
    -- run: the function succeeds
    (_run : processPendingConsolidations cfg w = .ok w')
    -- queue: the queue it reads
    (_queue : w.pendingConsolidations = .ok pending)
    -- epoch, next: the epoch it compares against
    (_epoch : getCurrentEpoch w = .ok current)
    (_next : current.add? U64.one "process_pending_consolidations" = .ok nextEpoch),
    ∃ (n : Nat) (us : List (BeaconState P f)),
      n ≤ pending.toArray.size ∧ us.length = n + 1 ∧ us[0]? = some w ∧
      (∃ last rest, us[n]? = some last ∧ w'.pendingConsolidations = .ok rest ∧
        rest.toArray.toList = pending.toArray.toList.drop n ∧
        w'.balances = last.balances ∧ w'.validators = w.validators) ∧
      (∀ i < n, ∀ pc u u', pending.toArray[i]? = some pc → us[i]? = some u → us[i + 1]? = some u' →
        ∃ source, w.validators.toArray[pc.source_index.toNat]? = some source ∧
          ((source.slashed = true ∧ u' = u) ∨
            (source.slashed = false ∧ ¬ nextEpoch < source.withdrawable_epoch ∧ Transfers u u' pc source))) ∧
      (∀ pc, pending.toArray[n]? = some pc →
        ∃ source, w.validators.toArray[pc.source_index.toNat]? = some source ∧
          source.slashed = false ∧ nextEpoch < source.withdrawable_epoch)

/-- **Local effect of one concrete `process_pending_consolidations` call `(w, w')`** consuming prefix `consumed` under
`PendingDistinct w`: `pendingList w = consumed ++ pendingList w'`, through loop states `us`, where each consumed entry
either has a slashed source (`u' = u`) or has an unslashed withdrawable source and satisfies **both** `Transfers` and
the unguarded per-account `UnguardedTransfers`; and any first remaining entry `(pendingList w')[0]?` has an unslashed
source not yet withdrawable. -/
def CallConsolidationEffect (cfg : Config) {f : CFork} (w w' : BeaconState P f)
    (consumed : List PendingConsolidation) : Prop :=
  processPendingConsolidations cfg w = .ok w' ∧
  pendingList w = consumed ++ pendingList w' ∧
  PendingDistinct w ∧
  ∃ (current nextEpoch : Epoch) (us : List (BeaconState P f)),
    getCurrentEpoch w = .ok current ∧
    current.add? U64.one "process_pending_consolidations" = .ok nextEpoch ∧
    us.length = consumed.length + 1 ∧ us[0]? = some w ∧
    (∃ last, us[consumed.length]? = some last ∧ w'.balances = last.balances ∧ w'.validators = w.validators) ∧
    (∀ i < consumed.length, ∀ pc u u',
      consumed[i]? = some pc → us[i]? = some u → us[i + 1]? = some u' →
      ∃ source, w.validators.toArray[pc.source_index.toNat]? = some source ∧
        ((source.slashed = true ∧ u' = u) ∨
          (source.slashed = false ∧ ¬ nextEpoch < source.withdrawable_epoch ∧
            Transfers u u' pc source ∧ UnguardedTransfers u u' pc source))) ∧
    (∀ pc, (pendingList w')[0]? = some pc →
      ∃ source, w.validators.toArray[pc.source_index.toNat]? = some source ∧
        source.slashed = false ∧ nextEpoch < source.withdrawable_epoch)

/-- **Every call sees a suffix.** Whatever slot processing hands to `process_pending_consolidations` holds a suffix
of the queue it started from, and the Fulu upgrade keeps the queue. -/
def PendingConsolidationsWindow : Prop :=
  (∀ {P : Preset} {f : CFork} (ctx : Ctx) {st w : BeaconState P f} {n : Nat},
    ConsolidationCall ctx st n w → ∃ d, pendingList w = (pendingList st).drop d) ∧
  (∀ {P : Preset} (ccfg : Config) {pre : BeaconState P .electra} {post : BeaconState P .fulu},
    upgradeToFulu ccfg pre = .ok post → pendingList post = pendingList pre)

/-! ### Ordered accepted-consolidation stream -/

/-- From a step's mid-list states `tr` and consolidation requests `crs`, collect in exact intra-block request order
`(k, pc)` for every request `k` whose `classify` outcome in `tr[k]` is `.pendingConsolidation`. -/
def traceAccepted (cfg : Config) (tr : List (BeaconState P f)) (crs : List ConsolidationRequest) :
    List (Nat × PendingConsolidation) :=
  (List.range crs.length).filterMap fun k =>
    match tr[k]?, crs[k]? with
    | some m, some cr =>
      match classify cfg m cr with
      | .ok (.pendingConsolidation s t) => some (k, { source_index := s, target_index := t })
      | _ => none
    | _, _ => none

/-- The `(reqIndex, pc)` pairs accepted in step `D`, in intra-block request order, preserving multiplicity. -/
def stepAcceptedWithPos (D : JointRunStep (P := P) cfg ccfg bls) : List (Nat × PendingConsolidation) :=
  match jointConsolidationTrace ccfg bls D.pre D.block with
  | .ok tr => traceAccepted ccfg tr (stepConsolidationRequests D)
  | .error _ => []

/-- The pending consolidations accepted in step `D`, in intra-block request order, preserving multiplicity. -/
def stepAccepted (D : JointRunStep (P := P) cfg ccfg bls) : List PendingConsolidation :=
  (stepAcceptedWithPos D).map Prod.snd

/-- The `(stepIndex, reqIndex, pc)` records accepted in the first `j` steps of `run`, in exact lexicographic
`(step, request)` order, preserving multiplicity. -/
noncomputable def runAcceptedRecordsUpTo {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) (j : Nat) :
    List (Nat × Nat × PendingConsolidation) :=
  (List.range (min j run.steps.length)).flatMap fun j' =>
    match run.steps[j']? with
    | some D => (stepAcceptedWithPos D).map fun (k, pc) => (j', k, pc)
    | none => []

/-- All `(stepIndex, reqIndex, pc)` records accepted across the entire `run`, in exact step and intra-block request
order, preserving multiplicity. -/
noncomputable def runAcceptedRecords {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) :
    List (Nat × Nat × PendingConsolidation) :=
  runAcceptedRecordsUpTo run run.steps.length

/-- Pending consolidations accepted in the first `j` steps of `run`, in exact step and intra-block request order. -/
noncomputable def runAcceptedUpTo {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) (j : Nat) :
    List PendingConsolidation :=
  (runAcceptedRecordsUpTo run j).map fun (_, _, pc) => pc

/-- Pending consolidations accepted across the entire `run`, in exact step and intra-block request order. -/
noncomputable def runAccepted {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) :
    List PendingConsolidation :=
  runAcceptedUpTo run run.steps.length

/-- The ordered accepted-entry stream up to step `j`: `anchor.beacon`'s initial pending queue followed in exact order
by `runAcceptedUpTo run j`. -/
noncomputable def acceptedStreamUpTo {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) (j : Nat) :
    List PendingConsolidation :=
  pendingList s₀.beacon ++ runAcceptedUpTo run j

/-- The full ordered accepted-entry stream through the end of `run`: `anchor.beacon`'s initial pending queue followed
in exact order by `runAccepted run`. -/
noncomputable def acceptedStream {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) :
    List PendingConsolidation :=
  pendingList s₀.beacon ++ runAccepted run

/-- Acceptance-time witness for a record `(j, k, pc)` in `runAcceptedRecords run`: at step `j`, request `k`, mid-list
state `m` (transitioning to `m'`), `processConsolidationRequest` classified `cr` as
`.pendingConsolidation pc.source_index pc.target_index` and satisfied `OutcomeMeans m m' cr ...` — in particular
`pc.source_index ≠ pc.target_index`, and at `m` the target validator was active, compounding, and had
`exit_epoch = FAR_FUTURE_EPOCH` (with no target signature or target address check required). -/
def AcceptedRecordWitness {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s)
    (j k : Nat) (pc : PendingConsolidation) : Prop :=
  ∃ D : JointRunStep (P := P) cfg ccfg bls, ∃ requests : ExecutionRequests P,
  ∃ cr : ConsolidationRequest, ∃ tr : List (BeaconState P D.block.1),
  ∃ m m' : BeaconState P D.block.1,
    run.steps[j]? = some D ∧
    Gated.read D.block.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests ∧
    requests.consolidations.toArray[k]? = some cr ∧
    jointConsolidationTrace ccfg bls D.pre D.block = .ok tr ∧
    tr[k]? = some m ∧ tr[k + 1]? = some m' ∧
    classify ccfg m cr = .ok (.pendingConsolidation pc.source_index pc.target_index) ∧
    applyOutcome ccfg m cr (.pendingConsolidation pc.source_index pc.target_index) = .ok m' ∧
    OutcomeMeans m m' cr (.pendingConsolidation pc.source_index pc.target_index)

/-- **C-S9 balance.**
(1) Reusable local `PendingConsolidationsLaw` and `PendingConsolidationsWindow`.
(2) Along any `ValidJointCBalance` chain `v`, `runAcceptedRecords v.run` is strictly ordered in `(step, request)` and
every entry carries its exact acceptance-time witness `AcceptedRecordWitness` (active, compounding, non-exiting target
at acceptance state `m`; distinct validator indices; no target signature or address match).
(3) There exists a per-step, per-call consumed-entry trace `runConsumed` (`runConsumed.length = v.run.steps.length`)
connecting every step `j` of `v.run` — via `StepConsolidationCalls`, covering same-fork `processSlots` and **both** the
pre-upgrade Electra `processSlots` and post-upgrade Fulu `processSlots` on an Electra → Fulu crossing — to its exact
chronological `processPendingConsolidations` calls `stepCalls`:
* before step `j`, `acceptedStreamUpTo v.run j = consumedBefore ++ pendingList D.pre.beacon` and
  `PendingDistinct D.pre.beacon`;
* at each call `m < stepCalls.length` (`c = stepCalls[m]`, `cs = perCallConsumed[m]`), `c.pre` and `c.post` are exact
  unconsumed suffixes of `acceptedStreamUpTo v.run j` (`consumedBefore ++ (perCallConsumed.take m).flatten` before the
  call, and `+ cs` after) and satisfy `CallConsolidationEffect ccfg c.pre c.post cs` (including `UnguardedTransfers`
  for every unslashed withdrawable entry consumed);
* after slot processing (`stIn`) and after block processing (`D.post.beacon`),
  `pendingList D.pre.beacon = perCallConsumed.flatten ++ pendingList stIn` and
  `pendingList D.post.beacon = pendingList stIn ++ stepAccepted D`;
* at `final.beacon`, `acceptedStream v.run = (runConsumed.flatten).flatten ++ pendingList final.beacon` and
  `PendingDistinct final.beacon`. -/
def C_S9_balance : Prop :=
  PendingConsolidationsLaw ∧ PendingConsolidationsWindow ∧
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P}
    (v : ValidJointCBalance cfg ccfg bls checkpoint anchor final),
    (∀ (idx₁ idx₂ j₁ k₁ j₂ k₂ : Nat) (pc₁ pc₂ : PendingConsolidation),
      idx₁ < idx₂ →
      (runAcceptedRecords v.run)[idx₁]? = some (j₁, k₁, pc₁) →
      (runAcceptedRecords v.run)[idx₂]? = some (j₂, k₂, pc₂) →
      j₁ < j₂ ∨ (j₁ = j₂ ∧ k₁ < k₂)) ∧
    (∀ (idx j k : Nat) (pc : PendingConsolidation),
      (runAcceptedRecords v.run)[idx]? = some (j, k, pc) →
      AcceptedRecordWitness v.run j k pc) ∧
    ∃ runConsumed : List (List (List PendingConsolidation)),
      runConsumed.length = v.run.steps.length ∧
      (∀ {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls} {perCallConsumed : List (List PendingConsolidation)},
        v.run.steps[j]? = some D →
        runConsumed[j]? = some perCallConsumed →
        let consumedBefore := ((runConsumed.take j).flatten).flatten
        acceptedStreamUpTo v.run j = consumedBefore ++ pendingList D.pre.beacon ∧
        PendingDistinct D.pre.beacon ∧
        ∃ (stIn : BeaconState P D.block.1) (stepCalls : List (AnyConsolidationCall P)),
          jointBlockInput ccfg bls D.pre D.block = .ok stIn ∧
          StepConsolidationCalls ccfg bls D.pre D.block stIn stepCalls ∧
          perCallConsumed.length = stepCalls.length ∧
          (∀ (m : Nat), m < stepCalls.length →
            ∀ (c : AnyConsolidationCall P) (cs : List PendingConsolidation),
            stepCalls[m]? = some c → perCallConsumed[m]? = some cs →
            acceptedStreamUpTo v.run j = (consumedBefore ++ (perCallConsumed.take m).flatten) ++ pendingList c.pre ∧
            acceptedStreamUpTo v.run j =
              (consumedBefore ++ (perCallConsumed.take (m + 1)).flatten) ++ pendingList c.post ∧
            CallConsolidationEffect ccfg c.pre c.post cs) ∧
          pendingList D.pre.beacon = perCallConsumed.flatten ++ pendingList stIn ∧
          pendingList D.post.beacon = pendingList stIn ++ stepAccepted D) ∧
      acceptedStream v.run = (runConsumed.flatten).flatten ++ pendingList final.beacon ∧
      PendingDistinct final.beacon

/-! ### C-S9 balance negative control -/

/-- **C-S9 balance negative control (`PendingDistinct` bites on `UnguardedTransfers`).**
(1) Positive derivation: `Transfers u u' pc source` together with `pc.source_index ≠ pc.target_index` (supplied along
`ValidJointCBalance` by `PendingDistinct`) implies the unguarded per-account equation `UnguardedTransfers u u' pc source`
(`sb' = sb - transfer ∧ tb' = tb + transfer`).
(2) Closed counterexample when `PendingDistinct` is omitted: a closed minimal-preset Electra state `w` with one pending
consolidation `pc` having `pc.source_index = pc.target_index` (violating only `PendingDistinct w`), unslashed and
withdrawable source validator, and positive transfer amount `min sb effective_balance > 0`. `processPendingConsolidations`
succeeds and consumes `pc` (`pendingList w' = []`), yet `increaseBalance` cancels `decreaseBalance`, leaving
`sb' = sb ≠ sb - transfer` (and `sb' ≠ sb + transfer`), falsifying `UnguardedTransfers w w' pc source`. -/
def C_S9_balance_control : Prop :=
  (∀ {P : Preset} {f : CFork} {u u' : BeaconState P f} {pc : PendingConsolidation} {source : Validator},
    Transfers u u' pc source → pc.source_index ≠ pc.target_index → UnguardedTransfers u u' pc source) ∧
  ∃ (w w' : BeaconState Preset.minimal .electra) (pc : PendingConsolidation) (source : Validator)
      (current nextEpoch : Epoch) (sb sb' : Gwei),
    pendingList w = [pc] ∧
    pc.source_index = pc.target_index ∧
    w.validators.toArray[pc.source_index.toNat]? = some source ∧
    getCurrentEpoch w = .ok current ∧
    current.add? U64.one "process_pending_consolidations" = .ok nextEpoch ∧
    source.slashed = false ∧ ¬ nextEpoch < source.withdrawable_epoch ∧
    w.balances.toArray[pc.source_index.toNat]? = some sb ∧
    0 < min sb.toNat source.effective_balance.toNat ∧
    processPendingConsolidations Config.minimal w = .ok w' ∧
    pendingList w' = [] ∧
    w'.balances.toArray[pc.source_index.toNat]? = some sb' ∧
    sb' = sb ∧
    sb'.toNat ≠ sb.toNat - min sb.toNat source.effective_balance.toNat ∧
    sb'.toNat ≠ sb.toNat + min sb.toNat source.effective_balance.toNat ∧
    ¬ UnguardedTransfers w w' pc source

end Blanc.Corpus.Freeze.ConsolidationJoint
