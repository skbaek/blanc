import Blanc.JointHistory
import Blanc.ExecutionKeptConfigured
import Blanc.ExecutionKeptClean
import Blanc.Composition.ConsolidationRequestPublicHistory

/-!
# Freeze record (G0, part cb): EIP-7251 across the layers, C-S9 (authorization, fate, balance)

Statements only, against Blanc main `7f2a69ba` and Jaune `c30cf0a5`, on the Electra/Fulu joint chain
(`Blanc.JointRun`, `Blanc/JointHistory.lean`) paired with Prague to BPO2. Nothing here is proved, registered in the
layering classification, or imported by the root.

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
execution history to the anchor's execution chain, then a joint run from the anchor. Every premise is a field. -/
structure ValidJointC (cfg : ChainConfig) (ccfg : Config) (bls : Bool) (checkpoint : BlockChain)
    (anchor final : JointState P) : Type where
  /-- root: canonical code, slots 0 to 3 at the inhibitor, 0, 0, 0, and no code at SYSTEM_ADDRESS, at the checkpoint
  (the mainnet form takes them from `ConsolidationCheckpointObservation`, block 22,431,083). -/
  root : CheckpointStart checkpoint.state
  /-- pre: the configured execution history from the checkpoint to the anchor's execution chain. -/
  pre : ConfiguredHistoryTrace cfg checkpoint anchor.exec
  /-- run: the joint run from the anchor. -/
  run : JointRun cfg ccfg bls anchor final
  /-- pendingDistinct: the anchor invariant on the anchor's beacon state (read by C-S9 balance only). -/
  pendingDistinct : PendingDistinct anchor.beacon
  /-- clean: no kept block of the joint history has SYSTEM_ADDRESS as a sender or a 7702 authority, and none
  creates it. -/
  clean : HistoryClean (run.toExec pre).kept
  /-- occurrences: at most 2^253 committed submissions over the joint history. -/
  occurrences : (submissions (run.toExec pre).kept).length ≤ 2 ^ 253

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

/-- **The law of `process_pending_consolidations`**, at any state. A successful run consumes a prefix of `n` entries
of the queue, through loop states `us` (the state before each consumed entry, then the state after the last). Each
consumed entry is skipped, changing nothing, exactly when its source is slashed; otherwise its source is
withdrawable by the next epoch and it is applied (`Transfers`). The first entry not consumed, if any, has an
unslashed source that is not yet withdrawable, and nothing after it is read. The conditions name the source's record
only: at processing the target is asked for nothing, and no validator record is written. -/
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

/-- **Every call sees a suffix.** Whatever slot processing hands to `process_pending_consolidations` holds a suffix
of the queue it started from, and the Fulu upgrade keeps the queue. A joint step's slot processing
(`Blanc.jointBlockInput`) is `process_slots` from the step's beacon state, or, across Electra → Fulu,
`process_slots`, `upgrade_to_fulu`, `process_slots`; so every entry it applies is an entry of the step's pre-state. -/
def PendingConsolidationsWindow : Prop :=
  (∀ {P : Preset} {f : CFork} (ctx : Ctx) {st w : BeaconState P f} {n : Nat},
    ConsolidationCall ctx st n w → ∃ d, pendingList w = (pendingList st).drop d) ∧
  (∀ {P : Preset} (ccfg : Config) {pre : BeaconState P .electra} {post : BeaconState P .fulu},
    upgradeToFulu ccfg pre = .ok post → pendingList post = pendingList pre)

/-- Entry `pc` was accepted by the run before step `j`: some consolidation request of an earlier step classified, at
its mid-list state, as the pending consolidation `pc.source_index → pc.target_index` (so `OutcomeMeans` gives the
target's checks at that acceptance state). -/
def Accepted (v : ValidJointC cfg ccfg bls checkpoint anchor final) (j : Nat) (pc : PendingConsolidation) :
    Prop :=
  ∃ j' k : Nat, j' < j ∧ ∃ D : JointRunStep (P := P) cfg ccfg bls, ∃ requests : ExecutionRequests P,
    ∃ cr, ∃ tr : List (BeaconState P D.block.1), ∃ m : BeaconState P D.block.1,
      v.run.steps[j']? = some D ∧
      Gated.read D.block.2.message.body.execution_requests
        "NewPayloadRequest: execution_requests" = .ok requests ∧
      requests.consolidations.toArray[k]? = some cr ∧
      jointConsolidationTrace ccfg bls D.pre D.block = .ok tr ∧ tr[k]? = some m ∧
      classify ccfg m cr = .ok (.pendingConsolidation pc.source_index pc.target_index)

/-- The queue `q` is traced from the anchor at step `j`: it is the anchor's queue followed by entries the run
accepted before step `j`, less a consumed prefix; and no entry names one validator twice. -/
def TracedQueue (v : ValidJointC cfg ccfg bls checkpoint anchor final) (j : Nat)
    (q : List PendingConsolidation) : Prop :=
  (∃ d acc, q = (pendingList anchor.beacon ++ acc).drop d ∧ ∀ pc ∈ acc, Accepted v j pc) ∧
  ∀ pc ∈ q, pc.source_index ≠ pc.target_index

/-- **C-S9 balance.** (1) The law of `process_pending_consolidations`: which entries are applied and what each
does to the two balances. (2) Every call inside a joint step's slot processing sees a suffix of the step's
pre-state queue. (3) Along a valid joint chain, the pending queue at every step's pre-state, and at the end, is
traced from the anchor: anchor entries, then entries accepted by the run's own classified requests, less a consumed
prefix, each naming two distinct validators. So whenever the chain applies an entry, the source loses and the
target gains `min(source balance, source effective balance)`; an entry accepted on the chain had a compounding,
active, non-exiting target when accepted, and nothing about the target is checked again. -/
def C_S9_balance : Prop :=
  PendingConsolidationsLaw ∧ PendingConsolidationsWindow ∧
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P}
    -- v: a valid joint chain for EIP-7251
    (v : ValidJointC cfg ccfg bls checkpoint anchor final),
    (∀ {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls}, v.run.steps[j]? = some D →
      TracedQueue v j (pendingList D.pre.beacon)) ∧
    TracedQueue v v.run.steps.length (pendingList final.beacon)

end Blanc.Corpus.Freeze.ConsolidationJoint
