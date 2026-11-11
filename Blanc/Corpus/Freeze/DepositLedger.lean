import Blanc.JointHistory

/-!
# G0 freeze, part d: the consensus half of D-S9 (fate, credit, conservation)

Goal `protocol-contract-corpus-v1` rev 2, cells D-S9 fate and credit and D-S9 conservation, the
consensus half. Freeze record only: this module is not in the root or the layering
classification, and each cell is frozen as `def … : Prop` (a later proof is `theorem … : …`).

**The ledger.** A pending deposit carries no index, and two requests with equal key, credentials,
amount and signature in one block give equal `PendingDeposit`s. So occurrences are tracked by a
ghost tag carried beside each queue entry: `some i` for the deposit request whose `index` is `i`,
`none` for every other source. The tagged replicas below run the same Jaune calls as
`process_slots`, `process_epoch` and `process_pending_deposits` with the tag list threaded
through; `PassMirror`, `SlotsMirror` and `StepMirror` freeze the bridge that the replicas leave
Jaune's results unchanged (proof machinery, stated so the reviewer can check it is the bridge
the headline needs). Every write of `pending_deposits` in Electra and Fulu is one of: the pass
(`process_pending_deposits`), an append by `process_deposit_request` (slot = the block's slot,
nonzero for every post-genesis block), or an append by another source at `GENESIS_SLOT`
(`apply_deposit` for an Eth1 bridge deposit, `queue_excess_active_balance` from a switch to
compounding, `upgrade_to_electra` for pre-activation balances). `upgrade_to_fulu` copies the
queue. The block-level appends are therefore tagged by slot: the `k`-th appended entry with a
nonzero slot is request `k`.

**Electra activation-slot ingress.** `JointRun` requires `processSlots` (`beacon.slot < block.slot`)
on `.electra → .electra` steps, which rejects an upgraded Electra anchor already at the Electra
activation slot when the activation-slot block arrives. `JointRunIngress` adds that exact ingress
case (`jointTransitionAt … (atSlot := firstBlock.message.slot == anchor.beacon.slot)` at `.electra`
when `anchor.beacon.slot ≤ firstBlock.message.slot < fuluForkSlot`, matching
`JauneConsensus/Joint.lean:40,82`) followed by `JointRun`.

New vocabulary, defined here minimally: `Tag`, `TQueue`, `requestPending`, `ApplyOutcome`,
`classifyApply`, `ApplyOutcomeSpec`, `PassPartition`, the tagged replicas, `JointRunIngress`,
`ValidIngressStep`, `stepLedger`, `runLedger`, `AnchorLedger`, `RunIndicesFreshIngress`.
-/

namespace Blanc.Corpus.Freeze.Deposit

open Jaune JauneConsensus Blanc ExecutionTrace

variable {P : Preset} {f : CFork}

/-! ## Vocabulary -/

/-- A queue entry's ghost source tag: the index of the deposit request it came from, or `none`
for every other source (and for pre-cutover legacy entries). -/
abbrev Tag := Option Nat

/-- A tagged pending-deposit queue. -/
abbrev TQueue := List (Tag × PendingDeposit)

/-- The pending deposit `process_deposit_request` appends for `dr` in a block at `slot`. -/
def requestPending (dr : DepositRequest) (slot : Slot) : PendingDeposit :=
  { pubkey := dr.pubkey, withdrawal_credentials := dr.withdrawal_credentials, amount := dr.amount,
    signature := dr.signature, slot := slot }

/-- The outcome of one `apply_pending_deposit` call. -/
inductive ApplyOutcome where
  /-- Unknown key, signature valid: a validator is added with the amount as its balance. -/
  | newValidator
  /-- Known key at this validator index: its balance increases by the amount. -/
  | topUp (index : Nat)
  /-- Unknown key, signature invalid: the state is unchanged; this occurrence gets no credit. -/
  | noCredit
  deriving DecidableEq

/-- `apply_pending_deposit`'s case split, read at the state it reads. -/
def classifyApply (ctx : Ctx) (state : BeaconState P f) (d : PendingDeposit) : M ApplyOutcome :=
  match findValidatorIndex state d.pubkey with
  | some i => pure (.topUp i)
  | none => do
    if ← isValidDepositSignature ctx d.pubkey d.withdrawal_credentials d.amount d.signature then
      pure .newValidator
    else pure .noCredit

/-- Exact 3-way case split and validator/balance consequences of `apply_pending_deposit` at
`ctx = jointCtx ccfg bls`. Exposes `addValidatorToRegistry` and `increaseBalance` directly in
terms of `validators` and `balances`. -/
def ApplyOutcomeSpec (ccfg : Config) (bls : Bool) (pre post : BeaconState P f)
    (d : PendingDeposit) (o : ApplyOutcome) : Prop :=
  let ctx := jointCtx ccfg bls
  classifyApply ctx pre d = .ok o ∧
  applyPendingDeposit ctx pre d = .ok post ∧
  ((o = .newValidator ∧
      findValidatorIndex pre d.pubkey = none ∧
      isValidDepositSignature ctx d.pubkey d.withdrawal_credentials d.amount d.signature =
        .ok true ∧
      addValidatorToRegistry pre d.pubkey d.withdrawal_credentials d.amount = .ok post ∧
      post.validators.length = pre.validators.length + 1 ∧
      (∀ idx < pre.validators.length,
        post.validators.toArray[idx]? = pre.validators.toArray[idx]?) ∧
      (∃ v : Validator, post.validators.toArray[pre.validators.length]? = some v ∧
        v.pubkey = d.pubkey ∧ v.withdrawal_credentials = d.withdrawal_credentials) ∧
      post.balances.toArray[pre.validators.length]? = some d.amount ∧
      (∀ idx, idx ≠ pre.validators.length →
        post.balances.toArray[idx]? = pre.balances.toArray[idx]?) ∧
      (pre.balances.length = pre.validators.length →
        post.balances.length = pre.balances.length + 1)) ∨
   (∃ i : Nat, o = .topUp i ∧
      findValidatorIndex pre d.pubkey = some i ∧
      (∃ iv : ValidatorIndex, U64.ofNat? i "ValidatorIndex" = .ok iv ∧
        increaseBalance pre iv d.amount = .ok post) ∧
      post.validators = pre.validators ∧
      post.balances.length = pre.balances.length ∧
      (∃ oldBal newBal : Gwei,
        pre.balances.toArray[i]? = some oldBal ∧
        post.balances.toArray[i]? = some newBal ∧
        newBal.toNat = oldBal.toNat + d.amount.toNat) ∧
      (∀ idx, idx ≠ i → post.balances.toArray[idx]? = pre.balances.toArray[idx]?)) ∨
   (o = .noCredit ∧
      findValidatorIndex pre d.pubkey = none ∧
      isValidDepositSignature ctx d.pubkey d.withdrawal_credentials d.amount d.signature =
        .ok false ∧
      post = pre ∧
      post.validators = pre.validators ∧
      post.balances = pre.balances))

/-- The Gwei an outcome credits for deposit `d`. -/
def ApplyOutcome.credited : ApplyOutcome → PendingDeposit → Nat
  | .noCredit, _ => 0
  | _, d => d.amount.toNat

/-- How a pass handled an entry it applied. -/
inductive ApplyRoute where
  /-- The validator is withdrawable: applied without consuming churn. -/
  | withdrawn
  /-- Applied within the churn. -/
  | churn
  deriving DecidableEq

/-- Why a pass stopped before the end of the queue. -/
inductive PassStop where
  | bridge | finality | count | churn
  deriving DecidableEq

/-- One entry a pass applied: its tag, the deposit, the state `apply_pending_deposit` read, and the
route. -/
structure Applied (P : Preset) (f : CFork) where
  tag : Tag
  deposit : PendingDeposit
  pre : BeaconState P f
  route : ApplyRoute

/-- An applied entry at whichever fork its pass ran. -/
abbrev AppliedAt (P : Preset) := Σ f : CFork, Applied P f

/-- The loop's result: the state after the loop (before the queue write), the next queue index,
the processed amount, the postponed entries, the applied entries in order, and the stop. -/
structure PassResult (P : Preset) (f : CFork) where
  state : BeaconState P f
  next : Nat
  processed : U64
  postponed : TQueue
  applied : List (Applied P f)
  stop : Option PassStop

/-- Exact occurrence-preserving ordered partition of a consumed queue prefix into applied entries
and postponed entries, preserving front-to-back order and multiplicity in both lists. -/
inductive PassPartition : TQueue → TQueue → TQueue → Prop where
  | nil : PassPartition [] [] []
  | apply (x : Tag × PendingDeposit) {xs ap post : TQueue} :
      PassPartition xs ap post → PassPartition (x :: xs) (x :: ap) post
  | postpone (x : Tag × PendingDeposit) {xs ap post : TQueue} :
      PassPartition xs ap post → PassPartition (x :: xs) ap (x :: post)

/-! ## The tagged replicas -/

/-- The header parameters `process_pending_deposits` derives from `(ctx, state)` before entering
its queue loop. -/
def passParams (ctx : Ctx) (state : BeaconState P f) :
    M (Epoch × U64 × Slot × U64) := do
  let site := "process_pending_deposits"
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
  let available ← (← state.depositBalanceToConsume).add?
    (← getActivationExitChurnLimit ctx.cfg state) site
  let finalizedSlot ← computeStartSlotAtEpoch P state.finalized_checkpoint.epoch
  let requestsStart ← state.depositRequestsStartIndex
  pure (nextEpoch, available, finalizedSlot, requestsStart)

/-- The loop of `process_pending_deposits` over a tagged queue, as structural recursion: the same
reads, the same breaks in the same order, the same calls. -/
def passLoop (ctx : Ctx) (nextEpoch : Epoch) (available : U64) (finalizedSlot : Slot)
    (requestsStart : U64) :
    TQueue → Nat → U64 → BeaconState P f → TQueue → List (Applied P f) → M (PassResult P f)
  | [], i, processed, state, post, ap => pure ⟨state, i, processed, post, ap, none⟩
  | (t, d) :: rest, i, processed, state, post, ap => do
    let site := "process_pending_deposits"
    if !(f.atLeast .fulu) && d.slot > GENESIS_SLOT && state.eth1_deposit_index < requestsStart then
      return ⟨state, i, processed, post, ap, some .bridge⟩
    if d.slot > finalizedSlot then return ⟨state, i, processed, post, ap, some .finality⟩
    if i ≥ P.MAX_PENDING_DEPOSITS_PER_EPOCH then return ⟨state, i, processed, post, ap, some .count⟩
    let mut exited := false
    let mut withdrawn := false
    if let some k := findValidatorIndex state d.pubkey then
      let validator ← state.validators.get k site
      exited := validator.exit_epoch < FAR_FUTURE_EPOCH
      withdrawn := validator.withdrawable_epoch < nextEpoch
    if withdrawn then
      let state' ← applyPendingDeposit ctx state d
      passLoop ctx nextEpoch available finalizedSlot requestsStart rest (i + 1) processed state'
        post (ap ++ [⟨t, d, state, .withdrawn⟩])
    else if exited then
      passLoop ctx nextEpoch available finalizedSlot requestsStart rest (i + 1) processed state
        (post ++ [(t, d)]) ap
    else
      let sum ← processed.add? d.amount site
      if sum > available then return ⟨state, i, processed, post, ap, some .churn⟩
      let state' ← applyPendingDeposit ctx state d
      passLoop ctx nextEpoch available finalizedSlot requestsStart rest (i + 1) sum state'
        post (ap ++ [⟨t, d, state, .churn⟩])

/-- `process_pending_deposits` over a tagged queue: the post-state, the tagged queue it leaves
(the unprocessed suffix, then the postponed entries), and the entries it applied. -/
def processPendingDepositsTagged (ctx : Ctx) (state : BeaconState P f) (tq : TQueue) :
    M (BeaconState P f × TQueue × List (Applied P f)) := do
  let site := "process_pending_deposits"
  let (nextEpoch, available, finalizedSlot, requestsStart) ← passParams ctx state
  let r ← passLoop ctx nextEpoch available finalizedSlot requestsStart tq 0 U64.zero state [] []
  let rest := tq.drop r.next ++ r.postponed
  let st ← r.state.setPendingDeposits (← SszList.ofArray (rest.map Prod.snd).toArray site)
  let st ← if r.stop = some .churn then st.setDepositBalanceToConsume (← available.sub? r.processed site)
    else st.setDepositBalanceToConsume U64.zero
  pure (st, rest, r.applied)

/-- `process_epoch` with the tagged pass in place of `process_pending_deposits`. -/
def processEpochTagged (ctx : Ctx) (state : BeaconState P f) (tq : TQueue) :
    M (BeaconState P f × TQueue × List (Applied P f)) := do
  let cfg := ctx.cfg
  let state ← processJustificationAndFinalization cfg state
  let state ← processInactivityUpdates cfg state
  let state ← processRewardsAndPenalties cfg state
  let state ← processRegistryUpdates cfg state
  let state ← processSlashings cfg state
  let state ← processEth1DataReset cfg state
  let (state, tq, ap) ← if f.atLeast .electra then do
      let (state, tq, ap) ← processPendingDepositsTagged ctx state tq
      let state ← processPendingConsolidations cfg state
      pure (state, tq, ap)
    else pure (state, tq, [])
  let state ← processEffectiveBalanceUpdates cfg state
  let state ← processSlashingsReset cfg state
  let state ← processRandaoMixesReset cfg state
  let state ← processHistoricalSummariesUpdate cfg state
  let state ← processParticipationFlagUpdates cfg state
  let state ← processSyncCommitteeUpdates ctx state
  let state ← if f.atLeast .fulu then processProposerLookahead cfg state else pure state
  pure (state, tq, ap)

/-- The slot loop of `process_slots` with the tagged epoch. -/
def slotsLoopTagged (ctx : Ctx) (slotsPerEpoch : U64) :
    Nat → BeaconState P f → TQueue → List (Applied P f) →
      M (BeaconState P f × TQueue × List (Applied P f))
  | 0, state, tq, ap => pure (state, tq, ap)
  | n + 1, state, tq, ap => do
    let state ← processSlot state
    let next ← state.slot.add? U64.one "process_slots: state.slot + 1"
    let (state, tq, ap) ←
      if (← next.mod? slotsPerEpoch "process_slots: (state.slot + 1) % SLOTS_PER_EPOCH").toNat == 0
      then do
        let (state, tq, ap') ← processEpochTagged ctx state tq
        pure (state, tq, ap ++ ap')
      else pure (state, tq, ap)
    slotsLoopTagged ctx slotsPerEpoch n { state with slot := next } tq ap

/-- `process_slots` over a tagged queue. -/
def processSlotsTagged (ctx : Ctx) (state : BeaconState P f) (slot : Slot) (tq : TQueue) :
    M (BeaconState P f × TQueue × List (Applied P f)) := do
  require (decide (state.slot < slot)) "process_slots: state.slot < slot"
  let slotsPerEpoch ← u64 P.SLOTS_PER_EPOCH "SLOTS_PER_EPOCH"
  slotsLoopTagged ctx slotsPerEpoch (slot.toNat - state.slot.toNat) state tq []

/-- Tag the entries `process_block` appended: the `k`-th one with a nonzero slot is request `k`
of the block (its `index`); every entry at `GENESIS_SLOT` is another source. -/
def tagAppended : List DepositRequest → List PendingDeposit → TQueue
  | _, [] => []
  | drs, d :: rest =>
    if d.slot ≠ GENESIS_SLOT then
      match drs with
      | dr :: drs' => (some dr.index.toNat, d) :: tagAppended drs' rest
      | [] => (none, d) :: tagAppended [] rest
    else (none, d) :: tagAppended drs rest

/-- `jointBlockInput` over a tagged queue: the same calls, with the tagged `process_slots`
(skipping `process_slots` on an Electra activation-slot block when `sb.message.slot == beacon.slot`,
just as `jointTransitionAt … (atSlot := true)` and the Fulu fork-slot case do); `upgrade_to_fulu`
copies the queue, so the tags pass through it. -/
def jointBlockInputTagged (ccfg : Config) (bls : Bool) :
    (s : JointState P) → (b : AnySignedBlock P) → TQueue →
      M (BeaconState P b.1 × TQueue × List (AppliedAt P))
  | ⟨.electra, beacon, _⟩, ⟨.electra, sb⟩, tq => do
    if sb.message.slot == beacon.slot then
      pure (beacon, tq, [])
    else
      let (st, tq, ap) ← processSlotsTagged (jointCtx ccfg bls) beacon sb.message.slot tq
      pure (st, tq, ap.map fun a => ⟨.electra, a⟩)
  | ⟨.fulu, beacon, _⟩, ⟨.fulu, sb⟩, tq => do
    let (st, tq, ap) ← processSlotsTagged (jointCtx ccfg bls) beacon sb.message.slot tq
    pure (st, tq, ap.map fun a => ⟨.fulu, a⟩)
  | ⟨.electra, beacon, _⟩, ⟨.fulu, sb⟩, tq => do
    let forkSlot ← U64.ofNat? (fuluForkSlot (P := P) ccfg) "joint step: Fulu fork slot"
    let (beacon, tq, ap₁) ← if beacon.slot < forkSlot then
        processSlotsTagged (jointCtx ccfg bls) beacon forkSlot tq
      else pure (beacon, tq, [])
    let beacon ← upgradeToFulu ccfg beacon
    let (st, tq, ap₂) ← if sb.message.slot == beacon.slot then pure (beacon, tq, [])
      else processSlotsTagged (jointCtx ccfg bls) beacon sb.message.slot tq
    pure (st, tq, ap₁.map (fun a => ⟨.electra, a⟩) ++ ap₂.map fun a => ⟨.fulu, a⟩)
  | _, _, _ => throw (.assert "joint step: fork pair outside Electra and Fulu")

/-! ## Electra activation-slot ingress -/

/-- Every successful Electra `jointTransitionAt` with the balance no-wrap bound has a configured
execution block trace (the `atSlot`-parametric counterpart of `nonempty_jointStepTrace`). -/
private theorem nonempty_electraTransitionTrace {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon₀ beacon₁ : BeaconState P .electra} {exec₀ exec₁ : BlockChain}
    {sb : SignedBeaconBlock P .electra} {atSlot : Bool}
    (step : jointTransitionAt cfg ccfg bls beacon₀ exec₀ sb atSlot = .ok (beacon₁, exec₁))
    (bound : sum exec₀.state.bal + wdsum (payloadWithdrawals ⟨.electra, sb⟩) < 2 ^ 256) :
    Nonempty (JointStepTrace cfg ccfg bls ⟨.electra, beacon₀, exec₀⟩
      ⟨.electra, beacon₁, exec₁⟩ ⟨.electra, sb⟩) := by
  obtain ⟨req, hreq, hengine⟩ := jointTransitionAt_engine step
  obtain ⟨fork, bodyState, blockOutput, hfork, -, hcovered, htransition, hbody, hrequests⟩ :=
    engineVerdict_ok hengine (.inl rfl)
  have hwds : (payloadToBlock req).wds = payloadWithdrawals ⟨.electra, sb⟩ := by
    simp only [payloadToBlock, payloadWithdrawals, ofBlock_executionPayload hreq]
  obtain ⟨fork', bodyState', blockOutput', hfork', hrules, hbody', hpost⟩ :=
    exists_configuredBody_of_transition htransition
  obtain rfl : fork' = fork := Except.ok.inj (hfork'.symm.trans hfork)
  obtain ⟨rfl, rfl⟩ : bodyState' = bodyState ∧ blockOutput' = blockOutput := by
    have := Except.ok.inj (hbody'.symm.trans hbody)
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  rcases exists_appliedBodyTrace hbody hcovered with ⟨bodyTrace⟩
  exact ⟨{
    req := req
    ofBlock := hreq
    engine := hengine
    trace := {
      block := payloadToBlock req
      bound := hwds ▸ bound
      fork := fork'
      forkAt := hfork
      rules := fork'.ruleSet
      rulesEq := rfl
      rulesAt := hrules
      covered := hcovered
      transition := htransition
      bodyState := bodyState'
      blockOutput := blockOutput'
      bodyRun := hbody
      bodyTrace := bodyTrace
      postEq := hpost }
    block_eq := rfl
    requests_eq := hrequests }⟩

/-- Chosen execution block trace for an Electra `jointTransitionAt` step. -/
noncomputable def chooseElectraTransitionTrace {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {beacon₀ beacon₁ : BeaconState P .electra} {exec₀ exec₁ : BlockChain}
    {sb : SignedBeaconBlock P .electra} {atSlot : Bool}
    (step : jointTransitionAt cfg ccfg bls beacon₀ exec₀ sb atSlot = .ok (beacon₁, exec₁))
    (bound : sum exec₀.state.bal + wdsum (payloadWithdrawals ⟨.electra, sb⟩) < 2 ^ 256) :
    JointStepTrace cfg ccfg bls ⟨.electra, beacon₀, exec₀⟩
      ⟨.electra, beacon₁, exec₁⟩ ⟨.electra, sb⟩ :=
  Classical.choice (nonempty_electraTransitionTrace step bound)

/-- A joint run from `anchor` to `final`, admitting either a standard `JointRun` or an initial
Electra ingress block via `jointTransitionAt … (atSlot := firstBlock.message.slot == beacon₀.slot)`
when `beacon₀.slot ≤ firstBlock.message.slot < fuluForkSlot` (covering an upgraded Electra anchor
at the Electra activation slot) followed by a standard `JointRun`. -/
inductive JointRunIngress {P : Preset} (cfg : ChainConfig) (ccfg : Config) (bls : Bool) :
    JointState P → JointState P → Type where
  | standard {anchor final : JointState P}
      (run : JointRun cfg ccfg bls anchor final) :
      JointRunIngress cfg ccfg bls anchor final
  | atElectraSlot {beacon₀ beacon₁ : BeaconState P .electra} {exec₀ exec₁ : BlockChain}
      {final : JointState P}
      (firstBlock : SignedBeaconBlock P .electra)
      (postGenesis : GENESIS_SLOT < firstBlock.message.slot)
      (slotLe : beacon₀.slot ≤ firstBlock.message.slot)
      (beforeFulu : firstBlock.message.slot.toNat < fuluForkSlot (P := P) ccfg)
      (firstStep : jointTransitionAt cfg ccfg bls beacon₀ exec₀ firstBlock
        (atSlot := firstBlock.message.slot == beacon₀.slot) = .ok (beacon₁, exec₁))
      (firstBound : sum exec₀.state.bal + wdsum (payloadWithdrawals ⟨.electra, firstBlock⟩) < 2 ^ 256)
      (tail : JointRun cfg ccfg bls ⟨.electra, beacon₁, exec₁⟩ final) :
      JointRunIngress cfg ccfg bls ⟨.electra, beacon₀, exec₀⟩ final

/-- Extend a configured execution history ending at `anchor.exec` across a `JointRunIngress`. -/
noncomputable def JointRunIngress.toExec {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint anchor.exec) :
    JointRunIngress cfg ccfg bls anchor final → ConfiguredHistoryTrace cfg checkpoint final.exec
  | .standard run => run.toExec pre
  | .atElectraSlot _ _ _ _ firstStep firstBound tail =>
      tail.toExec (.step pre (chooseElectraTransitionTrace firstStep firstBound).trace)

/-- The steps of a `JointRunIngress`, in chronological order. -/
noncomputable def JointRunIngress.steps {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} :
    JointRunIngress cfg ccfg bls anchor final → List (JointRunStep (P := P) cfg ccfg bls)
  | .standard run => run.steps
  | .atElectraSlot firstBlock _ _ _ firstStep firstBound tail =>
      ⟨_, _, ⟨.electra, firstBlock⟩, chooseElectraTransitionTrace firstStep firstBound⟩ ::
        tail.steps

/-- A `JointRunStep` arose from a valid joint transition (either an ordinary `jointStep` or an
Electra ingress `jointTransitionAt`) at a post-genesis block slot. -/
def ValidIngressStep (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    (D : JointRunStep (P := P) cfg ccfg bls) : Prop :=
  D.block.2.message.slot ≠ GENESIS_SLOT ∧
  (jointStep cfg ccfg bls D.pre D.block = .ok D.post ∨
    ∃ (beacon₀ beacon₁ : BeaconState P .electra) (exec₀ exec₁ : BlockChain)
      (sb : SignedBeaconBlock P .electra),
      D.pre = ⟨.electra, beacon₀, exec₀⟩ ∧
      D.post = ⟨.electra, beacon₁, exec₁⟩ ∧
      D.block = ⟨.electra, sb⟩ ∧
      beacon₀.slot ≤ sb.message.slot ∧
      sb.message.slot.toNat < fuluForkSlot (P := P) ccfg ∧
      jointTransitionAt cfg ccfg bls beacon₀ exec₀ sb
        (atSlot := sb.message.slot == beacon₀.slot) = .ok (beacon₁, exec₁))

/-- The deposit requests of a joint run step's beacon block. -/
def stepDepositRequests {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : JointRunStep (P := P) cfg ccfg bls) : List DepositRequest :=
  match Gated.read D.block.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" with
  | .ok requests => requests.deposits.toArray.toList
  | .error _ => []

/-- One step of the ledger: the tagged queue after the step's slots, then the entries its block
appended, tagged; and the entries the step's passes applied. -/
def stepLedger {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : JointRunStep (P := P) cfg ccfg bls) (tq : TQueue) :
    M (TQueue × List (AppliedAt P)) := do
  let (_, tq, ap) ← jointBlockInputTagged ccfg bls D.pre D.block tq
  let post ← D.post.beacon.pendingDeposits
  pure (tq ++ tagAppended (stepDepositRequests D) (post.toArray.toList.drop tq.length), ap)

/-- The ledger over a run's steps: the final tagged queue and every applied entry with the index
of its step. -/
def runLedger {cfg : ChainConfig} {ccfg : Config} {bls : Bool} :
    Nat → List (JointRunStep (P := P) cfg ccfg bls) → TQueue → List (Nat × AppliedAt P) →
      M (TQueue × List (Nat × AppliedAt P))
  | _, [], tq, ap => pure (tq, ap)
  | j, D :: rest, tq, ap => do
    let (tq, ap') ← stepLedger D tq
    runLedger (j + 1) rest tq (ap ++ ap'.map fun a => (j, a))

/-! ## Premises -/

/-- The pending-deposit queue of a joint state, as a list. -/
def pendingList (s : JointState P) : M (List PendingDeposit) := do
  pure (← s.beacon.pendingDeposits).toArray.toList

/-- **The anchor ledger** (D's consensus anchor premise, not a G1b invariant): the anchor's tags
align with its queue, only entries at a nonzero slot (request entries) carry a tag, and no tag
repeats. -/
def AnchorLedger (anchor : JointState P) (tq₀ : TQueue) : Prop :=
  pendingList anchor = .ok (tq₀.map Prod.snd) ∧
  (∀ e ∈ tq₀, e.1.isSome → e.2.slot ≠ GENESIS_SLOT) ∧
  (tq₀.filterMap Prod.fst).Nodup

/-- The deposit requests of a standard `JointRun`, in order. -/
noncomputable def runDepositRequests {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) : List DepositRequest :=
  run.steps.flatMap stepDepositRequests

/-- The deposit requests of a `JointRunIngress`, in order. -/
noncomputable def ingressDepositRequests {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (ingress : JointRunIngress cfg ccfg bls s₀ s) : List DepositRequest :=
  ingress.steps.flatMap stepDepositRequests

/-- **Fresh indices** on `JointRunIngress` (discharged in the joined D-S9 statement from D-S3 and
delivery: the run's requests carry the contract's consecutive counts from `E₀`, and an anchor tag
names a deposit below `E₀`): the run's request indices are distinct and none is an anchor tag. -/
def RunIndicesFreshIngress {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s₀ s : JointState P}
    (ingress : JointRunIngress cfg ccfg bls s₀ s) (tq₀ : TQueue) : Prop :=
  (tq₀.filterMap Prod.fst ++ (ingressDepositRequests ingress).map fun dr => dr.index.toNat).Nodup

/-- **Fresh indices** specialized to a standard `JointRun`. -/
def RunIndicesFresh {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s₀ s : JointState P}
    (run : JointRun cfg ccfg bls s₀ s) (tq₀ : TQueue) : Prop :=
  RunIndicesFreshIngress (.standard run) tq₀

/-! ## The bridges (proof machinery, frozen with the cells) -/

/-- The tagged pass leaves Jaune's `process_pending_deposits` unchanged, and its tags stay aligned. -/
def PassMirror : Prop :=
  ∀ {P : Preset} {f : CFork} (ctx : Ctx) (state : BeaconState P f) (tq : TQueue),
    (do pure (← state.pendingDeposits).toArray.toList) = (.ok (tq.map Prod.snd) : M _) →
    ∀ state', processPendingDeposits ctx state = .ok state' →
      ∃ tq' ap, processPendingDepositsTagged ctx state tq = .ok (state', tq', ap) ∧
        (do pure (← state'.pendingDeposits).toArray.toList) = (.ok (tq'.map Prod.snd) : M _)

/-- The tagged `process_slots` leaves Jaune's `process_slots` unchanged. -/
def SlotsMirror : Prop :=
  ∀ {P : Preset} {f : CFork} (ctx : Ctx) (state : BeaconState P f) (slot : Slot) (tq : TQueue),
    (do pure (← state.pendingDeposits).toArray.toList) = (.ok (tq.map Prod.snd) : M _) →
    ∀ state', processSlots ctx state slot = .ok state' →
      ∃ tq' ap, processSlotsTagged ctx state slot tq = .ok (state', tq', ap) ∧
        (do pure (← state'.pendingDeposits).toArray.toList) = (.ok (tq'.map Prod.snd) : M _)

/-- Every valid ingress/run step keeps the ledger aligned with the queue, and the block's appends
are, in order, other-source entries at `GENESIS_SLOT` and, tagged with its index,
`requestPending dr slot` for each of the block's deposit requests `dr` (`slot` the block's slot). -/
def StepMirror : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : JointRunStep (P := P) cfg ccfg bls) (tq : TQueue),
    ValidIngressStep cfg ccfg bls D →
    pendingList D.pre = .ok (tq.map Prod.snd) →
      ∃ tq' ap, stepLedger D tq = .ok (tq', ap) ∧ pendingList D.post = .ok (tq'.map Prod.snd) ∧
        ∃ st tqS tqA, jointBlockInputTagged ccfg bls D.pre D.block tq = .ok (st, tqS, ap) ∧
          tq' = tqS ++ tqA ∧
          tqA.filter (fun e => e.1.isSome) = (stepDepositRequests D).map
            (fun dr => (some dr.index.toNat, requestPending dr D.block.2.message.slot)) ∧
          ∀ e ∈ tqA, e.1 = none → e.2.slot = GENESIS_SLOT

/-! ## D-S9 fate and credit (consensus half) -/

/-- **D-S9 fate and credit, consensus half.** On a `JointRunIngress` from `anchor` with BLS on,
post-genesis block slots, an anchor ledger `tq₀`, and fresh request indices, the ledger is
computed, its final queue is the final state's queue, and every deposit request `dr` of step `j`'s
block meets **exact one** fate:

* **applied**: at a **unique list index** `apIdx` of `ap`, `ap[apIdx]? = some (j', a)` carries tag
  `some dr.index.toNat` at a later step `j' > j` (a block's appends follow its slots' passes),
  holding `requestPending dr slot`, and `ApplyOutcomeSpec ccfg true a.2.pre s' d o` holds (exact
  3-way outcome with real `blsVerify true` gating new-validator creation and explicit
  `addValidatorToRegistry` / `increaseBalance` validator and balance equations);
* **still pending**: no applied entry carries its tag, and a **unique queue index** `p` of `tqF`
  holds `(some dr.index.toNat, requestPending dr slot)`.

Postponement and the pass's stops are the intermediate moves of `D9Pass`. Entries from other
sources carry `none` and meet neither clause. -/
def D9Fate : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {anchor final : JointState P}
    (ingress : JointRunIngress cfg ccfg true anchor final) (tq₀ : TQueue),
    (∀ D ∈ ingress.steps, D.block.2.message.slot ≠ GENESIS_SLOT) →
    AnchorLedger anchor tq₀ →
    RunIndicesFreshIngress ingress tq₀ →
    ∃ tqF ap, runLedger 0 ingress.steps tq₀ [] = .ok (tqF, ap) ∧
      pendingList final = .ok (tqF.map Prod.snd) ∧
      ∀ (j : Nat) (D : JointRunStep (P := P) cfg ccfg true) (k : Nat) (dr : DepositRequest),
        ingress.steps[j]? = some D → (stepDepositRequests D)[k]? = some dr →
        let d := requestPending dr D.block.2.message.slot
        (((∀ p : Nat, (tqF[p]?.map Prod.fst) ≠ some (some dr.index.toNat)) ∧
          ∃ (apIdx j' : Nat) (a : AppliedAt P),
            ap[apIdx]? = some (j', a) ∧
            a.2.tag = some dr.index.toNat ∧
            j < j' ∧
            (∀ (apIdx' j'' : Nat) (a' : AppliedAt P),
              ap[apIdx']? = some (j'', a') → a'.2.tag = some dr.index.toNat → apIdx' = apIdx) ∧
            a.2.deposit = d ∧
            ∃ (o : ApplyOutcome) (s' : BeaconState P a.1),
              ApplyOutcomeSpec ccfg true a.2.pre s' d o) ∨
         ((∀ (apIdx : Nat) (j' : Nat) (a : AppliedAt P),
            ap[apIdx]? = some (j', a) → a.2.tag ≠ some dr.index.toNat) ∧
          ∃ p : Nat, tqF[p]? = some (some dr.index.toNat, d) ∧
            ∀ p' : Nat, (tqF[p']?.map Prod.fst) = some (some dr.index.toNat) → p' = p))

/-- **D-S9 pass (the intermediate moves).** In one tagged pass that succeeds, `passParams` and
`passLoop` produce `r : PassResult P f` with stop index `r.next ≤ tq.length`: `tq'` is
`tq.drop r.next ++ r.postponed`; the consumed prefix `tq.take r.next` partitions **in exact order
and multiplicity** via `PassPartition` into the applied entries `ap` and the postponed entries
`r.postponed`; every applied index `idx < ap.length` executed `applyPendingDeposit`; and every
postponed entry holds the pubkey of an exiting-but-not-yet-withdrawable validator
(`v.exit_epoch < FAR_FUTURE_EPOCH ∧ nextEpoch ≤ v.withdrawable_epoch`). -/
def D9Pass : Prop :=
  ∀ {P : Preset} {f : CFork} (ctx : Ctx) (state : BeaconState P f) (tq : TQueue)
    (state' : BeaconState P f) (tq' : TQueue) (ap : List (Applied P f)),
    processPendingDepositsTagged ctx state tq = .ok (state', tq', ap) →
    ∃ (nextEpoch : Epoch) (available : U64) (finalizedSlot : Slot) (requestsStart : U64)
      (r : PassResult P f),
      passParams ctx state = .ok (nextEpoch, available, finalizedSlot, requestsStart) ∧
      passLoop ctx nextEpoch available finalizedSlot requestsStart tq 0 U64.zero state [] [] =
        .ok r ∧
      r.applied = ap ∧
      r.next ≤ tq.length ∧
      tq' = tq.drop r.next ++ r.postponed ∧
      PassPartition (tq.take r.next) (ap.map fun a => (a.tag, a.deposit)) r.postponed ∧
      (∀ (idx : Nat) (a : Applied P f), ap[idx]? = some a →
        applyPendingDeposit ctx a.pre a.deposit =
          .ok ((ap[idx + 1]?.map Applied.pre).getD r.state)) ∧
      ((tq.filterMap Prod.fst).Nodup →
        ((ap.map Applied.tag).filterMap id ++ tq'.filterMap Prod.fst).Nodup) ∧
      ∀ e ∈ r.postponed, ∃ i, findValidatorIndex state e.2.pubkey = some i ∧
        ∃ v, state.validators.get i "process_pending_deposits" = .ok v ∧
          v.exit_epoch < FAR_FUTURE_EPOCH ∧ nextEpoch ≤ v.withdrawable_epoch

/-! ## D-S9 conservation (consensus half) -/

/-- The Gwei a run's applied tagged entries were credited. -/
noncomputable def creditedTotal (ctx : Ctx) (ap : List (Nat × AppliedAt P)) : Nat :=
  (ap.filter fun a => a.2.2.tag.isSome).foldr (fun a acc =>
    match classifyApply ctx a.2.2.pre a.2.2.deposit with
    | .ok o => o.credited a.2.2.deposit + acc
    | .error _ => acc) 0

/-- The Gwei of a run's applied tagged entries that received no credit. -/
noncomputable def uncreditedTotal (ctx : Ctx) (ap : List (Nat × AppliedAt P)) : Nat :=
  (ap.filter fun a => a.2.2.tag.isSome).foldr (fun a acc =>
    match classifyApply ctx a.2.2.pre a.2.2.deposit with
    | .ok .noCredit => a.2.2.deposit.amount.toNat + acc
    | _ => acc) 0

/-- The Gwei of the tagged entries of a queue. -/
def taggedTotal (tq : TQueue) : Nat :=
  ((tq.filter fun e => e.1.isSome).map fun e => e.2.amount.toNat).sum

/-- **D-S9 conservation, consensus half.** On a `JointRunIngress` with BLS on, post-genesis block
slots, an anchor ledger, and fresh indices, occurrence accounting balances exactly: credited plus
uncredited applied Gwei plus the tagged Gwei still pending equals the anchor's tagged Gwei plus
the Gwei of every deposit request the run's blocks carried. -/
def D9Conservation : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {anchor final : JointState P}
    (ingress : JointRunIngress cfg ccfg true anchor final) (tq₀ : TQueue),
    (∀ D ∈ ingress.steps, D.block.2.message.slot ≠ GENESIS_SLOT) →
    AnchorLedger anchor tq₀ → RunIndicesFreshIngress ingress tq₀ →
    ∃ tqF ap, runLedger 0 ingress.steps tq₀ [] = .ok (tqF, ap) ∧
      creditedTotal (jointCtx ccfg true) ap + uncreditedTotal (jointCtx ccfg true) ap +
          taggedTotal tqF =
        taggedTotal tq₀ + ((ingressDepositRequests ingress).map fun dr => dr.amount.toNat).sum

/-! ## Controls and closed witnesses, in statement form -/

/-- The replay mutant of the pass: it applies like the real pass but also keeps every applied
entry in the queue. -/
def processPendingDepositsReplay (ctx : Ctx) (state : BeaconState P f) (tq : TQueue) :
    M (BeaconState P f × TQueue × List (Applied P f)) := do
  let (st, rest, ap) ← processPendingDepositsTagged ctx state tq
  pure (st, rest ++ ap.map (fun a => (a.tag, a.deposit)), ap)

/-- **Tagged occurrence-accounting control (replay).** One closed Electra state and aligned tagged
queue (`tq` matches `state.pending_deposits`, with distinct tags and at least one positive-amount
tagged entry applied) on which the real pass balances (`taggedTotal` of applied + remaining equals
input `taggedTotal`) while `processPendingDepositsReplay` does not: replaying an applied queue
occurrence breaks tagged occurrence conservation. -/
def D9ReplayControl : Prop :=
  ∃ (ctx : Ctx) (state : BeaconState Preset.minimal .electra) (tq : TQueue)
    (s₁ s₂ : BeaconState Preset.minimal .electra) (q₁ q₂ : TQueue)
    (a₁ a₂ : List (Applied Preset.minimal .electra)),
    (do pure (← state.pendingDeposits).toArray.toList) = (.ok (tq.map Prod.snd) : M _) ∧
    (tq.filterMap Prod.fst).Nodup ∧
    (∃ a ∈ a₁, a.tag.isSome ∧ 0 < a.deposit.amount.toNat) ∧
    processPendingDepositsTagged ctx state tq = .ok (s₁, q₁, a₁) ∧
    processPendingDepositsReplay ctx state tq = .ok (s₂, q₂, a₂) ∧
    taggedTotal (a₁.map fun a => (a.tag, a.deposit)) + taggedTotal q₁ = taggedTotal tq ∧
    taggedTotal (a₂.map fun a => (a.tag, a.deposit)) + taggedTotal q₂ ≠ taggedTotal tq

/-- The all-zero 96-byte BLS signature (`0x00…00`): rejected before any pairing when `bls = true`
(`blsVerify_true_of_head_zero`). -/
def zeroBLSSignature : BLSSignature := ⟨Array.replicate 96 0, Array.size_replicate⟩

/-- **Closed positive-amount `apply_pending_deposit` outcome witnesses.** Full `applyPendingDeposit`
executions with positive amounts (`0 < d.amount.toNat`) and explicit validator/balance effects on
closed Electra states:
1. closed `bls = false` positive-amount new-validator registration (`validators` and `balances`
   grow by 1, new balance `= d.amount`);
2. closed `bls = true` positive-amount top-up on an existing validator (balance increases by
   `d.amount`, even with `zeroBLSSignature`);
3. closed `bls = true` positive-amount invalid-signature (`zeroBLSSignature`) new-key no-credit
   (`s' = s`, no validator added, zero balance credited). -/
def D9OutcomeWitnesses : Prop :=
  (∃ (ccfg : Config) (s s' : BeaconState Preset.minimal .electra) (d : PendingDeposit),
    0 < d.amount.toNat ∧
    s.balances.length = s.validators.length ∧
    ApplyOutcomeSpec ccfg false s s' d .newValidator ∧
    s'.balances.length = s.balances.length + 1) ∧
  (∃ (ccfg : Config) (s s' : BeaconState Preset.minimal .electra) (d : PendingDeposit) (i : Nat),
    0 < d.amount.toNat ∧
    d.signature = zeroBLSSignature ∧
    ApplyOutcomeSpec ccfg true s s' d (.topUp i)) ∧
  (∃ (ccfg : Config) (s s' : BeaconState Preset.minimal .electra) (d : PendingDeposit),
    0 < d.amount.toNat ∧
    d.signature = zeroBLSSignature ∧
    ApplyOutcomeSpec ccfg true s s' d .noCredit)

/-- **Conditional BLS-on new-validator registration vs corrupted-signature comparison.** On one
fixed closed Electra state `s` and positive `amount`:
(a) for every unregistered `key` and `sig` whose deposit message verifies under real BLS
    (`isValidDepositSignature (jointCtx ccfg true) key wc amount sig = .ok true`),
    `applyPendingDeposit` at `bls = true` appends the validator and credits `amount`; and
(b) on the **exact same** `(ccfg, s, wc, amount)` and unregistered `key`, replacing the signature
    with `zeroBLSSignature` yields `.noCredit` and leaves `s` (`validators` and `balances`)
    unchanged. -/
def D9BlsOnNewValidatorConditional : Prop :=
  ∃ (ccfg : Config) (s : BeaconState Preset.minimal .electra) (wc : Bytes32) (amount : Gwei),
    0 < amount.toNat ∧
    s.balances.length = s.validators.length ∧
    s.validators.length < Preset.minimal.VALIDATOR_REGISTRY_LIMIT ∧
    (∀ (key : BLSPubkey) (sig : BLSSignature),
      findValidatorIndex s key = none →
      isValidDepositSignature (jointCtx ccfg true) key wc amount sig = .ok true →
      let d : PendingDeposit :=
        { pubkey := key, withdrawal_credentials := wc, amount := amount,
          signature := sig, slot := ⟨1⟩ }
      ∃ s' : BeaconState Preset.minimal .electra,
        ApplyOutcomeSpec ccfg true s s' d .newValidator ∧
        s'.balances.length = s.balances.length + 1) ∧
    (∀ (key : BLSPubkey),
      findValidatorIndex s key = none →
      let dBad : PendingDeposit :=
        { pubkey := key, withdrawal_credentials := wc, amount := amount,
          signature := zeroBLSSignature, slot := ⟨1⟩ }
      ApplyOutcomeSpec ccfg true s s dBad .noCredit)

/-- **Postponement and stop witnesses.** All witnesses run `processPendingDepositsTagged` on closed
Electra states with aligned `pending_deposits` and `passParams` derived from `(ctx, s)`:
1. a closed pass entering the exiting-but-not-yet-withdrawable postponement branch
   (`r.postponed ≠ []`, `v.exit_epoch < FAR_FUTURE_EPOCH`, `nextEpoch ≤ v.withdrawable_epoch`);
2. for every `stop : PassStop` (`bridge`, `finality`, `count`, `churn`), a closed pass whose
   derived `passParams` cause `passLoop` to stop with `r.stop = some stop`. -/
def D9PassWitnesses : Prop :=
  (∃ (ctx : Ctx) (s s' : BeaconState Preset.minimal .electra) (tq tq' : TQueue)
    (ap : List (Applied Preset.minimal .electra))
    (nextEpoch : Epoch) (available : U64) (finalizedSlot : Slot) (requestsStart : U64)
    (r : PassResult Preset.minimal .electra) (e : Tag × PendingDeposit),
    (do pure (← s.pendingDeposits).toArray.toList) = (.ok (tq.map Prod.snd) : M _) ∧
    passParams ctx s = .ok (nextEpoch, available, finalizedSlot, requestsStart) ∧
    passLoop ctx nextEpoch available finalizedSlot requestsStart tq 0 U64.zero s [] [] = .ok r ∧
    processPendingDepositsTagged ctx s tq = .ok (s', tq', ap) ∧
    e ∈ r.postponed ∧
    ∃ i v, findValidatorIndex s e.2.pubkey = some i ∧
      s.validators.get i "process_pending_deposits" = .ok v ∧
      v.exit_epoch < FAR_FUTURE_EPOCH ∧ nextEpoch ≤ v.withdrawable_epoch) ∧
  ∀ stop : PassStop,
    ∃ (ctx : Ctx) (s s' : BeaconState Preset.minimal .electra) (tq tq' : TQueue)
      (ap : List (Applied Preset.minimal .electra))
      (nextEpoch : Epoch) (available : U64) (finalizedSlot : Slot) (requestsStart : U64)
      (r : PassResult Preset.minimal .electra),
      (do pure (← s.pendingDeposits).toArray.toList) = (.ok (tq.map Prod.snd) : M _) ∧
      passParams ctx s = .ok (nextEpoch, available, finalizedSlot, requestsStart) ∧
      passLoop ctx nextEpoch available finalizedSlot requestsStart tq 0 U64.zero s [] [] = .ok r ∧
      processPendingDepositsTagged ctx s tq = .ok (s', tq', ap) ∧
      r.stop = some stop

end Blanc.Corpus.Freeze.Deposit
