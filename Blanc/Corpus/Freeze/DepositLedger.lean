import Blanc.JointHistory

/-!
# G0 freeze, part d: the consensus half of D-S9 (fate, credit, conservation)

Goal `protocol-contract-corpus-v1` rev 2, cells D-S9 fate and credit and D-S9 conservation, the
consensus half. Freeze record only: this module is not in the root or the layering
classification, and it proves nothing. Each cell is a `def … : Prop`; a later proof is
`theorem … : …`.

**The ledger.** A pending deposit carries no index, and two requests with equal key, credentials,
amount and signature in one block give equal `PendingDeposit`s. So occurrences are tracked by a
ghost tag carried beside each queue entry: `some i` for the deposit request whose `index` is `i`,
`none` for every other source. The tagged replicas below run the same Jaune calls as
`process_slots`, `process_epoch` and `process_pending_deposits` with the tag list threaded
through; `PassMirror`, `SlotsMirror` and `StepMirror` freeze the bridge that the replicas leave
Jaune's results unchanged (proof machinery, stated so the reviewer can check it is the bridge
the headline needs). Every write of `pending_deposits` in Electra and Fulu is one of: the pass
(`process_pending_deposits`), an append by `process_deposit_request` (slot = the block's slot,
at least 1), or an append by another source at `GENESIS_SLOT` (`apply_deposit` for an Eth1
bridge deposit, `queue_excess_active_balance` from a switch to compounding, `upgrade_to_electra`
for pre-activation balances). `upgrade_to_fulu` copies the queue. The block-level appends are
therefore tagged by slot: the `k`-th appended entry with a nonzero slot is request `k`.

New vocabulary, defined here minimally: `Tag`, `TQueue`, `requestPending`, `ApplyOutcome`,
`classifyApply`, the tagged replicas, `stepLedger`, `runLedger`, `AnchorLedger`, `RunIndicesFresh`.
-/

namespace Blanc.Corpus.Freeze.Deposit

open Jaune JauneConsensus Blanc

variable {P : Preset} {f : CFork}

/-! ## Vocabulary -/

/-- A queue entry's ghost source tag: the index of the deposit request it came from, or `none`
for every other source (and for request entries the anchor ledger leaves unattributed). -/
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

/-! ## The tagged replicas -/

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
  let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
  let available ← (← state.depositBalanceToConsume).add?
    (← getActivationExitChurnLimit ctx.cfg state) site
  let finalizedSlot ← computeStartSlotAtEpoch P state.finalized_checkpoint.epoch
  let requestsStart ← state.depositRequestsStartIndex
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

/-- `jointBlockInput` over a tagged queue: the same calls, with the tagged `process_slots`;
`upgrade_to_fulu` copies the queue, so the tags pass through it. -/
def jointBlockInputTagged (ccfg : Config) (bls : Bool) :
    (s : JointState P) → (b : AnySignedBlock P) → TQueue →
      M (BeaconState P b.1 × TQueue × List (AppliedAt P))
  | ⟨.electra, beacon, _⟩, ⟨.electra, sb⟩, tq => do
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

/-- **The anchor ledger** (D's anchor premise, not a G1b invariant): the anchor's tags align with
its queue, only entries at a nonzero slot (request entries) carry a tag, and no tag repeats.
Tagging every entry `none` always meets it; an observed anchor may attribute its request
entries (§ the legacy prefix in the report). -/
def AnchorLedger (anchor : JointState P) (tq₀ : TQueue) : Prop :=
  pendingList anchor = .ok (tq₀.map Prod.snd) ∧
  (∀ e ∈ tq₀, e.1.isSome → e.2.slot ≠ GENESIS_SLOT) ∧
  (tq₀.filterMap Prod.fst).Nodup

/-- The deposit requests of a run, in order. -/
noncomputable def runDepositRequests {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) : List DepositRequest :=
  run.steps.flatMap stepDepositRequests

/-- **Fresh indices** (discharged in the joined D-S9 statement from D-S3 and delivery: the run's
requests carry the contract's consecutive counts from `E₀`, and an anchor tag names a deposit
below `E₀`): the run's request indices are distinct and none is an anchor tag. -/
def RunIndicesFresh {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s₀ s : JointState P}
    (run : JointRun cfg ccfg bls s₀ s) (tq₀ : TQueue) : Prop :=
  (tq₀.filterMap Prod.fst ++ (runDepositRequests run).map fun dr => dr.index.toNat).Nodup

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

/-- Every step of a run keeps the ledger aligned with the queue, and the block's appends are, in
order, other-source entries at `GENESIS_SLOT` and, tagged with its index, `requestPending dr slot`
for each of the block's deposit requests `dr` (`slot` the block's slot). -/
def StepMirror : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : JointRunStep (P := P) cfg ccfg bls) (tq : TQueue),
    pendingList D.pre = .ok (tq.map Prod.snd) →
      ∃ tq' ap, stepLedger D tq = .ok (tq', ap) ∧ pendingList D.post = .ok (tq'.map Prod.snd) ∧
        ∃ st tqS tqA, jointBlockInputTagged ccfg bls D.pre D.block tq = .ok (st, tqS, ap) ∧
          tq' = tqS ++ tqA ∧
          tqA.filter (fun e => e.1.isSome) = (stepDepositRequests D).map
            (fun dr => (some dr.index.toNat, requestPending dr D.block.2.message.slot)) ∧
          ∀ e ∈ tqA, e.1 = none → e.2.slot = GENESIS_SLOT

/-! ## D-S9 fate and credit (consensus half) -/

/-- **D-S9 fate and credit, consensus half.** On a joint run from `anchor` with BLS on, an anchor
ledger `tq₀` and fresh request indices, the ledger is computed, its final queue is the final
state's queue, and every deposit request `dr` of step `j`'s block meets exactly one fate:

* **applied**: exactly one applied entry carries its tag, at a step `j' > j`; that entry is
  `requestPending dr slot` (same key, credentials, amount and signature, the block's slot), applied
  at a later step (a block's appends follow its slots' passes), and
  `apply_pending_deposit` at the state it read has exactly one outcome: a new validator,
  created only when Jaune's real BLS verifies the deposit signature, with balance the amount; a
  top-up of the validator holding the key, whose balance rises by the amount; or no credit, the
  signature failing and the state unchanged (the paid ETH stays in the contract with no
  validator for this occurrence);
* **still pending**: no applied entry carries its tag, and exactly one position of the final
  queue does, holding `requestPending dr slot`.

Postponement and the pass's stops are the intermediate moves of `D9Pass`. Entries from other
sources carry `none` and meet neither clause. -/
def D9Fate : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {anchor final : JointState P}
    (run : JointRun cfg ccfg true anchor final) (tq₀ : TQueue),
    -- the anchor's tags align with its queue; only request entries carry one; none repeats
    AnchorLedger anchor tq₀ →
    -- the run's request indices are distinct and none is an anchor tag (joined form derives it)
    RunIndicesFresh run tq₀ →
    ∃ tqF ap, runLedger 0 run.steps tq₀ [] = .ok (tqF, ap) ∧
      pendingList final = .ok (tqF.map Prod.snd) ∧
      ∀ (j : Nat) (D : JointRunStep (P := P) cfg ccfg true) (k : Nat) (dr : DepositRequest),
        run.steps[j]? = some D → (stepDepositRequests D)[k]? = some dr →
        let d := requestPending dr D.block.2.message.slot
        let ctx := jointCtx ccfg true
        ((∃ (j' : Nat) (a : AppliedAt P), (j', a) ∈ ap ∧ a.2.tag = some dr.index.toNat ∧ j < j' ∧
            (∀ (j'' : Nat) (a' : AppliedAt P), (j'', a') ∈ ap → a'.2.tag = some dr.index.toNat →
              j'' = j' ∧ a' = a) ∧
            a.2.deposit = d ∧
            ∃ o s', classifyApply ctx a.2.pre d = .ok o ∧
              applyPendingDeposit ctx a.2.pre d = .ok s' ∧
              ((o = .newValidator ∧ findValidatorIndex a.2.pre d.pubkey = none ∧
                  isValidDepositSignature ctx d.pubkey d.withdrawal_credentials d.amount
                    d.signature = .ok true ∧
                  addValidatorToRegistry a.2.pre d.pubkey d.withdrawal_credentials d.amount =
                    .ok s') ∨
               (∃ i, o = .topUp i ∧ findValidatorIndex a.2.pre d.pubkey = some i ∧
                  ∃ iv, U64.ofNat? i "ValidatorIndex" = .ok iv ∧
                    increaseBalance a.2.pre iv d.amount = .ok s') ∨
               (o = .noCredit ∧ findValidatorIndex a.2.pre d.pubkey = none ∧
                  isValidDepositSignature ctx d.pubkey d.withdrawal_credentials d.amount
                    d.signature = .ok false ∧ s' = a.2.pre))) ∨
         ((∀ (j' : Nat) (a : AppliedAt P), (j', a) ∈ ap → a.2.tag ≠ some dr.index.toNat) ∧
          ∃ p : Nat, tqF[p]? = some (some dr.index.toNat, d) ∧
            ∀ p' : Nat, (tqF[p']?.map Prod.fst) = some (some dr.index.toNat) → p' = p))

/-- **D-S9 pass (the intermediate moves).** In one tagged pass that succeeds there is a stop
index `next`: every entry before it was either applied (in order) or postponed (in order, to the
end of the queue, and only when the validator holding its key is exiting), and every entry from
it on is kept, in order, at the front. Which check stopped the pass (Eth1 bridge unfinished, at
Electra only; not yet finalized; the per-epoch count; the churn) is `PassResult.stop`; each
occurs (`D9PassWitnesses`). -/
def D9Pass : Prop :=
  ∀ {P : Preset} {f : CFork} (ctx : Ctx) (state : BeaconState P f) (tq : TQueue)
    (state' : BeaconState P f) (tq' : TQueue) (ap : List (Applied P f)),
    processPendingDepositsTagged ctx state tq = .ok (state', tq', ap) →
    ∃ next post, next ≤ tq.length ∧ tq' = tq.drop next ++ post ∧
      List.Sublist post (tq.take next) ∧
      (ap.map fun a => (a.tag, a.deposit)).Sublist (tq.take next) ∧
      ((ap.map fun a => (a.tag, a.deposit)).length + post.length = next) ∧
      ∀ e ∈ post, ∃ i, findValidatorIndex state e.2.pubkey = some i ∧
        ∃ v, state.validators.get i "process_pending_deposits" = .ok v ∧
          v.exit_epoch < FAR_FUTURE_EPOCH

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

/-- **D-S9 conservation, consensus half.** On a joint run with BLS on, an anchor ledger and fresh
indices, occurrence accounting balances exactly: credited plus uncredited applied Gwei plus the
tagged Gwei still pending equals the anchor's tagged Gwei plus the Gwei of every deposit request
the run's blocks carried. So the total credited from deposit-request occurrences is at most the
anchor's tagged Gwei plus the run's requested Gwei; the joined statement turns the right side
into the contract's payments. -/
def D9Conservation : Prop :=
  ∀ {P : Preset} {cfg : ChainConfig} {ccfg : Config} {anchor final : JointState P}
    (run : JointRun cfg ccfg true anchor final) (tq₀ : TQueue),
    AnchorLedger anchor tq₀ → RunIndicesFresh run tq₀ →
    ∃ tqF ap, runLedger 0 run.steps tq₀ [] = .ok (tqF, ap) ∧
      creditedTotal (jointCtx ccfg true) ap + uncreditedTotal (jointCtx ccfg true) ap +
          taggedTotal tqF =
        taggedTotal tq₀ + ((runDepositRequests run).map fun dr => dr.amount.toNat).sum

/-! ## Controls, in statement form -/

/-- The replay mutant of the pass: it applies like the real pass but also keeps every applied
entry in the queue. -/
def processPendingDepositsReplay (ctx : Ctx) (state : BeaconState P f) (tq : TQueue) :
    M (BeaconState P f × TQueue × List (Applied P f)) := do
  let (st, rest, ap) ← processPendingDepositsTagged ctx state tq
  pure (st, rest ++ ap.map (fun a => (a.tag, a.deposit)), ap)

/-- **Conservation control (replay).** One closed Electra state and tagged queue on which the real
pass balances (applied Gwei plus pending tagged Gwei equals the input's tagged Gwei) while the
replay mutant does not: a replayed occurrence breaks the occurrence accounting. -/
def D9ReplayControl : Prop :=
  ∃ (ctx : Ctx) (state : BeaconState Preset.minimal .electra) (tq : TQueue)
    (s₁ s₂ : BeaconState Preset.minimal .electra) (q₁ q₂ : TQueue)
    (a₁ a₂ : List (Applied Preset.minimal .electra)),
    processPendingDepositsTagged ctx state tq = .ok (s₁, q₁, a₁) ∧
    processPendingDepositsReplay ctx state tq = .ok (s₂, q₂, a₂) ∧
    taggedTotal (a₁.map fun a => (a.tag, a.deposit)) + taggedTotal q₁ = taggedTotal tq ∧
    taggedTotal (a₂.map fun a => (a.tag, a.deposit)) + taggedTotal q₂ ≠ taggedTotal tq

/-- **Outcome witnesses.** Each outcome of `apply_pending_deposit` occurs on a closed Electra state
with a positive amount at BLS on. The new-validator case takes B1's form
(`w_register_blsOn`): for every unregistered key and every signature Jaune's real BLS verifies
over its deposit message, the outcome is a new validator; and the same signature with its first
byte zeroed gives no credit. A closed pairing evaluation is not frozen (see the report). -/
def D9OutcomeWitnesses : Prop :=
  (∃ (ccfg : Config) (s : BeaconState Preset.minimal .electra) (wc : Bytes32) (amount : Gwei),
    0 < amount.toNat ∧ ∀ (key : BLSPubkey) (sig : BLSSignature), findValidatorIndex s key = none →
      isValidDepositSignature (jointCtx ccfg true) key wc amount sig = .ok true →
      classifyApply (jointCtx ccfg true) s
        { pubkey := key, withdrawal_credentials := wc, amount, signature := sig, slot := ⟨1⟩ } =
        .ok .newValidator) ∧
  (∃ (ccfg : Config) (s : BeaconState Preset.minimal .electra) (d : PendingDeposit) (i : Nat),
    0 < d.amount.toNat ∧ classifyApply (jointCtx ccfg true) s d = .ok (.topUp i)) ∧
  (∃ (ccfg : Config) (s : BeaconState Preset.minimal .electra) (d : PendingDeposit),
    0 < d.amount.toNat ∧ classifyApply (jointCtx ccfg true) s d = .ok .noCredit)

/-- **Postponement and stop witnesses.** A closed Electra pass that postpones an exiting
validator's entry, and, for each stop reason, a closed pass that stops for it. -/
def D9PassWitnesses : Prop :=
  (∃ (ctx : Ctx) (s s' : BeaconState Preset.minimal .electra) (tq tq' : TQueue)
    (ap : List (Applied Preset.minimal .electra)) (e : Tag × PendingDeposit),
    processPendingDepositsTagged ctx s tq = .ok (s', tq', ap) ∧ e ∈ tq ∧
      tq'.getLast? = some e ∧ ∀ a ∈ ap, (a.tag, a.deposit) ≠ e) ∧
  ∀ stop : PassStop, ∃ (ctx : Ctx) (s : BeaconState Preset.minimal .electra) (tq : TQueue)
    (nextEpoch : Epoch) (available : U64) (finalizedSlot : Slot) (requestsStart : U64)
    (r : PassResult Preset.minimal .electra),
    passLoop ctx nextEpoch available finalizedSlot requestsStart tq 0 U64.zero s [] [] = .ok r ∧
      r.stop = some stop

end Blanc.Corpus.Freeze.Deposit
