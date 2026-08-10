import Blanc.Weth10HolderFlow
import Blanc.Weth10Permit

/-!
Hardened authorization provenance for the exact Blanc WETH10 runtime.

This module defines the trace-local attribution semantics consumed by the
`weth10-redeem-future-v2` goal: the exact raw word pairs the runtime hashed
while deriving tagged allowance keys during counted committed WETH10
execution, the trace-local `NoAllowanceKeyCollision` hypothesis over those
pairs, per-debit attribution roots derived from the committed slot-write
chain, and the `hardenedOutflow` sub-sum of permanent outflow carrying an
attribution witness.

Everything below is executable data derived from the retained execution
evidence of an `AccountedHistory`.  No definition assumes a conservation
equation, execution success, stability, collision freedom, or any global
keccak/allowance-key injectivity; the sole collision-shaped concept is the
decidable pairwise property of the finitely many touched pairs of one
explicit history.

Chronology matters here, unlike for the commutative balance-flow totals: an
attribution chain follows the *last committed write* to a key.  The stream
below therefore places a flash invocation's contribution after its callback
subtree — the runtime performs its allowance settlement only after the
borrower's callback returns, and the canonical repayment pattern grants the
allowance inside that callback — while every other selector's allowance
activity is a state prefix that precedes any spawned child.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## The projected allowance key -/

/-- The exact tagged key the runtime derives from the two raw words it
hashes: memory word 0 holds the owner word and memory word 1 the spender
word.  This is definitionally the projection used by
`callerAllowanceRuntimeKey` and `flashAllowanceRuntimeKey`. -/
def projectedAllowanceKey (owner spender : B256) : B256 :=
  allowanceTagWord |||
    (allowancePayloadMask &&& Bytes.keccak (owner.toBytes ++ spender.toBytes))

theorem callerAllowanceRuntimeKey_eq_projected (e : Sevm) :
    callerAllowanceRuntimeKey e =
      projectedAllowanceKey (Sevm.argWord e 0) e.caller.toB256 := rfl

theorem flashAllowanceRuntimeKey_eq_projected (e : Sevm) :
    flashAllowanceRuntimeKey e =
      projectedAllowanceKey (normalizedAddressArg e 0)
        e.currentTarget.toB256 := rfl

/-- Every projected key is in the tagged allowance region. -/
theorem projectedAllowanceKey_region (owner spender : B256) :
    InRegion .allowance (projectedAllowanceKey owner spender) :=
  runtimeAllowanceKey_region _

/-- A projected allowance key is never an address-shaped balance key. -/
theorem projectedAllowanceKey_not_valid (owner spender : B256) :
    ¬ ValidAdr (projectedAllowanceKey owner spender) :=
  runtimeAllowanceKey_not_valid _

/-- A projected allowance key is never the flash counter slot. -/
theorem projectedAllowanceKey_ne_flash (owner spender : B256) :
    projectedAllowanceKey owner spender ≠ flashMintedSlot :=
  runtimeAllowanceKey_ne_flash _

/-! ## Allowance-region visits -/

/-- The exact site and data of one committed visit to the tagged allowance
region.  Each visit corresponds to exactly one runtime evaluation of
`allowanceKeyFromMemory`, i.e. one hashed raw word pair.  `before`/`after`
and stored values are the exact words read and written at the projected
key. -/
inductive AllowanceVisit
  /-- The `allowance(owner,spender)` view's read. -/
  | viewRead (value : B256)
  /-- The `approve`/`approveAndCall` store with owner word `CALLER`. -/
  | approveStore (value : B256)
  /-- The store behind `permitRecover`'s recovered-signer equality. -/
  | permitStore (value : B256)
  /-- `transferFrom`/`withdrawFrom` read of an infinite allowance; no write. -/
  | spendMax
  /-- `transferFrom`/`withdrawFrom` finite decrement: reads `before`,
  writes `after = before - amount`. -/
  | spendFinite (before after : B256)
  /-- `flashLoan` post-callback read of an infinite allowance; no write. -/
  | flashMax
  /-- `flashLoan` post-callback finite settlement decrement. -/
  | flashFinite (before after : B256)
deriving DecidableEq

/-- One hashed-pair event: the exact raw owner/spender words the runtime
placed in memory words 0 and 1 before hashing, the visiting frame's actual
caller and depth, and the site data. -/
structure AllowanceEvent where
  owner : B256
  spender : B256
  caller : Adr
  depth : Nat
  visit : AllowanceVisit
deriving DecidableEq

/-- The projected key this event's pair hashes to. -/
def AllowanceEvent.key (event : AllowanceEvent) : B256 :=
  projectedAllowanceKey event.owner event.spender

/-- The exact word this visit read from the projected key, if it reads. -/
def AllowanceVisit.read? : AllowanceVisit → Option B256
  | .viewRead value => some value
  | .approveStore _ => none
  | .permitStore _ => none
  | .spendMax => some B256.max
  | .spendFinite before _ => some before
  | .flashMax => some B256.max
  | .flashFinite before _ => some before

/-- The exact word this visit wrote to the projected key, if it writes. -/
def AllowanceVisit.written? : AllowanceVisit → Option B256
  | .viewRead _ => none
  | .approveStore value => some value
  | .permitStore value => some value
  | .spendMax => none
  | .spendFinite _ after => some after
  | .flashMax => none
  | .flashFinite _ after => some after

/-! ## Per-frame extraction -/

def approveSelector : B256 := selector "approve" [.address, .uint256]

def allowanceSelector : B256 := selector "allowance" [.address, .address]

/-- The deterministic allowance visit of one committed exact WETH10
invocation, from its entry context, entry state, and committed frame post
state.  At most one visit exists per frame.  The flash arm reconstructs its
post-callback read from the committed post state exactly as
`flashAllowanceBranchFromPost` does; every other arm's read precedes any
storage write of the frame, so the entry state is the exact read source. -/
def frameAllowanceEvent (e : Sevm) (pre post : Devm) :
    Option AllowanceEvent :=
  if e.data.length.toB256 = 0 then none
  else if Sevm.selector e = approveSelector ||
      Sevm.selector e = approveAndCallSelector then
    some
      { owner := e.caller.toB256
        spender := Sevm.argWord e 0
        caller := e.caller
        depth := e.depth
        visit := .approveStore (Sevm.argWord e 1) }
  else if Sevm.selector e = permitSelector then
    some
      { owner := Sevm.argWord e 0
        spender := Sevm.argWord e 1
        caller := e.caller
        depth := e.depth
        visit := .permitStore (Sevm.argWord e 2) }
  else if Sevm.selector e = transferFromSelector ||
      Sevm.selector e = withdrawFromSelector then
    if Sevm.argWord e 0 = e.caller.toB256 then none
    else
      let before :=
        (Devm.getStor pre e.currentTarget).get (callerAllowanceRuntimeKey e)
      some
        { owner := Sevm.argWord e 0
          spender := e.caller.toB256
          caller := e.caller
          depth := e.depth
          visit :=
            if before = B256.max then .spendMax
            else .spendFinite before (before - Sevm.argWord e 2) }
  else if Sevm.selector e = flashLoanSelector then
    let after :=
      (Devm.getStor post e.currentTarget).get (flashAllowanceRuntimeKey e)
    some
      { owner := normalizedAddressArg e 0
        spender := e.currentTarget.toB256
        caller := e.caller
        depth := e.depth
        visit :=
          if after = B256.max then .flashMax
          else .flashFinite (after + Sevm.argWord e 2) after }
  else if Sevm.selector e = allowanceSelector then
    some
      { owner := Sevm.argWord e 0
        spender := Sevm.argWord e 1
        caller := e.caller
        depth := e.depth
        visit :=
          .viewRead ((Devm.getStor pre e.currentTarget).get
            (projectedAllowanceKey (Sevm.argWord e 0) (Sevm.argWord e 1))) }
  else none

/-- One counted committed exact WETH10 invocation's attribution record: the
actual caller and depth, the dispatched selector when calldata is nonempty,
the frame's allowance visit if any, and the frame's classified flow action
if any. -/
structure CountedFrame where
  caller : Adr
  depth : Nat
  sel? : Option B256
  allowance : Option AllowanceEvent
  action : Option FlowAction
deriving DecidableEq

def CountedFrame.ofFrame (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) : CountedFrame :=
  { caller := frame.sevm.caller
    depth := frame.sevm.depth
    sel? :=
      if frame.sevm.data.length.toB256 = 0 then none
      else some (Sevm.selector frame.sevm)
    allowance := frameAllowanceEvent frame.sevm frame.pre frame.post
    action := frame.flowAction? dp ca }

/-- Whether an entry context dispatches to `flashLoan`, the one selector
whose allowance activity chronologically follows its spawned callback. -/
def isFlashInvocation (e : Sevm) : Bool :=
  e.data.length.toB256 ≠ 0 && Sevm.selector e = flashLoanSelector

/-! ## Chronological attribution stream -/

/-- Place one committed frame's own record around its descendant stream
according to the runtime phase of its allowance activity. -/
def Exec.frameContribution (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) (inner : List CountedFrame) : List CountedFrame :=
  if frame.exactInvocation dp ca then
    let own := CountedFrame.ofFrame dp ca frame
    if isFlashInvocation frame.sevm then inner ++ [own] else own :: inner
  else inner

/-- Chronological counted-frame stream contributed by the committed spawned
descendants of a running derivation, excluding the current frame's own
record.  Children whose complete frame settlement does not commit contribute
nothing, exactly as in `Exec.descendantFrames`. -/
def Exec.attributionInner (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List CountedFrame :=
  match run with
  | .halt _ => []
  | .cont _ next => Exec.attributionInner dp ca next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next => Exec.attributionInner dp ca next
  | .runErr _ _ _ _ => []
  | .runOk (f := f) (raw := raw) _ _ child _ next =>
      (if h : Blanc.Weth10.Frame.settlementCommits f raw = true then
        Exec.frameContribution dp ca
          (Exec.Frame.ofRun child
            (Blanc.Weth10.Frame.raw_commits_of_settlementCommits h))
          (Exec.attributionInner dp ca child)
      else []) ++ Exec.attributionInner dp ca next
termination_by sizeOf run

/-- Full chronological stream of one root derivation.  An errored root
contributes nothing, exactly as in `Exec.committedFrames`. -/
def Exec.attributionStream (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List CountedFrame :=
  if h : Execution.commits out = true then
    Exec.frameContribution dp ca (Exec.Frame.ofRun run h)
      (Exec.attributionInner dp ca run)
  else []

def RetainedXlot.attributionStream (dp : DeployParams) (ca : Adr)
    {xl : Xlot} : RetainedXlot xl → List CountedFrame
  | .none => []
  | .some run => Exec.attributionStream dp ca run

def MessageCallTrace.attributionStream (dp : DeployParams) (ca : Adr)
    {msg : Msg} {state : State} {out : MsgCallOutput} :
    MessageCallTrace msg state out → List CountedFrame
  | .createCollision .. => []
  | .createRun _ _ evm _ trace _ =>
      if evm.error.isSome then []
      else trace.retained.attributionStream dp ca
  | .callRun _ _ _ _ _ _ _ _ trace _ =>
      trace.retained.attributionStream dp ca

def TransactionTrace.attributionStream (dp : DeployParams) (ca : Adr)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    List CountedFrame :=
  trace.message.attributionStream dp ca

def ApplyTransactionsTrace.attributionStream (dp : DeployParams) (ca : Adr) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    ApplyTransactionsTrace txs benv bout finalBenv finalBout →
      List CountedFrame
  | _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, .cons head tail =>
      head.attributionStream dp ca ++ tail.attributionStream dp ca

def SystemMessageTrace.attributionStream (dp : DeployParams) (ca : Adr)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    List CountedFrame :=
  trace.message.attributionStream dp ca

def RequestsTrace.attributionStream (dp : DeployParams) (ca : Adr)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') : List CountedFrame :=
  trace.withdrawal.attributionStream dp ca ++
    trace.consolidation.attributionStream dp ca

def AppliedBodyTrace.attributionStream (dp : DeployParams) (ca : Adr)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) :
    List CountedFrame :=
  trace.beacon.attributionStream dp ca ++
    trace.history.attributionStream dp ca ++
    trace.transactions.attributionStream dp ca ++
    trace.requests.attributionStream dp ca

def AccountedBlock.attributionStream (dp : DeployParams) (ca : Adr)
    {chainId : UInt64} {pre post : BlockChain}
    (accounted : AccountedBlock chainId dp ca pre post) :
    List CountedFrame :=
  accounted.bodyTrace.attributionStream dp ca

/-- The complete chronological attribution ledger of an accounted history:
one record per counted committed exact WETH10 invocation, in committed
runtime order. -/
def AccountedHistory.attributionLedger
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory chainId dp ca checkpoint future → List CountedFrame
  | .refl _ _ _ => []
  | .step prior accounted =>
      prior.attributionLedger ++ accounted.attributionStream dp ca

/-! ## Touched pairs and the trace-local collision hypothesis -/

/-- The exact raw word pairs the runtime hashed while deriving tagged
allowance keys during counted execution, in trace order, duplicates
retained, raw words undisturbed. -/
def touchedAllowancePairs
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) :
    List (B256 × B256) :=
  history.attributionLedger.filterMap fun frame =>
    frame.allowance.map fun event => (event.owner, event.spender)

/-- Distinct touched pair values have distinct projected keys.  This is a
decidable property of the explicit history's finitely many touched pairs,
never a global injectivity assumption. -/
def NoAllowanceKeyCollision
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) : Prop :=
  (touchedAllowancePairs history).Pairwise fun p q =>
    p ≠ q →
      projectedAllowanceKey p.1 p.2 ≠ projectedAllowanceKey q.1 q.2

instance {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) :
    Decidable (NoAllowanceKeyCollision history) := by
  unfold NoAllowanceKeyCollision
  infer_instance

/-! ## Attribution roots and the hardened outflow fold -/

/-- The root category of the committed slot-write chain governing a debit:
the most recent committed `approve`-site or committed successful
`permit`-site write to the key, reached through any interleaved finite
decrements, or the checkpoint when no counted write precedes the debit. -/
inductive AttributionRoot
  /-- Most recent root write is the `approve` store; carries its actual
  caller, the normalized owner of the stored pair. -/
  | approve (caller : Adr)
  /-- Most recent root write is the committed successful `permit` store;
  carries the exact raw owner word, equal to the recovered signer word. -/
  | permit (owner : B256)
  /-- No counted write precedes the debit: the governing value was already
  booked at the checkpoint. -/
  | checkpoint
deriving DecidableEq

/-- Walk a most-recent-first event stream back to the attribution root of
`key`.  Reads and infinite-allowance arms are transparent; finite decrements
never increase spending power, so the chain passes through them to the
originating store or the checkpoint. -/
def attributionRootAt : List CountedFrame → B256 → AttributionRoot
  | [], _ => .checkpoint
  | frame :: rest, key =>
      match frame.allowance with
      | some event =>
          if event.key = key then
            match event.visit with
            | .approveStore _ => .approve event.caller
            | .permitStore _ => .permit event.owner
            | _ => attributionRootAt rest key
          else attributionRootAt rest key
      | none => attributionRootAt rest key

/-- Walk a most-recent-first event stream back to the last committed write
to `key`, if any: reads and infinite-allowance arms are transparent, and
every writing visit — store or decrement — supplies its written word. -/
def lastAllowanceWriteAt : List CountedFrame → B256 → Option B256
  | [], _ => none
  | frame :: rest, key =>
      match frame.allowance with
      | some event =>
          if event.key = key then
            match event.visit.written? with
            | some value => some value
            | none => lastAllowanceWriteAt rest key
          else lastAllowanceWriteAt rest key
      | none => lastAllowanceWriteAt rest key

/-- Whether a root is a committed authorizing act of holder `u` or a
checkpoint-preexisting allowance.  Both `approve`'s owner word (the `CALLER`
opcode's clean word) and a committed successful `permit`'s owner word (checked
equal to the recovered signer word) normalize to the acting holder. -/
def AttributionRoot.attributedTo : AttributionRoot → Adr → Bool
  | .approve caller, u => caller = u
  | .permit owner, u => owner.toAdr = u
  | .checkpoint, _ => true

/-- Whether one debit carries a hardened attribution witness for holder `u`
against the most-recent-first stream of earlier counted frames: a direct
caller debit, the raw-word self-bypass, or an allowance-branch debit whose
governing slot-write chain roots at a committed `approve` by `u`, a
committed successful `permit` for owner `u`, or the checkpoint. -/
def DebitProvenance.hardenedFor (debit : DebitProvenance)
    (recent : List CountedFrame) (u : Adr) : Bool :=
  match debit.branch with
  | .direct => debit.actualCaller = u
  | .delegated .selfBypass => debit.actualCaller = u
  | .delegated (.finite key _ _) =>
      (attributionRootAt recent key).attributedTo u
  | .delegated (.maximum key) =>
      (attributionRootAt recent key).attributedTo u
  | .flash .selfBypass => false
  | .flash (.finite key _ _) =>
      (attributionRootAt recent key).attributedTo u
  | .flash (.maximum key) =>
      (attributionRootAt recent key).attributedTo u

/-- One counted frame's contribution to holder `u`'s permanent outflow:
committed ETH redemption plus committed external token transfer out.  Flash
pairs cancel and contribute nothing here. -/
def CountedFrame.permanentOutflow (frame : CountedFrame) (u : Adr) : Nat :=
  match frame.action with
  | some action =>
      (action.atom.holderFlow u).redeemed +
        (action.atom.holderFlow u).externalTransferredOut
  | none => 0

/-- One counted frame's hardened contribution: its permanent outflow when
its debit carries an attribution witness for `u`, else zero.  An action
without retained debit provenance is a mint and carries no outflow. -/
def CountedFrame.hardenedContribution (frame : CountedFrame)
    (recent : List CountedFrame) (u : Adr) : Nat :=
  match frame.action with
  | some action =>
      match action.debit with
      | some debit =>
          if debit.hardenedFor recent u then frame.permanentOutflow u else 0
      | none => 0
  | none => 0

private def hardenedOutflowGo (u : Adr) :
    List CountedFrame → List CountedFrame → Nat
  | _, [] => 0
  | recent, frame :: rest =>
      frame.hardenedContribution recent u +
        hardenedOutflowGo u (frame :: recent) rest

/-- The sub-sum of holder `u`'s permanent outflow whose debits carry a
hardened attribution witness, computed over the chronological attribution
ledger of the history. -/
def hardenedOutflow
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future)
    (u : Adr) : Nat :=
  hardenedOutflowGo u [] history.attributionLedger

/-! ## Dormancy predicates -/

/-- Every allowance slot whose owner word normalizes to `u` is zero in `w`'s
storage at `ca`, for every spender word.  This quantifies over raw words, so
dirty aliases of `u` are covered. -/
def AllowanceQuiescent (ca u : Adr) (w : Jaune.State) : Prop :=
  ∀ owner spender : B256, owner.toAdr = u →
    (w.getStor ca).get (projectedAllowanceKey owner spender) = 0

/-- Whether one counted frame is a committed authorizing act of `u`: a
counted committed WETH10-at-`ca` execution with actual caller `u`, or a
committed successful `permit` whose owner argument normalizes to `u`. -/
def CountedFrame.authorizes (frame : CountedFrame) (u : Adr) : Bool :=
  frame.caller = u ||
    match frame.allowance with
    | some event =>
        match event.visit with
        | .permitStore _ => event.owner.toAdr = u
        | _ => false
    | none => false

/-- No counted committed WETH10-at-`ca` execution with caller `u`, and no
committed successful `permit` whose owner argument normalizes to `u`. -/
def NoAuthorizingActBy
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (u : Adr)
    (history : AccountedHistory chainId dp ca checkpoint future) : Prop :=
  ∀ frame ∈ history.attributionLedger, frame.authorizes u = false

instance {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} (u : Adr)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    Decidable (NoAuthorizingActBy u history) := by
  unfold NoAuthorizingActBy
  infer_instance

/-! ## Basic bounds -/

theorem CountedFrame.hardenedContribution_le
    (frame : CountedFrame) (recent : List CountedFrame) (u : Adr) :
    frame.hardenedContribution recent u ≤ frame.permanentOutflow u := by
  cases hframe : frame.action with
  | none =>
      simp [CountedFrame.hardenedContribution, hframe]
  | some action =>
      cases hdebit : action.debit with
      | none =>
          simp [CountedFrame.hardenedContribution, hframe, hdebit]
      | some debit =>
          by_cases h : debit.hardenedFor recent u <;>
            simp [CountedFrame.hardenedContribution, hframe, hdebit, h]

/-! ## Executable boundary fixtures

These values exercise only the attribution-root walk, the hardened-outflow
fold, and the dormancy predicate defined above.  They are deliberately not
presented as authentic executions: execution authenticity is supplied by the
compiled/history theorems of the surrounding modules, while these fixtures
independently pin the list-level semantics of `attributionRootAt`,
`DebitProvenance.hardenedFor`, `CountedFrame.hardenedContribution`, and
`CountedFrame.authorizes` against concrete multi-frame ledgers. -/

/-- Build one counted frame from just its caller, allowance visit, and flow
action; `depth` and `sel?` are irrelevant to every fold exercised below. -/
private def fixtureFrame (caller : Adr) (allowance : Option AllowanceEvent)
    (action : Option FlowAction) : CountedFrame :=
  { caller, depth := 1, sel? := none, allowance, action }

/-! ### Approve-rooted decrement chain

Holder `u` approves spender `sp`, who spends 40 then 60 of a 100 allowance.
Both spends' governing chain roots back at the single `approve`, and the sum
of hardened contributions matches the sum of permanent outflow exactly. -/

private def approveFrame1 (u : Adr) (ow sp : B256) : CountedFrame :=
  fixtureFrame u
    (some
      { owner := ow
        spender := sp
        caller := u
        depth := 1
        visit := .approveStore 100 })
    none

private def spend40Debit (u : Adr) (ow sp : B256) : DebitProvenance :=
  { actualCaller := sp.toAdr
    rawSource := u.toB256
    source := u
    branch := .delegated (.finite (projectedAllowanceKey ow sp) 100 60) }

private def spendFrame40 (u w : Adr) (ow sp : B256) : CountedFrame :=
  fixtureFrame sp.toAdr
    (some
      { owner := ow
        spender := sp
        caller := sp.toAdr
        depth := 1
        visit := .spendFinite 100 60 })
    (some
      { atom := .transfer u.toB256 w.toB256 u w 40
        credit := none
        debit := some (spend40Debit u ow sp)
        actualCaller := sp.toAdr
        currentTarget := 0
        codeAddress := some 0
        depth := 1 })

private def spend60Debit (u : Adr) (ow sp : B256) : DebitProvenance :=
  { actualCaller := sp.toAdr
    rawSource := u.toB256
    source := u
    branch := .delegated (.finite (projectedAllowanceKey ow sp) 60 0) }

private def spendFrame60 (u w : Adr) (ow sp : B256) : CountedFrame :=
  fixtureFrame sp.toAdr
    (some
      { owner := ow
        spender := sp
        caller := sp.toAdr
        depth := 1
        visit := .spendFinite 60 0 })
    (some
      { atom := .transfer u.toB256 w.toB256 u w 60
        credit := none
        debit := some (spend60Debit u ow sp)
        actualCaller := sp.toAdr
        currentTarget := 0
        codeAddress := some 0
        depth := 1 })

private def approveDecrementLedger (u w : Adr) (ow sp : B256) : List CountedFrame :=
  [approveFrame1 u ow sp, spendFrame40 u w ow sp, spendFrame60 u w ow sp]

theorem approveDecrementLedger_root_before_spend40 (u : Adr) (ow sp : B256) :
    attributionRootAt [approveFrame1 u ow sp] (projectedAllowanceKey ow sp) =
      .approve u := by
  simp [approveFrame1, fixtureFrame, attributionRootAt, AllowanceEvent.key]

theorem approveDecrementLedger_root_before_spend60 (u w : Adr) (ow sp : B256) :
    attributionRootAt [spendFrame40 u w ow sp, approveFrame1 u ow sp]
        (projectedAllowanceKey ow sp) =
      .approve u := by
  simp [spendFrame40, approveFrame1, fixtureFrame, attributionRootAt, AllowanceEvent.key]

theorem spend40Debit_hardenedFor (u : Adr) (ow sp : B256) :
    (spend40Debit u ow sp).hardenedFor [approveFrame1 u ow sp] u = true := by
  simp [spend40Debit, DebitProvenance.hardenedFor, approveFrame1, fixtureFrame,
    attributionRootAt, AllowanceEvent.key, AttributionRoot.attributedTo]

theorem spend60Debit_hardenedFor (u w : Adr) (ow sp : B256) :
    (spend60Debit u ow sp).hardenedFor [spendFrame40 u w ow sp, approveFrame1 u ow sp] u =
      true := by
  simp [spend60Debit, DebitProvenance.hardenedFor, spendFrame40, approveFrame1, fixtureFrame,
    attributionRootAt, AllowanceEvent.key, AttributionRoot.attributedTo]

theorem approveDecrementLedger_hardenedOutflow_eq_permanentOutflow
    (u w : Adr) (ow sp : B256) (hne : u ≠ w) :
    hardenedOutflowGo u [] (approveDecrementLedger u w ow sp) = 100 ∧
    (approveFrame1 u ow sp).permanentOutflow u +
        (spendFrame40 u w ow sp).permanentOutflow u +
        (spendFrame60 u w ow sp).permanentOutflow u =
      100 := by
  constructor
  · simp [approveDecrementLedger, hardenedOutflowGo, approveFrame1, spendFrame40,
      spendFrame60, CountedFrame.hardenedContribution, CountedFrame.permanentOutflow,
      FlowAtom.holderFlow, HolderFlow.zero, fixtureFrame, spend40Debit, spend60Debit,
      DebitProvenance.hardenedFor, attributionRootAt, AllowanceEvent.key,
      AttributionRoot.attributedTo, hne.symm]
  · simp [approveFrame1, spendFrame40, spendFrame60, fixtureFrame,
      CountedFrame.permanentOutflow, FlowAtom.holderFlow, HolderFlow.zero, hne.symm]

/-! ### Permit-rooted third-party spend

A relayer submits a `permit` whose owner word normalizes to `u`; a later
spend at the same key by a third party still roots at that `permit`, and
carries a hardened witness for `u` even though `u` acted nowhere in the
ledger. -/

private def permitFrame1 (relayer : Adr) (ow sp : B256) : CountedFrame :=
  fixtureFrame relayer
    (some
      { owner := ow
        spender := sp
        caller := relayer
        depth := 1
        visit := .permitStore 1 })
    none

private def permitSpendDebit (u : Adr) (ow sp : B256) : DebitProvenance :=
  { actualCaller := sp.toAdr
    rawSource := u.toB256
    source := u
    branch := .delegated (.finite (projectedAllowanceKey ow sp) 50 20) }

private def permitSpendFrame (u w : Adr) (ow sp : B256) : CountedFrame :=
  fixtureFrame sp.toAdr
    (some
      { owner := ow
        spender := sp
        caller := sp.toAdr
        depth := 1
        visit := .spendFinite 50 20 })
    (some
      { atom := .transfer u.toB256 w.toB256 u w 30
        credit := none
        debit := some (permitSpendDebit u ow sp)
        actualCaller := sp.toAdr
        currentTarget := 0
        codeAddress := some 0
        depth := 1 })

theorem permitFrame1_root (relayer : Adr) (ow sp : B256) :
    attributionRootAt [permitFrame1 relayer ow sp] (projectedAllowanceKey ow sp) =
      .permit ow := by
  simp [permitFrame1, fixtureFrame, attributionRootAt, AllowanceEvent.key]

theorem permitSpendDebit_hardenedFor (relayer u : Adr) (ow sp : B256) (how : ow.toAdr = u) :
    (permitSpendDebit u ow sp).hardenedFor [permitFrame1 relayer ow sp] u = true := by
  simp [permitSpendDebit, DebitProvenance.hardenedFor, permitFrame1, fixtureFrame,
    attributionRootAt, AllowanceEvent.key, AttributionRoot.attributedTo, how]

/-! ### Checkpoint root

A spend at a key with no preceding counted write in the ledger roots at the
checkpoint, and still carries a hardened witness: the checkpoint-preexisting
allowance is exactly as attributable as a committed `approve`. -/

private def checkpointSpendDebit (u : Adr) (ow sp : B256) : DebitProvenance :=
  { actualCaller := sp.toAdr
    rawSource := u.toB256
    source := u
    branch := .delegated (.finite (projectedAllowanceKey ow sp) 80 50) }

private def checkpointSpendFrame (u w : Adr) (ow sp : B256) : CountedFrame :=
  fixtureFrame sp.toAdr
    (some
      { owner := ow
        spender := sp
        caller := sp.toAdr
        depth := 1
        visit := .spendFinite 80 50 })
    (some
      { atom := .transfer u.toB256 w.toB256 u w 30
        credit := none
        debit := some (checkpointSpendDebit u ow sp)
        actualCaller := sp.toAdr
        currentTarget := 0
        codeAddress := some 0
        depth := 1 })

theorem checkpointSpendDebit_root_at_empty (ow sp : B256) :
    attributionRootAt [] (projectedAllowanceKey ow sp) = .checkpoint := by
  simp [attributionRootAt]

theorem checkpointSpendDebit_hardenedFor (u : Adr) (ow sp : B256) :
    (checkpointSpendDebit u ow sp).hardenedFor [] u = true := by
  simp [checkpointSpendDebit, DebitProvenance.hardenedFor, attributionRootAt,
    AttributionRoot.attributedTo]

/-! ### Max-allowance transparency

A `transferFrom` against an infinite allowance reads but never writes; the
attribution chain passes straight through the `.spendMax` visit to the
preceding `approve`. -/

private def maxApproveFrame (u : Adr) (ow sp : B256) : CountedFrame :=
  fixtureFrame u
    (some
      { owner := ow
        spender := sp
        caller := u
        depth := 1
        visit := .approveStore B256.max })
    none

private def maxSpendDebit (u : Adr) (ow sp : B256) : DebitProvenance :=
  { actualCaller := sp.toAdr
    rawSource := u.toB256
    source := u
    branch := .delegated (.maximum (projectedAllowanceKey ow sp)) }

private def maxSpendFrame (u w : Adr) (ow sp : B256) : CountedFrame :=
  fixtureFrame sp.toAdr
    (some
      { owner := ow
        spender := sp
        caller := sp.toAdr
        depth := 1
        visit := .spendMax })
    (some
      { atom := .transfer u.toB256 w.toB256 u w 15
        credit := none
        debit := some (maxSpendDebit u ow sp)
        actualCaller := sp.toAdr
        currentTarget := 0
        codeAddress := some 0
        depth := 1 })

theorem maxApproveFrame_root (u : Adr) (ow sp : B256) :
    attributionRootAt [maxApproveFrame u ow sp] (projectedAllowanceKey ow sp) =
      .approve u := by
  simp [maxApproveFrame, fixtureFrame, attributionRootAt, AllowanceEvent.key]

theorem maxSpendDebit_hardenedFor (u : Adr) (ow sp : B256) :
    (maxSpendDebit u ow sp).hardenedFor [maxApproveFrame u ow sp] u = true := by
  simp [maxSpendDebit, DebitProvenance.hardenedFor, maxApproveFrame, fixtureFrame,
    attributionRootAt, AllowanceEvent.key, AttributionRoot.attributedTo]

/-! ### Flash decrement link

A flash invocation's post-callback settlement decrement sits between an
`approve` and a later ordinary spend; the ordinary spend's chain walks
through the `.flashFinite` decrement to the same `approve`, while the flash
frame's own permanent outflow is zero since a flash pair cancels. -/

private def flashApproveFrame (u : Adr) (ow sp : B256) : CountedFrame :=
  fixtureFrame u
    (some
      { owner := ow
        spender := sp
        caller := u
        depth := 1
        visit := .approveStore 10 })
    none

private def flashFrame (u : Adr) (ow sp : B256) : CountedFrame :=
  fixtureFrame sp.toAdr
    (some
      { owner := ow
        spender := sp
        caller := sp.toAdr
        depth := 1
        visit := .flashFinite 10 3 })
    (some
      { atom := .flashPair u.toB256 u 7
        credit := none
        debit := some
          { actualCaller := sp.toAdr
            rawSource := u.toB256
            source := u
            branch := .flash (.finite (projectedAllowanceKey ow sp) 10 3) }
        actualCaller := sp.toAdr
        currentTarget := 0
        codeAddress := some 0
        depth := 1 })

private def flashSpendDebit (u : Adr) (ow sp : B256) : DebitProvenance :=
  { actualCaller := sp.toAdr
    rawSource := u.toB256
    source := u
    branch := .delegated (.finite (projectedAllowanceKey ow sp) 3 0) }

theorem flashSpendDebit_root (u : Adr) (ow sp : B256) :
    attributionRootAt [flashFrame u ow sp, flashApproveFrame u ow sp]
        (projectedAllowanceKey ow sp) =
      .approve u := by
  simp [flashFrame, flashApproveFrame, fixtureFrame, attributionRootAt, AllowanceEvent.key]

theorem flashFrame_permanentOutflow_zero (u : Adr) (ow sp : B256) :
    (flashFrame u ow sp).permanentOutflow u = 0 := by
  simp [flashFrame, fixtureFrame, CountedFrame.permanentOutflow, FlowAtom.holderFlow,
    HolderFlow.zero]

/-! ### Dirty-pair separation

An `approve` written at one projected key never governs a spend at a
distinct projected key: `attributionRootAt` falls straight through to the
checkpoint. -/

private def dirtyApproveFrame (u : Adr) (ow1 sp1 : B256) : CountedFrame :=
  fixtureFrame u
    (some
      { owner := ow1
        spender := sp1
        caller := u
        depth := 1
        visit := .approveStore 25 })
    none

private def dirtySpendDebit (u : Adr) (ow2 sp2 : B256) : DebitProvenance :=
  { actualCaller := sp2.toAdr
    rawSource := u.toB256
    source := u
    branch := .delegated (.finite (projectedAllowanceKey ow2 sp2) 0 0) }

theorem dirtySpendDebit_root_checkpoint (u : Adr) (ow1 sp1 ow2 sp2 : B256)
    (hk : projectedAllowanceKey ow1 sp1 ≠ projectedAllowanceKey ow2 sp2) :
    attributionRootAt [dirtyApproveFrame u ow1 sp1] (projectedAllowanceKey ow2 sp2) =
      .checkpoint := by
  simp [dirtyApproveFrame, fixtureFrame, attributionRootAt, AllowanceEvent.key, hk]

/-! ### Dormant vs. non-dormant

Ledger A never has `u` act and never has a committed `permit` naming `u`:
every frame's `authorizes u` is false and `u`'s permanent outflow across the
ledger is zero.  Ledger B is identical except `u` additionally approves
somewhere in the middle; that one frame now authorizes `u`, so the
`NoAuthorizingActBy`-shaped premise fails for ledger B, while the unrelated
holder `w`'s own spend still roots exactly as it did in ledger A. -/

private def dormantMintFrame (other u : Adr) : CountedFrame :=
  fixtureFrame other none
    (some
      { atom := .ordinaryMint u.toB256 u 5
        credit := none
        debit := none
        actualCaller := other
        currentTarget := 0
        codeAddress := some 0
        depth := 1 })

private def dormantApproveFrame (w : Adr) (spW : B256) : CountedFrame :=
  fixtureFrame w
    (some
      { owner := w.toB256
        spender := spW
        caller := w
        depth := 1
        visit := .approveStore 40 })
    none

private def dormantSpendFrame (w : Adr) (spW : B256) : CountedFrame :=
  fixtureFrame spW.toAdr
    (some
      { owner := w.toB256
        spender := spW
        caller := spW.toAdr
        depth := 1
        visit := .spendFinite 40 10 })
    (some
      { atom := .transfer w.toB256 spW w spW.toAdr 30
        credit := none
        debit := some
          { actualCaller := spW.toAdr
            rawSource := w.toB256
            source := w
            branch := .delegated (.finite (projectedAllowanceKey w.toB256 spW) 40 10) }
        actualCaller := spW.toAdr
        currentTarget := 0
        codeAddress := some 0
        depth := 1 })

private def dormantLedger (other u w : Adr) (spW : B256) : List CountedFrame :=
  [dormantMintFrame other u, dormantApproveFrame w spW, dormantSpendFrame w spW]

theorem dormantLedger_authorizes_false (other u w : Adr) (spW : B256)
    (hother : other ≠ u) (hw : w ≠ u) (hsp : spW.toAdr ≠ u) :
    ∀ frame ∈ dormantLedger other u w spW, frame.authorizes u = false := by
  intro frame hframe
  simp [dormantLedger] at hframe
  rcases hframe with rfl | rfl | rfl
  · simp [dormantMintFrame, fixtureFrame, CountedFrame.authorizes, hother]
  · simp [dormantApproveFrame, fixtureFrame, CountedFrame.authorizes, hw]
  · simp [dormantSpendFrame, fixtureFrame, CountedFrame.authorizes, hsp]

theorem dormantLedger_permanentOutflow_zero (other u w : Adr) (spW : B256) (hw : w ≠ u) :
    (dormantMintFrame other u).permanentOutflow u = 0 ∧
    (dormantApproveFrame w spW).permanentOutflow u = 0 ∧
    (dormantSpendFrame w spW).permanentOutflow u = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [dormantMintFrame, fixtureFrame, CountedFrame.permanentOutflow, FlowAtom.holderFlow,
      HolderFlow.zero]
  · simp [dormantApproveFrame, fixtureFrame, CountedFrame.permanentOutflow]
  · by_cases h : spW.toAdr = u <;>
      simp [dormantSpendFrame, fixtureFrame, CountedFrame.permanentOutflow, FlowAtom.holderFlow,
        HolderFlow.zero, hw, h]

private def nonDormantApproveFrameByU (u : Adr) (owU spU : B256) : CountedFrame :=
  fixtureFrame u
    (some
      { owner := owU
        spender := spU
        caller := u
        depth := 1
        visit := .approveStore 15 })
    none

theorem nonDormantApproveFrameByU_authorizes (u : Adr) (owU spU : B256) :
    (nonDormantApproveFrameByU u owU spU).authorizes u = true := by
  simp [nonDormantApproveFrameByU, fixtureFrame, CountedFrame.authorizes]

theorem dormantSpendFrame_root_dormant (other u w : Adr) (spW : B256) :
    attributionRootAt [dormantApproveFrame w spW, dormantMintFrame other u]
        (projectedAllowanceKey w.toB256 spW) =
      .approve w := by
  simp [dormantApproveFrame, fixtureFrame, attributionRootAt, AllowanceEvent.key]

theorem dormantSpendFrame_root_nonDormant (other u w : Adr) (spW owU spU : B256)
    (hk : projectedAllowanceKey owU spU ≠ projectedAllowanceKey w.toB256 spW) :
    attributionRootAt
        [nonDormantApproveFrameByU u owU spU, dormantApproveFrame w spW,
          dormantMintFrame other u]
        (projectedAllowanceKey w.toB256 spW) =
      .approve w := by
  simp [nonDormantApproveFrameByU, dormantApproveFrame, fixtureFrame,
    attributionRootAt, AllowanceEvent.key, hk]

/-! ### Self-bypass and direct debits

A direct-caller redemption and a raw-word self-bypass transfer both carry a
hardened witness unconditionally, and each one's hardened contribution
equals its own permanent outflow. -/

private def directRedeemDebit (u : Adr) : DebitProvenance :=
  { actualCaller := u
    rawSource := u.toB256
    source := u
    branch := .direct }

private def directRedeemFrame (u : Adr) : CountedFrame :=
  fixtureFrame u none
    (some
      { atom := .redemption u.toB256 u u 4
        credit := none
        debit := some (directRedeemDebit u)
        actualCaller := u
        currentTarget := 0
        codeAddress := some 0
        depth := 1 })

private def selfBypassDebit (u : Adr) : DebitProvenance :=
  { actualCaller := u
    rawSource := u.toB256
    source := u
    branch := .delegated .selfBypass }

private def selfBypassTransferFrame (u w : Adr) : CountedFrame :=
  fixtureFrame u none
    (some
      { atom := .transfer u.toB256 w.toB256 u w 2
        credit := none
        debit := some (selfBypassDebit u)
        actualCaller := u
        currentTarget := 0
        codeAddress := some 0
        depth := 1 })

theorem directRedeemDebit_hardenedFor (u : Adr) :
    (directRedeemDebit u).hardenedFor [] u = true := by
  simp [directRedeemDebit, DebitProvenance.hardenedFor]

theorem selfBypassDebit_hardenedFor (u : Adr) :
    (selfBypassDebit u).hardenedFor [] u = true := by
  simp [selfBypassDebit, DebitProvenance.hardenedFor]

theorem directRedeemFrame_hardenedContribution_eq_outflow (u : Adr) :
    (directRedeemFrame u).hardenedContribution [] u =
        (directRedeemFrame u).permanentOutflow u ∧
      (directRedeemFrame u).permanentOutflow u = 4 := by
  simp [directRedeemFrame, fixtureFrame, CountedFrame.hardenedContribution,
    CountedFrame.permanentOutflow, FlowAtom.holderFlow, HolderFlow.zero, directRedeemDebit,
    DebitProvenance.hardenedFor]

theorem selfBypassTransferFrame_hardenedContribution_eq_outflow (u w : Adr) (hne : u ≠ w) :
    (selfBypassTransferFrame u w).hardenedContribution [] u =
        (selfBypassTransferFrame u w).permanentOutflow u ∧
      (selfBypassTransferFrame u w).permanentOutflow u = 2 := by
  simp [selfBypassTransferFrame, fixtureFrame, CountedFrame.hardenedContribution,
    CountedFrame.permanentOutflow, FlowAtom.holderFlow, HolderFlow.zero, selfBypassDebit,
    DebitProvenance.hardenedFor, hne.symm]

/-! ### Duplicate-pair `Pairwise` shape -/

/-- Two identical touched pairs trivially satisfy the pairwise
non-collision shape: the antecedent `p ≠ q` is refutable by `rfl` since both
list elements are literally the same pair, so no keccak evaluation is
needed.  Computed distinct-key evidence for genuinely different touched
pairs lives in the script-altitude fixtures, not here. -/
theorem duplicatePair_pairwise (ow sp : B256) :
    [(ow, sp), (ow, sp)].Pairwise
      (fun p q => p ≠ q → projectedAllowanceKey p.1 p.2 ≠ projectedAllowanceKey q.1 q.2) :=
  List.pairwise_pair.mpr fun h => absurd rfl h

/-! ### Last-committed-write walk -/

theorem approveDecrementLedger_lastWrite_after_approve (u : Adr) (ow sp : B256) :
    lastAllowanceWriteAt [approveFrame1 u ow sp] (projectedAllowanceKey ow sp) =
      some 100 := by
  simp [approveFrame1, fixtureFrame, lastAllowanceWriteAt, AllowanceEvent.key,
    AllowanceVisit.written?]

theorem approveDecrementLedger_lastWrite_after_spend40 (u w : Adr) (ow sp : B256) :
    lastAllowanceWriteAt [spendFrame40 u w ow sp, approveFrame1 u ow sp]
        (projectedAllowanceKey ow sp) =
      some 60 := by
  simp [spendFrame40, fixtureFrame, lastAllowanceWriteAt, AllowanceEvent.key,
    AllowanceVisit.written?]

theorem maxSpend_lastWrite_transparent (u w : Adr) (ow sp : B256) :
    lastAllowanceWriteAt [maxSpendFrame u w ow sp, maxApproveFrame u ow sp]
        (projectedAllowanceKey ow sp) =
      some B256.max := by
  simp [maxSpendFrame, maxApproveFrame, fixtureFrame, lastAllowanceWriteAt, AllowanceEvent.key,
    AllowanceVisit.written?]

theorem flashFrame_lastWrite (u : Adr) (ow sp : B256) :
    lastAllowanceWriteAt [flashFrame u ow sp, flashApproveFrame u ow sp]
        (projectedAllowanceKey ow sp) =
      some 3 := by
  simp [flashFrame, fixtureFrame, lastAllowanceWriteAt, AllowanceEvent.key,
    AllowanceVisit.written?]

theorem emptyLedger_lastWrite_none (k : B256) :
    lastAllowanceWriteAt [] k = none := by
  simp [lastAllowanceWriteAt]

theorem dirtyPair_lastWrite_none (u : Adr) (ow1 sp1 ow2 sp2 : B256)
    (hk : projectedAllowanceKey ow1 sp1 ≠ projectedAllowanceKey ow2 sp2) :
    lastAllowanceWriteAt [dirtyApproveFrame u ow1 sp1] (projectedAllowanceKey ow2 sp2) =
      none := by
  simp [dirtyApproveFrame, fixtureFrame, lastAllowanceWriteAt, AllowanceEvent.key, hk]

end Weth10

end Blanc
