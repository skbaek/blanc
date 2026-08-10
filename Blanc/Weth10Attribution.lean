import Blanc.Weth10HolderFlow

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

/-! ## Per-frame extraction -/

def approveSelector : B256 := selector "approve" [.address, .uint256]

def permitSelector : B256 :=
  selector "permit"
    [.address, .address, .uint256, .uint256, .uint 8, .bytes 32, .bytes 32]

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

end Weth10

end Blanc
