import Blanc.ExecutionSettlement
import Blanc.ExecutionHistory
import Blanc.Weth10HolderFlowAlgebra
import Blanc.Weth10Redeemable
import Blanc.Weth10Erc677Functional
import Blanc.Weth10FlashFunctional

/-!
Committed per-holder flow accounting for the exact Blanc WETH10 runtime.

This module deliberately separates the executable data fold below from the
execution and settlement proofs that populate it.  In particular, none of the
action types assumes a balance equation, a successful history, stability, or a
final-state bound.  Later sections tie actions to retained `Exec` trees and to
configured block transitions before proving conservation.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- The public per-holder totals.  The holder remains a nominal index so flows
for different holders do not mix definitionally. -/
structure HolderFlow (u : Adr) where
  ordinaryIn : Nat
  redeemed : Nat
  externalTransferredOut : Nat
  selfTransfer : Nat
  flashCredit : Nat
  flashRepayment : Nat
deriving DecidableEq

def HolderFlow.zero (u : Adr) : HolderFlow u :=
  ⟨0, 0, 0, 0, 0, 0⟩

def HolderFlow.add {u : Adr} (x y : HolderFlow u) : HolderFlow u :=
  ⟨x.ordinaryIn + y.ordinaryIn,
    x.redeemed + y.redeemed,
    x.externalTransferredOut + y.externalTransferredOut,
    x.selfTransfer + y.selfTransfer,
    x.flashCredit + y.flashCredit,
    x.flashRepayment + y.flashRepayment⟩

@[simp] theorem HolderFlow.zero_add {u : Adr} (x : HolderFlow u) :
    (HolderFlow.zero u).add x = x := by
  cases x
  simp [HolderFlow.zero, HolderFlow.add]

@[simp] theorem HolderFlow.add_zero {u : Adr} (x : HolderFlow u) :
    x.add (HolderFlow.zero u) = x := by
  cases x
  simp [HolderFlow.zero, HolderFlow.add]

theorem HolderFlow.add_assoc {u : Adr} (x y z : HolderFlow u) :
    (x.add y).add z = x.add (y.add z) := by
  cases x
  cases y
  cases z
  simp [HolderFlow.add, Nat.add_assoc]

/-- The exact runtime arm accepted before a delegated debit.  Raw keys and
before/after allowance words are retained for the successor provenance goal;
this goal attributes no human intent to them. -/
inductive AllowanceBranch
  | selfBypass
  | finite (key before after : B256)
  | maximum (key : B256)
deriving DecidableEq

/-- Mechanical debit provenance: direct caller, delegated allowance arm, or
flash settlement's post-callback allowance arm. -/
inductive DebitBranch
  | direct
  | delegated (allowance : AllowanceBranch)
  | flash (allowance : AllowanceBranch)
deriving DecidableEq

/-- Per-debit data retained by the committed ledger.  `rawSource` is the word
used by the runtime branch/key path; `source` is its normalized balance key. -/
structure DebitProvenance where
  actualCaller : Adr
  rawSource : B256
  source : Adr
  branch : DebitBranch
deriving DecidableEq

/-- Data-level tag for the caller allowance arm selected by the runtime.  The
full state/log effect remains in `CallerAllowanceOutcome`; this tag makes the
accepted branch and its raw key/value data extractable. -/
def CallerAllowanceTag (e : Sevm) (pre : Devm) (amountArg : B256) :
    AllowanceBranch → Prop
  | .selfBypass => Sevm.argWord e 0 = e.caller.toB256
  | .maximum key =>
      Sevm.argWord e 0 ≠ e.caller.toB256 ∧
      key = callerAllowanceRuntimeKey e ∧
      (Devm.getStor pre e.currentTarget).get key = B256.max
  | .finite key before after =>
      Sevm.argWord e 0 ≠ e.caller.toB256 ∧
      key = callerAllowanceRuntimeKey e ∧
      (Devm.getStor pre e.currentTarget).get key = before ∧
      before ≠ B256.max ∧
      Sevm.argWord e amountArg ≤ before ∧
      after = before - Sevm.argWord e amountArg

def CallerAllowanceAccepted (e : Sevm) (pre core : Devm)
    (amountArg : B256) (branch : AllowanceBranch) : Prop :=
  CallerAllowanceOutcome e pre core amountArg ∧
    CallerAllowanceTag e pre amountArg branch

theorem exists_callerAllowanceAccepted
    {e : Sevm} {pre core : Devm} {amountArg : B256}
    (h : CallerAllowanceOutcome e pre core amountArg) :
    ∃ branch, CallerAllowanceAccepted e pre core amountArg branch := by
  rcases h.1 with hself | ⟨hne, hmax | hfinite⟩
  · exact ⟨.selfBypass, h, hself.1⟩
  · exact ⟨.maximum (callerAllowanceRuntimeKey e), h,
      hne, rfl, hmax.1⟩
  · rcases hfinite with ⟨allowance, hnotmax, hle, hget, _⟩
    exact ⟨.finite (callerAllowanceRuntimeKey e) allowance
      (allowance - Sevm.argWord e amountArg), h,
      hne, rfl, hget, hnotmax, hle, rfl⟩

/-- Data-level tag for flash settlement's max/finite allowance arm. -/
def FlashAllowanceTag (e : Sevm) (settle : Devm) :
    AllowanceBranch → Prop
  | .selfBypass => False
  | .maximum key =>
      key = flashAllowanceRuntimeKey e ∧
      (Devm.getStor settle e.currentTarget).get key = B256.max
  | .finite key before after =>
      key = flashAllowanceRuntimeKey e ∧
      (Devm.getStor settle e.currentTarget).get key = before ∧
      before ≠ B256.max ∧
      Sevm.argWord e 2 ≤ before ∧
      after = before - Sevm.argWord e 2

def FlashAllowanceAccepted (e : Sevm) (settle burn : Devm)
    (branch : AllowanceBranch) : Prop :=
  FlashAllowanceOutcome e settle burn ∧ FlashAllowanceTag e settle branch

theorem exists_flashAllowanceAccepted
    {e : Sevm} {settle burn : Devm}
    (h : FlashAllowanceOutcome e settle burn) :
    ∃ branch, FlashAllowanceAccepted e settle burn branch := by
  rcases h.1 with hmax | hfinite
  · exact ⟨.maximum (flashAllowanceRuntimeKey e), h, rfl, hmax.1⟩
  · rcases hfinite with ⟨allowance, hnotmax, hle, hget, _⟩
    exact ⟨.finite (flashAllowanceRuntimeKey e) allowance
      (allowance - Sevm.argWord e 2), h,
      rfl, hget, hnotmax, hle, rfl⟩

/-- One committed WETH10 invocation's balance-flow category.  A successful
flash invocation is one paired atom, so its exact receiver/principal pairing
is retained rather than reconstructed by matching lookalike burn logs. -/
inductive FlowAtom
  | ordinaryMint (rawRecipient : B256) (recipient : Adr) (amount : Nat)
  | transfer (rawSource rawRecipient : B256)
      (source recipient : Adr) (amount : Nat)
  | redemption (rawSource : B256) (source : Adr)
      (ethRecipient : Adr) (amount : Nat)
  | flashPair (rawReceiver : B256) (receiver : Adr) (amount : Nat)
deriving DecidableEq

/-- The exact modular addition site underlying one credited balance write.
`before` is the recipient word immediately before that addition (after the
source debit for a self-transfer), so `creditLoss before amountWord` measures
precisely whether this individual write wrapped. -/
structure CreditOccurrence where
  recipient : Adr
  before : B256
  amountWord : B256
deriving DecidableEq

def CreditOccurrence.loss (credit : CreditOccurrence) : Nat :=
  creditLoss credit.before credit.amountWord

def CreditOccurrence.Nof (credit : CreditOccurrence) : Prop :=
  B256.Nof credit.before credit.amountWord

theorem CreditOccurrence.loss_eq_zero_iff (credit : CreditOccurrence) :
    credit.loss = 0 ↔ credit.Nof :=
  creditLoss_eq_zero_iff credit.before credit.amountWord

/-- Flow data plus the actual invocation context.  Authenticity proofs later
pin `currentTarget`, `codeAddress`, code, storage writes, and the associated
WETH-emitter log to the retained execution. -/
structure FlowAction where
  atom : FlowAtom
  credit : Option CreditOccurrence
  debit : Option DebitProvenance
  actualCaller : Adr
  currentTarget : Adr
  codeAddress : Option Adr
  depth : Nat
deriving DecidableEq

def FlowAtom.creditOccurrence (pre : Devm) (ca : Adr) :
    FlowAtom → Option CreditOccurrence
  | .ordinaryMint _ recipient amount =>
      some
        { recipient
          before := Stor.rest (Devm.getStor pre ca) recipient
          amountWord := Nat.toB256 amount }
  | .transfer _ _ source recipient amount =>
      let amountWord := Nat.toB256 amount
      let before :=
        if source = recipient then
          Stor.rest (Devm.getStor pre ca) source - amountWord
        else
          Stor.rest (Devm.getStor pre ca) recipient
      some { recipient, before, amountWord }
  | .redemption .. => none
  | .flashPair _ receiver amount =>
      some
        { recipient := receiver
          before := Stor.rest (Devm.getStor pre ca) receiver
          amountWord := Nat.toB256 amount }

/-- Executable contribution of one classified atom to a holder's totals.
Dirty address words branch in `primaryFlowAtom` before their low-160-bit
normalization; normalized aliases therefore become self-transfers here. -/
def FlowAtom.holderFlow (atom : FlowAtom) (u : Adr) : HolderFlow u :=
  match atom with
  | .ordinaryMint _ recipient amount =>
      if recipient = u then
        { HolderFlow.zero u with ordinaryIn := amount }
      else HolderFlow.zero u
  | .transfer _ _ source recipient amount =>
      if source = u then
        if recipient = u then
          { HolderFlow.zero u with selfTransfer := amount }
        else
          { HolderFlow.zero u with externalTransferredOut := amount }
      else if recipient = u then
        { HolderFlow.zero u with ordinaryIn := amount }
      else HolderFlow.zero u
  | .redemption _ source _ amount =>
      if source = u then
        { HolderFlow.zero u with redeemed := amount }
      else HolderFlow.zero u
  | .flashPair _ receiver amount =>
      if receiver = u then
        { HolderFlow.zero u with
          flashCredit := amount
          flashRepayment := amount }
      else HolderFlow.zero u

theorem FlowAtom.holderFlow_flash_eq (atom : FlowAtom) (u : Adr) :
    (atom.holderFlow u).flashCredit =
      (atom.holderFlow u).flashRepayment := by
  cases atom <;> simp only [FlowAtom.holderFlow] <;> aesop

/-- The public numeric fold used by `AccountedHistory.weth10Flow`. -/
def holderFlowOfActions (actions : List FlowAction) (u : Adr) : HolderFlow u :=
  actions.foldl (fun total action =>
    total.add (action.atom.holderFlow u)) (HolderFlow.zero u)

private theorem holderFlowOfActions_from_eq_add
    (actions : List FlowAction) (u : Adr) (initial : HolderFlow u) :
    actions.foldl (fun total action =>
      total.add (action.atom.holderFlow u)) initial =
    initial.add (holderFlowOfActions actions u) := by
  unfold holderFlowOfActions
  induction actions generalizing initial with
  | nil => simp
  | cons action actions ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rw [ih (initial := (HolderFlow.zero u).add
        (action.atom.holderFlow u))]
      rw [HolderFlow.zero_add, HolderFlow.add_assoc]

theorem holderFlowOfActions_append
    (left right : List FlowAction) (u : Adr) :
    holderFlowOfActions (left ++ right) u =
      (holderFlowOfActions left u).add
        (holderFlowOfActions right u) := by
  unfold holderFlowOfActions
  rw [List.foldl_append]
  exact holderFlowOfActions_from_eq_add right u _

private theorem holderFlowOfActions_flash_eq_from
    (actions : List FlowAction) (u : Adr) (initial : HolderFlow u)
    (hinitial : initial.flashCredit = initial.flashRepayment) :
    (actions.foldl (fun total action =>
      total.add (action.atom.holderFlow u)) initial).flashCredit =
    (actions.foldl (fun total action =>
      total.add (action.atom.holderFlow u)) initial).flashRepayment := by
  induction actions generalizing initial with
  | nil => exact hinitial
  | cons action actions ih =>
      simp only [List.foldl_cons]
      apply ih
      simp only [HolderFlow.add]
      rw [hinitial, action.atom.holderFlow_flash_eq]

theorem holderFlowOfActions_flash_eq (actions : List FlowAction) (u : Adr) :
    (holderFlowOfActions actions u).flashCredit =
      (holderFlowOfActions actions u).flashRepayment := by
  apply holderFlowOfActions_flash_eq_from
  rfl

/-- Wrap loss attributed to a holder's credited balance writes. -/
def FlowAction.holderCreditLoss (action : FlowAction) (u : Adr) : Nat :=
  match action.credit with
  | some credit => if credit.recipient = u then credit.loss else 0
  | none => 0

def holderCreditLossOfActions (actions : List FlowAction) (u : Adr) : Nat :=
  (actions.map (fun action => action.holderCreditLoss u)).sum

/-- Every credited write retained by an action is an ordinary, non-wrapping
`B256` addition. -/
def FlowAction.CreditNof (action : FlowAction) : Prop :=
  ∀ credit, action.credit = some credit → credit.Nof

def FlowActionsCreditNof (actions : List FlowAction) : Prop :=
  ∀ action ∈ actions, action.CreditNof

/-- The deterministic, provenance-neutral part of a retained action.  Debit
provenance is stored alongside these observations by the authenticity layer;
the public numeric fold depends only on this uniquely replayable projection. -/
structure FlowObservation where
  atom : FlowAtom
  actualCaller : Adr
  currentTarget : Adr
  codeAddress : Option Adr
  depth : Nat
deriving DecidableEq

def FlowAction.observation (action : FlowAction) : FlowObservation :=
  { atom := action.atom
    actualCaller := action.actualCaller
    currentTarget := action.currentTarget
    codeAddress := action.codeAddress
    depth := action.depth }

def holderFlowOfObservations (observations : List FlowObservation)
    (u : Adr) : HolderFlow u :=
  observations.foldl (fun total observation =>
    total.add (observation.atom.holderFlow u)) (HolderFlow.zero u)

private theorem holderFlowOfObservations_from_eq_add
    (observations : List FlowObservation) (u : Adr)
    (initial : HolderFlow u) :
    observations.foldl (fun total observation =>
      total.add (observation.atom.holderFlow u)) initial =
    initial.add (holderFlowOfObservations observations u) := by
  unfold holderFlowOfObservations
  induction observations generalizing initial with
  | nil => simp
  | cons observation observations ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rw [ih (initial := (HolderFlow.zero u).add
        (observation.atom.holderFlow u))]
      rw [HolderFlow.zero_add, HolderFlow.add_assoc]

theorem holderFlowOfObservations_append
    (left right : List FlowObservation) (u : Adr) :
    holderFlowOfObservations (left ++ right) u =
      (holderFlowOfObservations left u).add
        (holderFlowOfObservations right u) := by
  unfold holderFlowOfObservations
  rw [List.foldl_append]
  exact holderFlowOfObservations_from_eq_add right u _

theorem holderFlowOfObservations_map_observation
    (actions : List FlowAction) (u : Adr) :
    holderFlowOfObservations (actions.map FlowAction.observation) u =
      holderFlowOfActions actions u := by
  unfold holderFlowOfObservations holderFlowOfActions
  have go : ∀ (xs : List FlowAction) (initial : HolderFlow u),
      List.foldl
        (fun total observation =>
          total.add (observation.atom.holderFlow u))
        initial (xs.map FlowAction.observation) =
      List.foldl
        (fun total action => total.add (action.atom.holderFlow u))
        initial xs := by
    intro xs
    induction xs with
    | nil => intro initial; rfl
    | cons action xs ih =>
        intro initial
        simp only [List.map_cons, List.foldl_cons,
          FlowAction.observation]
        exact ih _
  exact go actions _

private theorem holderFlowOfObservations_flash_eq_from
    (observations : List FlowObservation) (u : Adr)
    (initial : HolderFlow u)
    (hinitial : initial.flashCredit = initial.flashRepayment) :
    (observations.foldl (fun total observation =>
      total.add (observation.atom.holderFlow u)) initial).flashCredit =
    (observations.foldl (fun total observation =>
      total.add (observation.atom.holderFlow u)) initial).flashRepayment := by
  induction observations generalizing initial with
  | nil => exact hinitial
  | cons observation observations ih =>
      simp only [List.foldl_cons]
      apply ih
      simp only [HolderFlow.add]
      rw [hinitial, observation.atom.holderFlow_flash_eq]

theorem holderFlowOfObservations_flash_eq
    (observations : List FlowObservation) (u : Adr) :
    (holderFlowOfObservations observations u).flashCredit =
      (holderFlowOfObservations observations u).flashRepayment := by
  apply holderFlowOfObservations_flash_eq_from
  rfl

/-- Exact direct WETH10-at-`ca` invocation context.  `currentTarget` pins the
storage/log owner; `codeAddress` excludes CALLCODE, DELEGATECALL, and EIP-7702
foreign-code execution against that owner; the code witness pins the compiled
runtime family. -/
def exactInvocation (dp : DeployParams) (ca : Adr) (e : Sevm) : Prop :=
  e.currentTarget = ca ∧ e.codeAddress = some ca ∧
    some e.code.toList = Prog.compile (weth10 dp)

instance (dp : DeployParams) (ca : Adr) (e : Sevm) :
    Decidable (exactInvocation dp ca e) := by
  unfold exactInvocation
  infer_instance

def transferSelector : B256 := selector "transfer" [.address, .uint256]

def transferFromSelector : B256 :=
  selector "transferFrom" [.address, .address, .uint256]

def withdrawFromSelector : B256 :=
  selector "withdrawFrom" [.address, .address, .uint256]

def depositSelector : B256 := selector "deposit" []

def depositToSelector : B256 := selector "depositTo" [.address]

/-- Deterministic candidate category for a successful exact WETH10 frame.
Settlement and compiled-write completeness are intentionally not encoded in
this function: the trace relation proves those facts before admitting the
candidate as a `FlowAction`.

The raw recipient word selects the zero/redemption arm before normalization,
matching the runtime.  Consequently a dirty nonzero word normalizing to zero
is an ordinary transfer to balance key zero, and a dirty alias normalizing to
the source is a self-transfer. -/
def primaryFlowAtom (e : Sevm) : Option FlowAtom :=
  if e.data.length.toB256 = 0 then
    some (.ordinaryMint e.caller.toB256 e.caller e.value.toNat)
  else if Sevm.selector e = depositSelector then
    some (.ordinaryMint e.caller.toB256 e.caller e.value.toNat)
  else if Sevm.selector e = depositToSelector ||
      Sevm.selector e = depositToAndCallSelector then
    let raw := Sevm.argWord e 0
    some (.ordinaryMint raw raw.toAdr e.value.toNat)
  else if Sevm.selector e = transferSelector ||
      Sevm.selector e = transferAndCallSelector then
    let rawTo := Sevm.argWord e 0
    let amount := (Sevm.argWord e 1).toNat
    if rawTo = 0 then
      some (.redemption e.caller.toB256 e.caller e.caller amount)
    else
      some (.transfer e.caller.toB256 rawTo e.caller rawTo.toAdr amount)
  else if Sevm.selector e = transferFromSelector then
    let rawFrom := Sevm.argWord e 0
    let rawTo := Sevm.argWord e 1
    let amount := (Sevm.argWord e 2).toNat
    if rawTo = 0 then
      some (.redemption rawFrom rawFrom.toAdr e.caller amount)
    else
      some (.transfer rawFrom rawTo rawFrom.toAdr rawTo.toAdr amount)
  else if Sevm.selector e = withdrawSelector then
    some (.redemption e.caller.toB256 e.caller e.caller
      (Sevm.argWord e 0).toNat)
  else if Sevm.selector e = withdrawToSelector then
    some (.redemption e.caller.toB256 e.caller
      (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toNat)
  else if Sevm.selector e = withdrawFromSelector then
    some (.redemption (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
      (Sevm.argWord e 1).toAdr (Sevm.argWord e 2).toNat)
  else if Sevm.selector e = flashLoanSelector then
    some (.flashPair (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
      (Sevm.argWord e 2).toNat)
  else none

/-- The exact caller-allowance arm selected from the invocation's entry
state.  This is data, not an authorization claim: a finite or maximum branch
records only what the runtime inspected and accepted. -/
def callerAllowanceBranch (e : Sevm) (pre : Devm)
    (amountArg : B256) : AllowanceBranch :=
  if Sevm.argWord e 0 = e.caller.toB256 then
    .selfBypass
  else
    let key := callerAllowanceRuntimeKey e
    let before := (Devm.getStor pre e.currentTarget).get key
    if before = B256.max then
      .maximum key
    else
      .finite key before (before - Sevm.argWord e amountArg)

/-- Flash settlement performs its allowance test after the callback.  The
committed post-state retains the selected arm: a maximum allowance is
unchanged, while a finite arm's pre-debit value is the exact natural
reconstruction `after + amount` proved by the flash effect theorem. -/
def flashAllowanceBranchFromPost (e : Sevm) (post : Devm) : AllowanceBranch :=
  let key := flashAllowanceRuntimeKey e
  let after := (Devm.getStor post e.currentTarget).get key
  if after = B256.max then
    .maximum key
  else
    .finite key (after + Sevm.argWord e 2) after

/-- Deterministic per-debit provenance candidate for a successful exact
invocation.  Later authenticity theorems connect each branch to the
corresponding functional effect and accepted runtime test. -/
def primaryDebitProvenance (e : Sevm) (pre post : Devm) :
    Option DebitProvenance :=
  let direct (rawSource : B256) (source : Adr) : DebitProvenance :=
    { actualCaller := e.caller
      rawSource
      source
      branch := .direct }
  let delegated (rawSource : B256) (amountArg : B256) : DebitProvenance :=
    { actualCaller := e.caller
      rawSource
      source := rawSource.toAdr
      branch := .delegated (callerAllowanceBranch e pre amountArg) }
  if e.data.length.toB256 = 0 then
    none
  else if Sevm.selector e = transferSelector ||
      Sevm.selector e = transferAndCallSelector ||
      Sevm.selector e = withdrawSelector ||
      Sevm.selector e = withdrawToSelector then
    some (direct e.caller.toB256 e.caller)
  else if Sevm.selector e = transferFromSelector then
    some (delegated (Sevm.argWord e 0) 2)
  else if Sevm.selector e = withdrawFromSelector then
    some (delegated (Sevm.argWord e 0) 2)
  else if Sevm.selector e = flashLoanSelector then
    let rawReceiver := Sevm.argWord e 0
    some
      { actualCaller := e.caller
        rawSource := rawReceiver
        source := rawReceiver.toAdr
        branch := .flash (flashAllowanceBranchFromPost e post) }
  else none


/-- Deterministic candidate observation for a retained frame.  The exact
target/code context rejects foreign lookalikes and library-style execution;
the committed-frame traversal supplies the settlement boundary. -/
def Exec.Frame.exactInvocation (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) : Prop :=
  frame.pc = 0 ∧ Blanc.Weth10.exactInvocation dp ca frame.sevm

instance (dp : DeployParams) (ca : Adr) (frame : Exec.Frame) :
    Decidable (Exec.Frame.exactInvocation dp ca frame) := by
  unfold Exec.Frame.exactInvocation
  infer_instance

def Exec.Frame.flowAction? (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) : Option FlowAction :=
  if Exec.Frame.exactInvocation dp ca frame then
    (primaryFlowAtom frame.sevm).map fun atom =>
      { atom
        credit := atom.creditOccurrence frame.pre ca
        debit := primaryDebitProvenance frame.sevm frame.pre frame.post
        actualCaller := frame.sevm.caller
        currentTarget := frame.sevm.currentTarget
        codeAddress := frame.sevm.codeAddress
        depth := frame.sevm.depth }
  else none

def Exec.Frame.flowObservation? (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) : Option FlowObservation :=
  (Exec.Frame.flowAction? dp ca frame).map FlowAction.observation

def Exec.flowActions (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List FlowAction :=
  (Exec.committedFrames run).filterMap
    (Exec.Frame.flowAction? dp ca)

/-- The action contribution of a raw-committing CREATE child is nevertheless
empty when code-deposit settlement rolls the child world back.  This is the
observable ledger falsifier for using `Execution.commits raw` as the retention
test. -/
theorem Exec.retainedChildActions_eq_nil_of_create_codeDepositRollback
    {dp : DeployParams} {ca : Adr} {f : Jaune.Frame}
    {raw : Execution} {settled : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm}
    (child : Exec pc sevm pre raw)
    (_rawCommits : Execution.commits raw = true)
    (hcreate : f.isCreate = true)
    (hsettled : processCreateMessage.settle f.outer
      (processMessage.settle f.inner (executeCode.handleError raw)) =
        .ok settled)
    (herror : settled.error.isSome = true) :
    (if Blanc.Frame.settlementCommits f raw = true then
      Exec.flowActions dp ca child
     else []) = [] := by
  have hframeSettle : f.settle raw = .ok settled := by
    unfold Frame.settle Frame.settleMsg
    simpa only [hcreate, ↓reduceIte] using hsettled
  have hnot : Blanc.Frame.settlementCommits f raw ≠ true := by
    intro hcommit
    unfold Blanc.Frame.settlementCommits at hcommit
    rw [hframeSettle] at hcommit
    cases hoption : settled.error with
    | none => simp [hoption] at herror
    | some error => simp [hoption] at hcommit
  simp only [if_neg hnot]

/-- Executable observations for one root derivation, in enclosing-frame then
depth-first child order.  Classification proofs later show that this includes
every and only committed balance-writing WETH10 invocation. -/
def Exec.flowObservations (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List FlowObservation :=
  (Exec.flowActions dp ca run).map FlowAction.observation
/-! ## Contract-neutral retained-trace compatibility

The carriers and replay proofs are owned by `Blanc.ExecutionTrace`.  These
aliases preserve the established WETH10 type, helper, and existence-theorem
surface used by repository consumers while the observation folds below remain
contract-local.  Generated constructor/projection declarations belong to the
shared types; ordinary pattern matching and field notation remain unchanged. -/

abbrev RetainedXlot := ExecutionTrace.RetainedXlot

namespace RetainedXlot

abbrev none : Blanc.Weth10.RetainedXlot .none :=
  ExecutionTrace.RetainedXlot.none
abbrev some {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    Blanc.Weth10.RetainedXlot (.some ⟨⟨pc, sevm, pre⟩, out⟩) :=
  ExecutionTrace.RetainedXlot.some run

theorem toFilled {xl : Xlot} :
    Blanc.Weth10.RetainedXlot xl → xl.Filled :=
  ExecutionTrace.RetainedXlot.toFilled

end RetainedXlot

abbrev ProcessMessageTrace := ExecutionTrace.ProcessMessageTrace
abbrev ProcessCreateMessageTrace := ExecutionTrace.ProcessCreateMessageTrace
abbrev MessageCallTrace := ExecutionTrace.MessageCallTrace
abbrev TransactionTrace := ExecutionTrace.TransactionTrace
abbrev ApplyTransactionsTrace := ExecutionTrace.ApplyTransactionsTrace
abbrev SystemMessageTrace := ExecutionTrace.SystemMessageTrace
abbrev RequestsTrace := ExecutionTrace.RequestsTrace
abbrev AppliedBodyTrace := ExecutionTrace.AppliedBodyTrace

theorem exists_retainedXlot_of_filled {xl : Xlot}
    (h : xl.Filled) : Nonempty (RetainedXlot xl) :=
  ExecutionTrace.exists_retainedXlot_of_filled h

theorem exists_processMessageTrace
    (msg : Msg) (out : Except (EvmError × State × AdrSet × Tra) Devm)
    (h : processMessage msg = out) :
    Nonempty (ProcessMessageTrace msg out) :=
  ExecutionTrace.exists_processMessageTrace msg out h

theorem exists_processCreateMessageTrace
    (msg : Msg) (out : Except (EvmError × State × AdrSet × Tra) Devm)
    (h : processCreateMessage msg = out) :
    Nonempty (ProcessCreateMessageTrace msg out) :=
  ExecutionTrace.exists_processCreateMessageTrace msg out h

theorem exists_messageCallTrace {msg : Msg} {state : State}
    {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨state, out⟩) :
    Nonempty (MessageCallTrace msg state out) :=
  ExecutionTrace.exists_messageCallTrace h

theorem exists_transactionTrace
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (h : processTransaction benv bout tx index = .ok (state, bout')) :
    Nonempty (TransactionTrace benv bout tx index state bout') :=
  ExecutionTrace.exists_transactionTrace h

theorem exists_applyTransactionsTrace
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (h : applyTransactions txs benv bout = .ok (finalBenv, finalBout)) :
    Nonempty (ApplyTransactionsTrace txs benv bout finalBenv finalBout) :=
  ExecutionTrace.exists_applyTransactionsTrace h

theorem exists_systemMessageTrace
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (h : processUncheckedSystemTransaction benv target data =
      .ok (state, out)) :
    Nonempty (SystemMessageTrace benv target data state out) :=
  ExecutionTrace.exists_systemMessageTrace h

theorem exists_requestsTrace
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (h : processGeneralPurposeRequests benv bout = .ok (state, bout')) :
    Nonempty (RequestsTrace benv bout state bout') :=
  ExecutionTrace.exists_requestsTrace h

theorem exists_appliedBodyTrace
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (h : applyBody benv txs wds = .ok (state, bout)) :
    Nonempty (AppliedBodyTrace benv txs wds state bout) :=
  ExecutionTrace.exists_appliedBodyTrace h

def RetainedXlot.flowActions (dp : DeployParams) (ca : Adr)
    {xl : Xlot} : RetainedXlot xl → List FlowAction
  | .none => []
  | .some run => Blanc.Weth10.Exec.flowActions dp ca run

def RetainedXlot.flowObservations (dp : DeployParams) (ca : Adr)
    {xl : Xlot} : RetainedXlot xl → List FlowObservation
  | retained =>
      (Blanc.Weth10.RetainedXlot.flowActions dp ca retained).map
        FlowAction.observation

def MessageCallTrace.flowActions (dp : DeployParams) (ca : Adr)
    {msg : Msg} {state : State} {out : MsgCallOutput} :
    MessageCallTrace msg state out → List FlowAction
  | .createCollision .. => []
  | .createRun _ _ evm _ trace _ =>
      if evm.error.isSome then []
      else Blanc.Weth10.RetainedXlot.flowActions dp ca trace.retained
  | .callRun _ _ _ _ _ _ _ _ trace _ =>
      Blanc.Weth10.RetainedXlot.flowActions dp ca trace.retained

def MessageCallTrace.flowObservations (dp : DeployParams) (ca : Adr)
    {msg : Msg} {state : State} {out : MsgCallOutput} :
    MessageCallTrace msg state out → List FlowObservation
  | trace =>
      (Blanc.Weth10.MessageCallTrace.flowActions dp ca trace).map
        FlowAction.observation


def TransactionTrace.flowActions (dp : DeployParams) (ca : Adr)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    List FlowAction :=
  Blanc.Weth10.MessageCallTrace.flowActions dp ca trace.message

def TransactionTrace.flowObservations (dp : DeployParams) (ca : Adr)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    List FlowObservation :=
  (Blanc.Weth10.TransactionTrace.flowActions dp ca trace).map
    FlowAction.observation


def ApplyTransactionsTrace.flowActions (dp : DeployParams) (ca : Adr) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    ApplyTransactionsTrace txs benv bout finalBenv finalBout →
      List FlowAction
  | _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, .cons head tail =>
      Blanc.Weth10.TransactionTrace.flowActions dp ca head ++
        Blanc.Weth10.ApplyTransactionsTrace.flowActions dp ca tail

def ApplyTransactionsTrace.flowObservations (dp : DeployParams) (ca : Adr) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    ApplyTransactionsTrace txs benv bout finalBenv finalBout →
      List FlowObservation
  | _, _, _, _, _, trace =>
      (Blanc.Weth10.ApplyTransactionsTrace.flowActions dp ca trace).map
        FlowAction.observation

def SystemMessageTrace.flowActions (dp : DeployParams) (ca : Adr)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    List FlowAction :=
  Blanc.Weth10.MessageCallTrace.flowActions dp ca trace.message

def SystemMessageTrace.flowObservations (dp : DeployParams) (ca : Adr)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    List FlowObservation :=
  (Blanc.Weth10.SystemMessageTrace.flowActions dp ca trace).map
    FlowAction.observation


def RequestsTrace.flowActions (dp : DeployParams) (ca : Adr)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') : List FlowAction :=
  Blanc.Weth10.SystemMessageTrace.flowActions dp ca trace.withdrawal ++
    Blanc.Weth10.SystemMessageTrace.flowActions dp ca trace.consolidation

def RequestsTrace.flowObservations (dp : DeployParams) (ca : Adr)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') : List FlowObservation :=
  (Blanc.Weth10.RequestsTrace.flowActions dp ca trace).map
    FlowAction.observation


def AppliedBodyTrace.flowActions (dp : DeployParams) (ca : Adr)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) :
    List FlowAction :=
  Blanc.Weth10.SystemMessageTrace.flowActions dp ca trace.beacon ++
    Blanc.Weth10.SystemMessageTrace.flowActions dp ca trace.history ++
    Blanc.Weth10.ApplyTransactionsTrace.flowActions dp ca
      trace.transactions ++
    Blanc.Weth10.RequestsTrace.flowActions dp ca trace.requests

def AppliedBodyTrace.flowObservations (dp : DeployParams) (ca : Adr)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) :
    List FlowObservation :=
  (Blanc.Weth10.AppliedBodyTrace.flowActions dp ca trace).map
    FlowAction.observation

/-! ## Full applied-block history -/

/-- One configured transition together with the selected rules, body output,
and every retained message execution that produced it. -/
structure AccountedBlock
    (cfg : ChainConfig) (dp : DeployParams) (ca : Adr)
    (pre post : BlockChain) : Type where
  block : Block
  bound : sum pre.state.bal + wdsum block.wds < 2 ^ 256
  rules : ForkRules
  rulesAt : cfg.rulesAt block.header.timestamp = .ok rules
  transition : stateTransitionUsing cfg pre block = .ok post
  bodyState : State
  blockOutput : BlockOutput
  bodyRun : applyBody (initBenv rules pre block.header)
    block.txs block.wds = .ok (bodyState, blockOutput)
  bodyTrace : AppliedBodyTrace
    (initBenv rules pre block.header)
    block.txs block.wds bodyState blockOutput
  actions : List FlowAction
  actions_eq : actions =
    Blanc.Weth10.AppliedBodyTrace.flowActions dp ca bodyTrace
  observations : List FlowObservation
  observations_eq : observations =
    Blanc.Weth10.AppliedBodyTrace.flowObservations dp ca bodyTrace
  postEq : post = ⟨appendBlock pre.blocks block, bodyState, pre.chainId⟩

/-- Forgetting WETH10's deterministic ledgers recovers the common configured
block trace literally, without rebuilding any execution evidence. -/
def AccountedBlock.toConfiguredBlockTrace
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (accounted : AccountedBlock cfg dp ca pre post) :
    ExecutionTrace.ConfiguredBlockTrace cfg pre post := {
  block := accounted.block
  bound := accounted.bound
  rules := accounted.rules
  rulesAt := accounted.rulesAt
  transition := accounted.transition
  bodyState := accounted.bodyState
  blockOutput := accounted.blockOutput
  bodyRun := accounted.bodyRun
  bodyTrace := accounted.bodyTrace
  postEq := accounted.postEq
}

/-- Enrich a common configured block trace with the deterministic WETH10
action and observation ledgers computed from its retained body trace. -/
def AccountedBlock.ofConfiguredBlockTrace
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (trace : ExecutionTrace.ConfiguredBlockTrace cfg pre post) :
    AccountedBlock cfg dp ca pre post := {
  block := trace.block
  bound := trace.bound
  rules := trace.rules
  rulesAt := trace.rulesAt
  transition := trace.transition
  bodyState := trace.bodyState
  blockOutput := trace.blockOutput
  bodyRun := trace.bodyRun
  bodyTrace := trace.bodyTrace
  actions := Blanc.Weth10.AppliedBodyTrace.flowActions dp ca trace.bodyTrace
  actions_eq := rfl
  observations :=
    Blanc.Weth10.AppliedBodyTrace.flowObservations dp ca trace.bodyTrace
  observations_eq := rfl
  postEq := trace.postEq
}

theorem AccountedBlock.toConfiguredBlockTrace_ofConfiguredBlockTrace
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain}
    (trace : ExecutionTrace.ConfiguredBlockTrace cfg pre post) :
    (AccountedBlock.ofConfiguredBlockTrace
      (dp := dp) (ca := ca) trace).toConfiguredBlockTrace = trace := by
  cases trace
  rfl

theorem AccountedBlock.exists_of_transition
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain} {block : Block}
    (bound : sum pre.state.bal + wdsum block.wds < 2 ^ 256)
    (h : stateTransitionUsing cfg pre block = .ok post) :
    Nonempty (AccountedBlock cfg dp ca pre post) := by
  rcases ExecutionTrace.exists_configuredBlockTrace_of_transition bound h with
    ⟨trace⟩
  exact ⟨AccountedBlock.ofConfiguredBlockTrace
    (dp := dp) (ca := ca) trace⟩

/-- A proof-carrying configured replay from a checkpoint to an endpoint. -/
inductive AccountedHistory
    (cfg : ChainConfig) (dp : DeployParams) (ca : Adr)
    (checkpoint : BlockChain) : BlockChain → Type
  | refl
      (hcfg : cfg.Valid)
      (hctx : checkpoint.ValidContext)
      (hid : cfg.chainId = checkpoint.chainId) :
      AccountedHistory cfg dp ca checkpoint checkpoint
  | step {current future : BlockChain} :
      AccountedHistory cfg dp ca checkpoint current →
      AccountedBlock cfg dp ca current future →
      AccountedHistory cfg dp ca checkpoint future

def AccountedHistory.appliedBlocks
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory cfg dp ca checkpoint future → List Block
  | .refl _ _ _ => []
  | .step prior accounted => prior.appliedBlocks ++ [accounted.block]

def AccountedHistory.flowObservations
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory cfg dp ca checkpoint future → List FlowObservation
  | .refl _ _ _ => []
  | .step prior accounted =>
      prior.flowObservations ++ accounted.observations

/-- The provenance-rich committed action ledger retained for successor
analyses.  The public numeric fold deliberately uses its deterministic
observation projection only. -/
def AccountedHistory.flowActions
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory cfg dp ca checkpoint future → List FlowAction
  | .refl _ _ _ => []
  | .step prior accounted =>
      prior.flowActions ++ accounted.actions

def AccountedHistory.weth10Flow
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future)
    (u : Adr) : HolderFlow u :=
  holderFlowOfObservations history.flowObservations u

/-- Every retained flash atom carries its receiver credit and exact same-word
repayment as one pair, so successful committed pairs cancel numerically before
any conservation reasoning. -/
theorem AccountedHistory.flash_pair_totals_eq
    {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future) :
    (history.weth10Flow u).flashCredit =
      (history.weth10Flow u).flashRepayment :=
  holderFlowOfObservations_flash_eq history.flowObservations u

/-- Forget WETH10's ledgers throughout a configured retained history. -/
def AccountedHistory.toConfiguredHistoryTrace
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory cfg dp ca checkpoint future →
      ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future
  | .refl hcfg hctx hid => .refl hcfg hctx hid
  | .step prior accounted =>
      .step prior.toConfiguredHistoryTrace accounted.toConfiguredBlockTrace

/-- Enrich every block of a common configured history with its deterministic
WETH10 ledgers. -/
def AccountedHistory.ofConfiguredHistoryTrace
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future →
      AccountedHistory cfg dp ca checkpoint future
  | .refl hcfg hctx hid => .refl hcfg hctx hid
  | .step prior block =>
      .step (AccountedHistory.ofConfiguredHistoryTrace
        (dp := dp) (ca := ca) prior)
        (AccountedBlock.ofConfiguredBlockTrace
          (dp := dp) (ca := ca) block)

theorem AccountedHistory.toConfiguredHistoryTrace_ofConfiguredHistoryTrace
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future) :
    (AccountedHistory.ofConfiguredHistoryTrace
      (dp := dp) (ca := ca) history).toConfiguredHistoryTrace = history := by
  induction history with
  | refl => rfl
  | step prior block ih =>
      simp only [AccountedHistory.ofConfiguredHistoryTrace,
        AccountedHistory.toConfiguredHistoryTrace,
        AccountedBlock.toConfiguredBlockTrace_ofConfiguredBlockTrace, ih]

theorem exists_accountedHistory_of_configuredHistoryTrace
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future) :
    Nonempty (AccountedHistory cfg dp ca checkpoint future) :=
  ⟨AccountedHistory.ofConfiguredHistoryTrace
    (dp := dp) (ca := ca) history⟩

theorem AccountedHistory.toReachUsing
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future) :
    BlockChain.ReachUsing cfg checkpoint future :=
  history.toConfiguredHistoryTrace.toReachUsing

theorem exists_accountedHistory_of_reachUsing
    {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (_hstable : Stable dp ca checkpoint.state)
    (h : BlockChain.ReachUsing cfg checkpoint future) :
    Nonempty (AccountedHistory cfg dp ca checkpoint future) := by
  rcases ExecutionTrace.exists_configuredHistoryTrace_of_reachUsing h with
    ⟨history⟩
  exact exists_accountedHistory_of_configuredHistoryTrace
    (dp := dp) (ca := ca) history

end Weth10

end Blanc

/- The shared carrier changes the namespace Lean consults for dot notation.
These contract-owned compatibility abbreviations keep the historical WETH10
fold syntax working without moving a WETH-specific observation into the
contract-neutral trace module. -/
abbrev Blanc.ExecutionTrace.RetainedXlot.flowActions :=
  Blanc.Weth10.RetainedXlot.flowActions
abbrev Blanc.ExecutionTrace.RetainedXlot.flowObservations :=
  Blanc.Weth10.RetainedXlot.flowObservations
abbrev Blanc.ExecutionTrace.MessageCallTrace.flowActions :=
  Blanc.Weth10.MessageCallTrace.flowActions
abbrev Blanc.ExecutionTrace.MessageCallTrace.flowObservations :=
  Blanc.Weth10.MessageCallTrace.flowObservations
abbrev Blanc.ExecutionTrace.TransactionTrace.flowActions :=
  Blanc.Weth10.TransactionTrace.flowActions
abbrev Blanc.ExecutionTrace.TransactionTrace.flowObservations :=
  Blanc.Weth10.TransactionTrace.flowObservations
abbrev Blanc.ExecutionTrace.ApplyTransactionsTrace.flowActions :=
  Blanc.Weth10.ApplyTransactionsTrace.flowActions
abbrev Blanc.ExecutionTrace.ApplyTransactionsTrace.flowObservations :=
  Blanc.Weth10.ApplyTransactionsTrace.flowObservations
abbrev Blanc.ExecutionTrace.SystemMessageTrace.flowActions :=
  Blanc.Weth10.SystemMessageTrace.flowActions
abbrev Blanc.ExecutionTrace.SystemMessageTrace.flowObservations :=
  Blanc.Weth10.SystemMessageTrace.flowObservations
abbrev Blanc.ExecutionTrace.RequestsTrace.flowActions :=
  Blanc.Weth10.RequestsTrace.flowActions
abbrev Blanc.ExecutionTrace.RequestsTrace.flowObservations :=
  Blanc.Weth10.RequestsTrace.flowObservations
abbrev Blanc.ExecutionTrace.AppliedBodyTrace.flowActions :=
  Blanc.Weth10.AppliedBodyTrace.flowActions
abbrev Blanc.ExecutionTrace.AppliedBodyTrace.flowObservations :=
  Blanc.Weth10.AppliedBodyTrace.flowObservations
