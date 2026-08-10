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

/-- Whether an execution outcome commits its frame state. -/
def Execution.commits : Execution → Bool
  | .error _ => false
  | .ok post => post.error.isNone

/-- Whether the child world survives the complete message-frame settlement.
For CREATE this is strictly stronger than raw execution success: code-deposit
failure rolls the constructor world back before the parent resumes. -/
def Frame.settlementCommits (frame : Frame) (raw : Execution) : Bool :=
  match frame.settle raw with
  | .error _ => false
  | .ok post => post.error.isNone

private theorem execution_commits_of_handleError_clean
    {raw : Execution} {post : Devm}
    (hresult : executeCode.handleError raw = .ok post)
    (hclean : post.error.isNone = true) :
    Execution.commits raw = true := by
  cases raw with
  | ok rawPost =>
      simp only [executeCode.handleError, Except.ok.injEq] at hresult
      subst post
      exact hclean
  | error error =>
      rcases error with ⟨error, rawPost⟩
      cases error <;>
        simp [executeCode.handleError, Devm.withError,
          Devm.setMeta] at hresult
      all_goals subst post
      all_goals change (some _).isNone = true at hclean
      all_goals simp at hclean

private theorem processMessage_clean_input
    {msg : Msg}
    {input : Except (EvmError × State × AdrSet × Tra) Devm}
    {post : Devm}
    (hresult : processMessage.settle msg input = .ok post)
    (hclean : post.error.isNone = true) :
    ∃ pre : Devm, input = .ok pre ∧ pre.error.isNone = true := by
  cases input with
  | error error => simp [processMessage.settle] at hresult
  | ok pre =>
      cases herror : pre.error with
      | none => exact ⟨pre, rfl, by simp [herror]⟩
      | some error =>
          simp [processMessage.settle, herror] at hresult
          rw [← hresult] at hclean
          change pre.error.isNone = true at hclean
          rw [herror] at hclean
          simp at hclean

private theorem processCreateMessage_clean_input
    {msg : Msg}
    {input : Except (EvmError × State × AdrSet × Tra) Devm}
    {post : Devm}
    (hresult : processCreateMessage.settle msg input = .ok post)
    (hclean : post.error.isNone = true) :
    ∃ pre : Devm, input = .ok pre ∧ pre.error.isNone = true := by
  cases input with
  | error error => simp [processCreateMessage.settle] at hresult
  | ok pre =>
      cases herror : pre.error with
      | none => exact ⟨pre, rfl, by simp [herror]⟩
      | some error =>
          simp [processCreateMessage.settle, herror] at hresult
          rw [← hresult] at hclean
          change pre.error.isNone = true at hclean
          rw [herror] at hclean
          simp at hclean

/-- Complete frame settlement can be clean only when the underlying code
execution itself was clean. -/
theorem Frame.raw_commits_of_settlementCommits
    {frame : Frame} {raw : Execution}
    (h : Blanc.Weth10.Frame.settlementCommits frame raw = true) :
    Execution.commits raw = true := by
  unfold Frame.settlementCommits at h
  cases hsettled : frame.settle raw with
  | error error => simp [hsettled] at h
  | ok settled =>
      have hclean : settled.error.isNone = true := by
        simpa only [hsettled] using h
      unfold Frame.settle Frame.settleMsg at hsettled
      cases hcreate : frame.isCreate with
      | false =>
          simp only [hcreate, Bool.false_eq_true, ↓reduceIte] at hsettled
          rcases processMessage_clean_input hsettled hclean with
            ⟨handled, hhandled, hhandledClean⟩
          exact execution_commits_of_handleError_clean hhandled hhandledClean
      | true =>
          simp only [hcreate, ↓reduceIte] at hsettled
          rcases processCreateMessage_clean_input hsettled hclean with
            ⟨inner, hinner, hinnerClean⟩
          rcases processMessage_clean_input hinner hinnerClean with
            ⟨handled, hhandled, hhandledClean⟩
          exact execution_commits_of_handleError_clean hhandled hhandledClean

/-- The concrete outcome indexed by an `Exec` derivation. -/
def Exec.outcome {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (_ : Exec pc sevm pre out) : Execution := out

/-- A retained successful execution frame.  Keeping the full derivation makes
the history suitable for later provenance refinements, rather than merely
retaining a precomputed numeric tally. -/
structure Exec.Frame where
  pc : Nat
  sevm : Sevm
  pre : Devm
  out : Execution
  run : Exec pc sevm pre out
  committed : Execution.commits out = true

/-- The committed post-machine indexed by a retained frame. -/
def Execution.committedPost (out : Execution)
    (h : Execution.commits out = true) : Devm :=
  match out with
  | .ok post => post
  | .error _ => by simp [Execution.commits] at h

def Exec.Frame.post (frame : Exec.Frame) : Devm :=
  Execution.committedPost frame.out frame.committed

def Exec.Frame.ofRun {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) : Exec.Frame :=
  ⟨pc, sevm, pre, out, run, committed⟩

/-- Successful descendant frames whose effects survive in the enclosing
successful frame.  Failed children are discarded, while successful children
are traversed to arbitrary depth. -/
def Exec.descendantFrames {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Frame :=
  match run with
  | .halt _ => []
  | .cont _ next => Exec.descendantFrames next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next => Exec.descendantFrames next
  | .runErr _ _ _ _ => []
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      let childFrames :=
        if h : Blanc.Weth10.Frame.settlementCommits frame raw = true then
          let hraw : Execution.commits raw = true :=
            Blanc.Weth10.Frame.raw_commits_of_settlementCommits h
          Exec.Frame.ofRun child hraw :: Exec.descendantFrames child
        else []
      childFrames ++ Exec.descendantFrames next
termination_by sizeOf run

/-- A spawned child whose complete frame settlement does not commit contributes
no retained frame, even if its raw execution itself committed. -/
@[simp] theorem Exec.descendantFrames_runOk_of_not_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {f : Jaune.Frame} {rsm : Resume}
    {cevm : Evm} {raw out : Execution}
    (hstep : Jaune.Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (hnot : Blanc.Weth10.Frame.settlementCommits f raw ≠ true) :
    Exec.descendantFrames (Exec.runOk hstep henter child hr next) =
      Exec.descendantFrames next := by
  simp only [Exec.descendantFrames, dif_neg hnot, List.nil_append]

/-- In particular, a CREATE child whose raw execution commits but whose
code-deposit settlement rolls back contributes no descendant frame.  The raw
commit premise records the semantic counterexample to pruning by raw outcome
alone. -/
theorem Exec.descendantFrames_runOk_create_codeDepositRollback
    {pc pc' : Nat} {sevm : Sevm} {pre devm' settled : Devm}
    {f : Jaune.Frame} {rsm : Resume}
    {cevm : Evm} {raw out : Execution}
    (hstep : Jaune.Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (_rawCommits : Execution.commits raw = true)
    (hcreate : f.isCreate = true)
    (hsettled : processCreateMessage.settle f.outer
      (processMessage.settle f.inner (executeCode.handleError raw)) =
        .ok settled)
    (herror : settled.error.isSome = true) :
    Exec.descendantFrames (Exec.runOk hstep henter child hr next) =
      Exec.descendantFrames next := by
  apply Exec.descendantFrames_runOk_of_not_settlementCommits
    hstep henter child hr next
  intro hcommit
  have hframeSettle : f.settle raw = .ok settled := by
    unfold Frame.settle Frame.settleMsg
    simpa only [hcreate, ↓reduceIte] using hsettled
  unfold Blanc.Weth10.Frame.settlementCommits at hcommit
  rw [hframeSettle] at hcommit
  cases hoption : settled.error with
  | none => simp [hoption] at herror
  | some error => simp [hoption] at hcommit

/-- All and only committed frames in a successful root execution.  An errored
root contributes no frames, so a later enclosing rollback cannot leak actions
into the accounting fold. -/
def Exec.committedFrames {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Frame :=
  if h : Execution.commits out = true then
    Exec.Frame.ofRun run h :: Exec.descendantFrames run
  else []

/-- Deterministic candidate observation for a retained frame.  The exact
target/code context rejects foreign lookalikes and library-style execution;
the committed-frame traversal supplies the settlement boundary. -/
def Exec.Frame.exactInvocation (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) : Prop :=
  frame.pc = 0 ∧ Blanc.Weth10.exactInvocation dp ca frame.sevm

instance (dp : DeployParams) (ca : Adr) (frame : Exec.Frame) :
    Decidable (frame.exactInvocation dp ca) := by
  unfold Exec.Frame.exactInvocation
  infer_instance

def Exec.Frame.flowAction? (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) : Option FlowAction :=
  if frame.exactInvocation dp ca then
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
  (frame.flowAction? dp ca).map FlowAction.observation

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
    (if Blanc.Weth10.Frame.settlementCommits f raw = true then
      Exec.flowActions dp ca child
     else []) = [] := by
  have hframeSettle : f.settle raw = .ok settled := by
    unfold Frame.settle Frame.settleMsg
    simpa only [hcreate, ↓reduceIte] using hsettled
  have hnot : Blanc.Weth10.Frame.settlementCommits f raw ≠ true := by
    intro hcommit
    unfold Blanc.Weth10.Frame.settlementCommits at hcommit
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

/-- A Type-valued version of a filled recursive execution slot.  Unlike
`Xlot.Filled`, this retains the concrete `Exec` value that the accounting fold
and its successor provenance analysis consume. -/
inductive RetainedXlot : Xlot → Type
  | none : RetainedXlot .none
  | some {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
      (run : Exec pc sevm pre out) :
      RetainedXlot (.some ⟨⟨pc, sevm, pre⟩, out⟩)

theorem RetainedXlot.toFilled {xl : Xlot} : RetainedXlot xl → xl.Filled
  | .none => trivial
  | .some run => ⟨run⟩

theorem exists_retainedXlot_of_filled {xl : Xlot}
    (h : xl.Filled) : Nonempty (RetainedXlot xl) := by
  cases xl with
  | none => exact ⟨.none⟩
  | some slot =>
      rcases slot with ⟨evm, out⟩
      rcases h with ⟨run⟩
      exact ⟨.some run⟩

def RetainedXlot.flowActions (dp : DeployParams) (ca : Adr)
    {xl : Xlot} : RetainedXlot xl → List FlowAction
  | .none => []
  | .some run => Blanc.Weth10.Exec.flowActions dp ca run

def RetainedXlot.flowObservations (dp : DeployParams) (ca : Adr)
    {xl : Xlot} : RetainedXlot xl → List FlowObservation
  | retained => (retained.flowActions dp ca).map FlowAction.observation

/-- An exact retained execution of Jaune's raw call-message core. -/
structure ProcessMessageTrace (msg : Msg)
    (out : Except (EvmError × State × AdrSet × Tra) Devm) where
  slot : Xlot
  retained : RetainedXlot slot
  run : ProcessMessage msg slot out

theorem exists_processMessageTrace
    (msg : Msg) (out : Except (EvmError × State × AdrSet × Tra) Devm)
    (h : processMessage msg = out) :
    Nonempty (ProcessMessageTrace msg out) := by
  obtain ⟨xl, hfilled, hrun⟩ := of_processMessage msg out h
  rcases exists_retainedXlot_of_filled hfilled with ⟨retained⟩
  exact ⟨⟨xl, retained, hrun⟩⟩

/-- An exact retained execution of Jaune's raw create-message core. -/
structure ProcessCreateMessageTrace (msg : Msg)
    (out : Except (EvmError × State × AdrSet × Tra) Devm) where
  slot : Xlot
  retained : RetainedXlot slot
  run : ProcessCreateMessage msg slot out

theorem exists_processCreateMessageTrace
    (msg : Msg) (out : Except (EvmError × State × AdrSet × Tra) Devm)
    (h : processCreateMessage msg = out) :
    Nonempty (ProcessCreateMessageTrace msg out) := by
  obtain ⟨xl, hfilled, hrun⟩ := of_processCreateMessage msg out h
  rcases exists_retainedXlot_of_filled hfilled with ⟨retained⟩
  exact ⟨⟨xl, retained, hrun⟩⟩

/-- The collision test used by the create arm of `processMessageCall`. -/
def messageCreateCollision (msg : Msg) : Bool :=
  accountHasCodeOrNonce msg.benv.state msg.currentTarget ||
    accountHasStorage msg.benv.state msg.currentTarget

/-- The exact EIP-7702 preparation prefix used by the call arm. -/
def messageCallDelegation (msg : Msg) : Except EvmError (Msg × Nat) :=
  if msg.tenv.stat.auths.isEmpty then
    .ok ⟨msg, 0⟩
  else do
    let ⟨delegated, refund⟩ ← setDelegation msg
    .ok ⟨delegated, refund.toNat⟩

/-- The actual message executed after resolving an EIP-7702 code delegation. -/
def messageCallExecutionMessage (msg : Msg) : Msg :=
  match getDelegatedCodeAddress msg.code with
  | none => msg
  | some dca =>
      { msg with
        disablePrecompiles := true
        accessedAddresses := msg.accessedAddresses.insert dca
        code := msg.benv.state.getCode dca
        codeAddress := some dca }

/-- Proof-carrying trace of Jaune's settled message-call wrapper.  The three
constructors match its collision, create-execution, and call-execution arms;
the retained core is tied to the exact deterministic wrapper result. -/
inductive MessageCallTrace (msg : Msg) (state : State)
    (out : MsgCallOutput) : Type
  | createCollision
      (h_target : msg.target.isNone = true)
      (h_collision : messageCreateCollision msg = true)
      (h_result : processMessageCall msg = .ok ⟨state, out⟩) :
      MessageCallTrace msg state out
  | createRun
      (h_target : msg.target.isNone = true)
      (h_collision : messageCreateCollision msg = false)
      (evm : Devm)
      (h_core : processCreateMessage msg = .ok evm)
      (trace : ProcessCreateMessageTrace msg (.ok evm))
      (h_result : processMessageCall msg = .ok ⟨state, out⟩) :
      MessageCallTrace msg state out
  | callRun
      (h_target : msg.target.isNone = false)
      (delegated : Msg) (refund : Nat)
      (h_delegation : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
      (execMsg : Msg)
      (h_execMsg : execMsg = messageCallExecutionMessage delegated)
      (evm : Devm)
      (h_core : processMessage execMsg = .ok evm)
      (trace : ProcessMessageTrace execMsg (.ok evm))
      (h_result : processMessageCall msg = .ok ⟨state, out⟩) :
      MessageCallTrace msg state out

def MessageCallTrace.flowActions (dp : DeployParams) (ca : Adr)
    {msg : Msg} {state : State} {out : MsgCallOutput} :
    MessageCallTrace msg state out → List FlowAction
  | .createCollision .. => []
  | .createRun _ _ evm _ trace _ =>
      if evm.error.isSome then []
      else trace.retained.flowActions dp ca
  | .callRun _ _ _ _ _ _ _ _ trace _ =>
      trace.retained.flowActions dp ca

def MessageCallTrace.flowObservations (dp : DeployParams) (ca : Adr)
    {msg : Msg} {state : State} {out : MsgCallOutput} :
    MessageCallTrace msg state out → List FlowObservation
  | trace => (trace.flowActions dp ca).map FlowAction.observation

/-- Every successful settled message-call wrapper admits a retained trace of
the exact raw execution core it ran. -/
theorem exists_messageCallTrace {msg : Msg} {state : State}
    {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨state, out⟩) :
    Nonempty (MessageCallTrace msg state out) := by
  have h_result := h
  unfold processMessageCall at h
  split at h
  · rename_i htarget
    unfold processMessageCall.create at h
    dsimp only at h
    split at h
    · rename_i hcollision
      exact ⟨.createCollision htarget (by
        simpa [messageCreateCollision] using hcollision) h_result⟩
    · rename_i hcollision
      obtain ⟨evm, hevm, _⟩ := Except.bind_eq_ok h
      have hcore := Except.bimap_id_eq_ok hevm
      rcases exists_processCreateMessageTrace msg (.ok evm) hcore with
        ⟨trace⟩
      exact ⟨.createRun htarget (by
        simpa [messageCreateCollision] using hcollision)
        evm hcore trace h_result⟩
  · rename_i htarget
    have htargetFalse : msg.target.isNone = false := by
      cases ht : msg.target.isNone <;> simp_all
    unfold processMessageCall.call at h
    split at h
    · rename_i hauth
      obtain ⟨x0, hx0, h⟩ := Except.bind_eq_ok h
      cases hx0
      dsimp only at h
      split at h
      · rename_i hcode
        obtain ⟨evm, hevm, _⟩ := Except.bind_eq_ok h
        have hcore0 := Except.bimap_id_eq_ok hevm
        have hcore :
            processMessage (messageCallExecutionMessage msg) = .ok evm := by
          simpa [messageCallExecutionMessage, hcode] using hcore0
        rcases exists_processMessageTrace _ (.ok evm) hcore with ⟨trace⟩
        exact ⟨.callRun htargetFalse msg 0 (by
          simp [messageCallDelegation, hauth])
          (messageCallExecutionMessage msg) rfl evm hcore trace h_result⟩
      · rename_i hcode
        obtain ⟨evm, hevm, _⟩ := Except.bind_eq_ok h
        have hcore0 := Except.bimap_id_eq_ok hevm
        have hcore :
            processMessage (messageCallExecutionMessage msg) = .ok evm := by
          simpa [messageCallExecutionMessage, hcode] using hcore0
        rcases exists_processMessageTrace _ (.ok evm) hcore with ⟨trace⟩
        exact ⟨.callRun htargetFalse msg 0 (by
          simp [messageCallDelegation, hauth])
          (messageCallExecutionMessage msg) rfl evm hcore trace h_result⟩
    · rename_i hauth
      obtain ⟨w, hw, h⟩ := Except.bind_eq_ok h
      obtain ⟨delegated, refundWord⟩ := w
      obtain ⟨x0, hx0, h⟩ := Except.bind_eq_ok h
      cases hx0
      dsimp only at h
      split at h
      · rename_i hcode
        obtain ⟨evm, hevm, _⟩ := Except.bind_eq_ok h
        have hcore0 := Except.bimap_id_eq_ok hevm
        have hcore : processMessage
            (messageCallExecutionMessage delegated) = .ok evm := by
          simpa [messageCallExecutionMessage, hcode] using hcore0
        rcases exists_processMessageTrace _ (.ok evm) hcore with ⟨trace⟩
        exact ⟨.callRun htargetFalse delegated refundWord.toNat (by
          simp [messageCallDelegation, hauth, hw])
          (messageCallExecutionMessage delegated) rfl evm hcore trace h_result⟩
      · rename_i hcode
        obtain ⟨evm, hevm, _⟩ := Except.bind_eq_ok h
        have hcore0 := Except.bimap_id_eq_ok hevm
        have hcore : processMessage
            (messageCallExecutionMessage delegated) = .ok evm := by
          simpa [messageCallExecutionMessage, hcode] using hcore0
        rcases exists_processMessageTrace _ (.ok evm) hcore with ⟨trace⟩
        exact ⟨.callRun htargetFalse delegated refundWord.toNat (by
          simp [messageCallDelegation, hauth, hw])
          (messageCallExecutionMessage delegated) rfl evm hcore trace h_result⟩

/-! ## Transaction traces -/

def transactionPreludeBout
    (bout : BlockOutput) (tx : Tx) (index : Nat) : BlockOutput :=
  { bout with
    transactionsTrie := bout.transactionsTrie.insert
      (BLT.bytes index.toBytes).toBytes tx }

def transactionBlobGasFee (benv : Benv) (tx : Tx) : Nat :=
  if tx.isTypeThree then
    calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
  else 0

def transactionTenv (benv : Benv) (tx : Tx) (index : Nat)
    (sender : Adr) (effectiveGasPrice intrinsicGas : Nat)
    (blobVersionedHashes : List B256) : Tenv :=
  { transientStorage := .empty
    stat :=
      { origin := sender
        gasPrice := effectiveGasPrice
        gas := tx.gas - intrinsicGas
        accessListAddresses :=
          .ofList (benv.stat.coinbase :: tx.accessList.map Prod.fst)
        accessListStorageKeys :=
          .ofList (tx.accessList.map (fun ⟨adr, keys⟩ =>
            keys.map (⟨adr, ·⟩))).flatten
        blobVersionedHashes := blobVersionedHashes
        auths := tx.auths
        indexInBlock := index
        txHash := getTxHash tx } }

/-- A successful transaction together with the exact prepared message and its
retained recursive execution.  Validation, sender recovery/fee checking,
up-front debit, and message preparation are all replay equations, so an
unrelated or forged message trace cannot inhabit this type. -/
structure TransactionTrace (benv : Benv) (bout : BlockOutput)
    (tx : Tx) (index : Nat) (state : State) (bout' : BlockOutput) where
  intrinsicGas : Nat
  calldataFloorGasCost : Nat
  sender : Adr
  effectiveGasPrice : Nat
  blobVersionedHashes : List B256
  txBlobGasUsed : Nat
  debitState : State
  msg : Msg
  messageState : State
  messageOut : MsgCallOutput
  validation : validateTransaction benv.stat.rules tx =
    .ok (intrinsicGas, calldataFloorGasCost)
  checked : checkTransaction benv.beginTransaction
    (transactionPreludeBout bout tx index) tx =
      .ok (sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed)
  debit : (benv.state.incrNonce sender).subBal sender
    (tx.gas * effectiveGasPrice +
      transactionBlobGasFee benv tx).toB256 = some debitState
  prepared : prepareMessage
    { benv.beginTransaction with state := debitState }
    (transactionTenv benv.beginTransaction tx index sender
      effectiveGasPrice intrinsicGas blobVersionedHashes) tx = .ok msg
  message : MessageCallTrace msg messageState messageOut
  result : processTransaction benv bout tx index = .ok (state, bout')

def TransactionTrace.flowActions (dp : DeployParams) (ca : Adr)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    List FlowAction :=
  trace.message.flowActions dp ca

def TransactionTrace.flowObservations (dp : DeployParams) (ca : Adr)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    List FlowObservation :=
  (trace.flowActions dp ca).map FlowAction.observation

/-- Every successful transaction admits an exact retained message trace. -/
theorem exists_transactionTrace
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (h : processTransaction benv bout tx index = .ok (state, bout')) :
    Nonempty (TransactionTrace benv bout tx index state bout') := by
  have h_result := h
  unfold processTransaction at h
  dsimp only at h
  obtain ⟨prelude, hprelude, h⟩ := Except.bind_eq_ok h
  cases hprelude
  obtain ⟨validated, hvalidated, h⟩ := Except.bind_eq_ok h
  obtain ⟨intrinsicGas, calldataFloorGasCost⟩ := validated
  rw [Except.mapError_eq_ok_iff] at hvalidated
  obtain ⟨checked, hchecked, h⟩ := Except.bind_eq_ok h
  obtain ⟨sender, effectiveGasPrice, blobVersionedHashes,
    txBlobGasUsed⟩ := checked
  obtain ⟨debitState, hdebit, h⟩ := Except.bind_eq_ok h
  have hdebit' := Option.toExcept_eq_ok hdebit
  obtain ⟨msg, hprepared, h⟩ := Except.bind_eq_ok h
  obtain ⟨messageResult, hmessage, _⟩ := Except.bind_eq_ok h
  obtain ⟨messageState, messageOut⟩ := messageResult
  rw [Except.mapError_eq_ok_iff] at hmessage
  rcases exists_messageCallTrace hmessage with ⟨messageTrace⟩
  exact ⟨⟨intrinsicGas, calldataFloorGasCost, sender,
    effectiveGasPrice, blobVersionedHashes, txBlobGasUsed, debitState,
    msg, messageState, messageOut,
    by simpa [Benv.beginTransaction] using hvalidated,
    by simpa [transactionPreludeBout] using hchecked,
    by simpa [transactionBlobGasFee, Benv.beginTransaction] using hdebit',
    by simpa [transactionTenv, Benv.beginTransaction] using hprepared,
    messageTrace, h_result⟩⟩

/-- Exact retained replay of the decoded transaction list. -/
inductive ApplyTransactionsTrace :
    List (Nat × Tx) → Benv → BlockOutput → Benv → BlockOutput → Type
  | nil (benv : Benv) (bout : BlockOutput) :
      ApplyTransactionsTrace [] benv bout benv bout
  | cons {index : Nat} {tx : Tx} {txs : List (Nat × Tx)}
      {benv : Benv} {bout : BlockOutput}
      {txState : State} {txBout : BlockOutput}
      {finalBenv : Benv} {finalBout : BlockOutput}
      (head : TransactionTrace benv bout tx index txState txBout)
      (tail : ApplyTransactionsTrace txs (benv.withState txState) txBout
        finalBenv finalBout) :
      ApplyTransactionsTrace ((index, tx) :: txs) benv bout
        finalBenv finalBout

def ApplyTransactionsTrace.flowActions (dp : DeployParams) (ca : Adr) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    ApplyTransactionsTrace txs benv bout finalBenv finalBout →
      List FlowAction
  | _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, .cons head tail =>
      head.flowActions dp ca ++ tail.flowActions dp ca

def ApplyTransactionsTrace.flowObservations (dp : DeployParams) (ca : Adr) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    ApplyTransactionsTrace txs benv bout finalBenv finalBout →
      List FlowObservation
  | _, _, _, _, _, trace =>
      (trace.flowActions dp ca).map FlowAction.observation

theorem exists_applyTransactionsTrace
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (h : applyTransactions txs benv bout = .ok (finalBenv, finalBout)) :
    Nonempty (ApplyTransactionsTrace txs benv bout finalBenv finalBout) := by
  induction txs generalizing benv bout with
  | nil =>
      simp only [applyTransactions] at h
      cases h
      exact ⟨.nil finalBenv finalBout⟩
  | cons head txs ih =>
      obtain ⟨index, tx⟩ := head
      simp only [applyTransactions] at h
      obtain ⟨txResult, htx, htail⟩ := Except.bind_eq_ok h
      obtain ⟨txState, txBout⟩ := txResult
      rcases exists_transactionTrace htx with ⟨headTrace⟩
      rcases ih htail with ⟨tailTrace⟩
      exact ⟨.cons headTrace tailTrace⟩

/-! ## System-message and body traces -/

def systemTransactionMessage
    (benv : Benv) (target : Adr) (data : Bytes) : Msg :=
  let active := benv.beginTransaction
  processSystemTransactionMsg active (processSystemTransactionTenv active)
    target data (benv.state.getCode target)

/-- Exact retained root for one of Prague's system transactions. -/
structure SystemMessageTrace (benv : Benv) (target : Adr) (data : Bytes)
    (state : State) (out : MsgCallOutput) where
  message : MessageCallTrace
    (systemTransactionMessage benv target data) state out
  run : processUncheckedSystemTransaction benv target data = .ok (state, out)

def SystemMessageTrace.flowActions (dp : DeployParams) (ca : Adr)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    List FlowAction :=
  trace.message.flowActions dp ca

def SystemMessageTrace.flowObservations (dp : DeployParams) (ca : Adr)
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    List FlowObservation :=
  (trace.flowActions dp ca).map FlowAction.observation

theorem exists_systemMessageTrace
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (h : processUncheckedSystemTransaction benv target data =
      .ok (state, out)) :
    Nonempty (SystemMessageTrace benv target data state out) := by
  have hmessage : processMessageCall
      (systemTransactionMessage benv target data) = .ok (state, out) := by
    simpa [processUncheckedSystemTransaction, processSystemTransaction,
      systemTransactionMessage] using h
  rcases exists_messageCallTrace hmessage with ⟨trace⟩
  exact ⟨⟨trace, h⟩⟩

/-- Retained execution evidence for the two checked request-system calls at
the tail of `applyBody`. -/
structure RequestsTrace (benv : Benv) (bout : BlockOutput)
    (state : State) (bout' : BlockOutput) where
  depositRequests : Bytes
  parsed : parseDepositRequests bout = .ok depositRequests
  withdrawalState : State
  withdrawalOut : MsgCallOutput
  withdrawalRun : processCheckedSystemTransaction benv
    withdrawalRequestPredeployAddress [] =
      .ok (withdrawalState, withdrawalOut)
  withdrawal : SystemMessageTrace benv
    withdrawalRequestPredeployAddress [] withdrawalState withdrawalOut
  consolidationState : State
  consolidationOut : MsgCallOutput
  consolidationRun : processCheckedSystemTransaction
    (benv.withState withdrawalState)
    consolidationRequestPredeployAddress [] =
      .ok (consolidationState, consolidationOut)
  consolidation : SystemMessageTrace (benv.withState withdrawalState)
    consolidationRequestPredeployAddress []
    consolidationState consolidationOut
  run : processGeneralPurposeRequests benv bout = .ok (state, bout')

def RequestsTrace.flowActions (dp : DeployParams) (ca : Adr)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') : List FlowAction :=
  trace.withdrawal.flowActions dp ca ++
    trace.consolidation.flowActions dp ca

def RequestsTrace.flowObservations (dp : DeployParams) (ca : Adr)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') : List FlowObservation :=
  (trace.flowActions dp ca).map FlowAction.observation

theorem exists_requestsTrace
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (h : processGeneralPurposeRequests benv bout = .ok (state, bout')) :
    Nonempty (RequestsTrace benv bout state bout') := by
  have h_result := h
  unfold processGeneralPurposeRequests at h
  obtain ⟨deposits, hdeposits, h⟩ := Except.bind_eq_ok h
  dsimp only at h
  split at h <;>
    (obtain ⟨⟨withdrawalState, withdrawalOut⟩, hwithdrawal, h⟩ :=
      Except.bind_eq_ok h
     have hwithdrawal' :=
       processCheckedSystemTransaction_to_unchecked hwithdrawal
     rcases exists_systemMessageTrace hwithdrawal' with ⟨withdrawalTrace⟩
     dsimp only at h
     split at h <;>
       (obtain ⟨⟨consolidationState, consolidationOut⟩,
          hconsolidation, _⟩ := Except.bind_eq_ok h
        have hconsolidation' :=
          processCheckedSystemTransaction_to_unchecked hconsolidation
        rcases exists_systemMessageTrace hconsolidation' with
          ⟨consolidationTrace⟩
        exact ⟨⟨deposits, hdeposits,
          withdrawalState, withdrawalOut, hwithdrawal, withdrawalTrace,
          consolidationState, consolidationOut,
          hconsolidation, consolidationTrace, h_result⟩⟩))

/-- Complete retained execution evidence for a successful Prague block body.
This includes the two pre-transaction system calls, every decoded normal
transaction, and the two checked request-system calls. -/
structure AppliedBodyTrace (benv : Benv) (txs : List (Bytes ⊕ Tx))
    (wds : List Withdrawal) (state : State) (bout : BlockOutput) where
  run : applyBody benv txs wds = .ok (state, bout)
  beaconState : State
  beaconOut : MsgCallOutput
  beacon : SystemMessageTrace benv beaconRootsAddress
    benv.stat.parentBeaconBlockRoot.toBytes beaconState beaconOut
  lastHash : B256
  lastHashRun :
    ((benv.withState beaconState).stat.blockHashes.getLast?).toExcept
      (TransitionError.internal
        (.invariant (.text "block hashes is empty"))) = .ok lastHash
  historyState : State
  historyOut : MsgCallOutput
  history : SystemMessageTrace (benv.withState beaconState)
    historyStorageAddress lastHash.toBytes historyState historyOut
  decodedTxs : List Tx
  decodeRun : txs.mapM decodeTx = .ok decodedTxs
  transactionBenv : Benv
  transactionBout : BlockOutput
  transactions : ApplyTransactionsTrace decodedTxs.putIndex
    ((benv.withState beaconState).withState historyState) .init
    transactionBenv transactionBout
  requests : RequestsTrace
    (transactionBenv.withState
      (processWithdrawalsState transactionBenv.state wds))
    (transactionBout.withWithdrawalsTrie
      (processWithdrawalsTrie transactionBout.withdrawalsTrie wds))
    state bout

def AppliedBodyTrace.flowActions (dp : DeployParams) (ca : Adr)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) :
    List FlowAction :=
  trace.beacon.flowActions dp ca ++
    trace.history.flowActions dp ca ++
    trace.transactions.flowActions dp ca ++
    trace.requests.flowActions dp ca

def AppliedBodyTrace.flowObservations (dp : DeployParams) (ca : Adr)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) :
    List FlowObservation :=
  (trace.flowActions dp ca).map FlowAction.observation

theorem exists_appliedBodyTrace
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (h : applyBody benv txs wds = .ok (state, bout)) :
    Nonempty (AppliedBodyTrace benv txs wds state bout) := by
  have h_result := h
  rw [applyBody] at h
  simp only at h
  rcases Except.bind_eq_ok h with
    ⟨⟨beaconState, beaconOut⟩, hbeacon, h⟩
  rcases Except.bind_eq_ok h with ⟨lastHash, hlastHash, h⟩
  rcases Except.bind_eq_ok h with
    ⟨⟨historyState, historyOut⟩, hhistory, h⟩
  rcases Except.bind_eq_ok h with ⟨decodedTxs, hdecoded, h⟩
  rcases Except.bind_eq_ok h with
    ⟨⟨transactionBenv, transactionBout⟩, htransactions, hrequests⟩
  dsimp only at hhistory htransactions hrequests
  rw [Except.mapError_eq_ok_iff] at hbeacon hhistory
  rcases exists_systemMessageTrace hbeacon with ⟨beaconTrace⟩
  rcases exists_systemMessageTrace hhistory with ⟨historyTrace⟩
  rcases exists_applyTransactionsTrace htransactions with
    ⟨transactionsTrace⟩
  dsimp [processWithdrawals] at hrequests
  rcases exists_requestsTrace hrequests with ⟨requestsTrace⟩
  exact ⟨⟨h_result, beaconState, beaconOut, beaconTrace,
    lastHash, hlastHash, historyState, historyOut, historyTrace,
    decodedTxs, hdecoded, transactionBenv, transactionBout,
    transactionsTrace, requestsTrace⟩⟩

/-! ## Full applied-block history -/

/-- One configured Prague transition together with the body output and every
retained message execution that produced it. -/
structure AccountedBlock
    (chainId : UInt64) (dp : DeployParams) (ca : Adr)
    (pre post : BlockChain) : Type where
  block : Block
  bound : sum pre.state.bal + wdsum block.wds < 2 ^ 256
  transition :
    stateTransitionUsing (ChainConfig.pragueOnly chainId) pre block = .ok post
  bodyState : State
  blockOutput : BlockOutput
  bodyRun : applyBody (initBenv pragueRules pre block.header)
    block.txs block.wds = .ok (bodyState, blockOutput)
  bodyTrace : AppliedBodyTrace
    (initBenv pragueRules pre block.header)
    block.txs block.wds bodyState blockOutput
  actions : List FlowAction
  actions_eq : actions = bodyTrace.flowActions dp ca
  observations : List FlowObservation
  observations_eq : observations = bodyTrace.flowObservations dp ca
  postEq : post = ⟨appendBlock pre.blocks block, bodyState, pre.chainId⟩

theorem AccountedBlock.exists_of_transition
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {pre post : BlockChain} {block : Block}
    (bound : sum pre.state.bal + wdsum block.wds < 2 ^ 256)
    (h : stateTransitionUsing (ChainConfig.pragueOnly chainId) pre block =
      .ok post) :
    Nonempty (AccountedBlock chainId dp ca pre post) := by
  have hId : (ChainConfig.pragueOnly chainId).chainId = pre.chainId :=
    stateTransitionUsing_success_chainId_eq h
  have hWith := h
  rw [stateTransitionUsing_eq_of_chainId_eq hId] at hWith
  simp only [ChainConfig.pragueOnly_rulesAt, Except.mapError,
    Except.bind] at hWith
  rw [stateTransitionWith_eq_ok_iff, stateTransitionE] at hWith
  obtain ⟨_, _, hWith⟩ := Except.bind_eq_ok hWith
  obtain ⟨_, _, hWith⟩ := Except.bind_eq_ok hWith
  dsimp only at hWith
  obtain ⟨⟨bodyState, blockOutput⟩, hBody, hWith⟩ :=
    Except.bind_eq_ok hWith
  dsimp only at hWith
  obtain ⟨_, _, hFinal⟩ := Except.bind_eq_ok hWith
  rcases exists_appliedBodyTrace hBody with ⟨bodyTrace⟩
  exact ⟨{
    block := block
    bound := bound
    transition := h
    bodyState := bodyState
    blockOutput := blockOutput
    bodyRun := hBody
    bodyTrace := bodyTrace
    actions := bodyTrace.flowActions dp ca
    actions_eq := rfl
    observations := bodyTrace.flowObservations dp ca
    observations_eq := rfl
    postEq := (Except.ok.inj hFinal).symm
  }⟩

/-- A proof-carrying Prague-only replay from a checkpoint to an endpoint. -/
inductive AccountedHistory
    (chainId : UInt64) (dp : DeployParams) (ca : Adr)
    (checkpoint : BlockChain) : BlockChain → Type
  | refl
      (hcfg : (ChainConfig.pragueOnly chainId).Valid)
      (hctx : checkpoint.ValidContext)
      (hid : chainId = checkpoint.chainId) :
      AccountedHistory chainId dp ca checkpoint checkpoint
  | step {current future : BlockChain} :
      AccountedHistory chainId dp ca checkpoint current →
      AccountedBlock chainId dp ca current future →
      AccountedHistory chainId dp ca checkpoint future

def AccountedHistory.appliedBlocks
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory chainId dp ca checkpoint future → List Block
  | .refl _ _ _ => []
  | .step prior accounted => prior.appliedBlocks ++ [accounted.block]

def AccountedHistory.flowObservations
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory chainId dp ca checkpoint future → List FlowObservation
  | .refl _ _ _ => []
  | .step prior accounted =>
      prior.flowObservations ++ accounted.observations

/-- The provenance-rich committed action ledger retained for successor
analyses.  The public numeric fold deliberately uses its deterministic
observation projection only. -/
def AccountedHistory.flowActions
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory chainId dp ca checkpoint future → List FlowAction
  | .refl _ _ _ => []
  | .step prior accounted =>
      prior.flowActions ++ accounted.actions

def AccountedHistory.weth10Flow
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future)
    (u : Adr) : HolderFlow u :=
  holderFlowOfObservations history.flowObservations u

/-- Every retained flash atom carries its receiver credit and exact same-word
repayment as one pair, so successful committed pairs cancel numerically before
any conservation reasoning. -/
theorem AccountedHistory.flash_pair_totals_eq
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) :
    (history.weth10Flow u).flashCredit =
      (history.weth10Flow u).flashRepayment :=
  holderFlowOfObservations_flash_eq history.flowObservations u

theorem AccountedHistory.toReachUsing
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) :
    BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      checkpoint future := by
  induction history with
  | refl hcfg hctx hid =>
      exact .refl checkpoint hcfg hctx hid
  | step prior accounted ih =>
      exact .step ih accounted.bound accounted.transition

theorem exists_accountedHistory_of_reachUsing
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (_hstable : Stable dp ca checkpoint.state)
    (h : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) checkpoint future) :
    Nonempty (AccountedHistory chainId dp ca checkpoint future) := by
  induction h with
  | refl hcfg hctx hid =>
      exact ⟨.refl hcfg hctx hid⟩
  | step prior bound transition ih =>
      rcases ih with ⟨history⟩
      rcases AccountedBlock.exists_of_transition
        (dp := dp) (ca := ca) bound transition with ⟨block⟩
      exact ⟨.step history block⟩

end Weth10

end Blanc
