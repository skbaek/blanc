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

/-- Flow data plus the actual invocation context.  Authenticity proofs later
pin `currentTarget`, `codeAddress`, code, storage writes, and the associated
WETH-emitter log to the retained execution. -/
structure FlowAction where
  atom : FlowAtom
  debit : Option DebitProvenance
  actualCaller : Adr
  currentTarget : Adr
  codeAddress : Option Adr
  depth : Nat
deriving DecidableEq

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

/-- The public numeric fold used by `AccountedHistory.weth10Flow`. -/
def holderFlowOfActions (actions : List FlowAction) (u : Adr) : HolderFlow u :=
  actions.foldl (fun total action =>
    total.add (action.atom.holderFlow u)) (HolderFlow.zero u)

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

def holderFlowOfObservations (observations : List FlowObservation)
    (u : Adr) : HolderFlow u :=
  observations.foldl (fun total observation =>
    total.add (observation.atom.holderFlow u)) (HolderFlow.zero u)

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

/-- Whether an execution outcome commits its frame state. -/
def Execution.commits : Execution → Bool
  | .error _ => false
  | .ok post => post.error.isNone

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
  | .runOk _ _ child _ next =>
      let childFrames :=
        if h : Execution.commits (Blanc.Weth10.Exec.outcome child) = true then
          Exec.Frame.ofRun child h :: Exec.descendantFrames child
        else []
      childFrames ++ Exec.descendantFrames next
termination_by sizeOf run

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
def Exec.Frame.flowObservation? (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) : Option FlowObservation :=
  if exactInvocation dp ca frame.sevm then
    (primaryFlowAtom frame.sevm).map fun atom =>
      { atom
        actualCaller := frame.sevm.caller
        currentTarget := frame.sevm.currentTarget
        codeAddress := frame.sevm.codeAddress
        depth := frame.sevm.depth }
  else none

/-- Executable observations for one root derivation, in enclosing-frame then
depth-first child order.  Classification proofs later show that this includes
every and only committed balance-writing WETH10 invocation. -/
def Exec.flowObservations (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List FlowObservation :=
  (Exec.committedFrames run).filterMap
    (Exec.Frame.flowObservation? dp ca)

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

def RetainedXlot.flowObservations (dp : DeployParams) (ca : Adr)
    {xl : Xlot} : RetainedXlot xl → List FlowObservation
  | .none => []
  | .some run => Blanc.Weth10.Exec.flowObservations dp ca run

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

def MessageCallTrace.flowObservations (dp : DeployParams) (ca : Adr)
    {msg : Msg} {state : State} {out : MsgCallOutput} :
    MessageCallTrace msg state out → List FlowObservation
  | .createCollision .. => []
  | .createRun _ _ _ _ trace _ =>
      trace.retained.flowObservations dp ca
  | .callRun _ _ _ _ _ _ _ _ trace _ =>
      trace.retained.flowObservations dp ca

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

end Weth10

end Blanc
