import Blanc.Composition.BuilderRequestApplicability.Checks
import Blanc.Composition.BuilderRequestJointG
import Blanc.Composition.BuilderRequestPublicObservers
import Blanc.Lift.SystemWordWriter
import Blanc.Lift.WithdrawalRequest.DrainTx

/-! Literal caller bytes for the single builder applicability transaction. The
writer and ordinary-helper byte strings are moved from ApplicabilityCalls once. -/
namespace Blanc.Composition.BuilderRequestApplicabilityInput
open Jaune Blanc Blanc.Lift
open Blanc.Composition.BuilderRequestPublic (depositAddr exitAddr)
variable (full : Bool)

def ordinaryAddr : Adr := 0x1234

-- Empty static fee read, then a 184-byte deposit with 10^9 gwei credited;
-- empty static exit fee read, then a 48-byte exit paid at its returned fee.
def ordinaryCode : ByteArray :=
  ⟨([0x60, 0x20, 0x5f, 0x5f, 0x5f, 0x73] ++ depositAddr.toBytes ++
    [0x5a, 0xfa, 0x50, 0x63, 0x3b, 0x9a, 0xca, 0x00, 0x60, 0x38, 0x52,
     0x5f, 0x5f, 0x60, 0xb8, 0x5f, 0x5f, 0x51, 0x67,
     0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00, 0x01, 0x73] ++
    depositAddr.toBytes ++ [0x5a, 0xf1, 0x50,
     0x60, 0x20, 0x5f, 0x5f, 0x5f, 0x73] ++ exitAddr.toBytes ++
    [0x5a, 0xfa, 0x50, 0x5f, 0x5f, 0x60, 0x30, 0x5f, 0x5f, 0x51, 0x73] ++
    exitAddr.toBytes ++ [0x5a, 0xf1, 0x50, 0x00]).toArray⟩

def ordinaryAcct : Acct :=
  { Acct.nil with nonce := 1, bal := (2 ^ 100 : Nat).toB256, code := ordinaryCode }

-- Remaining SYSTEM calls: Exit latch/reset, then the funded ordinary helper.
-- Only their bytes/context are selected here; their executions are later work.
def writerSuffix : Bytes :=
  [0x50, 0x5f, 0x5f, 0x60, 0x20, 0x5f, 0x5f, 0x73] ++ exitAddr.toBytes ++
  [0x5a, 0xf1, 0x50, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x73] ++ exitAddr.toBytes ++
  [0x5a, 0xf1, 0x50, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x73] ++ ordinaryAddr.toBytes ++
  [0x5a, 0xf1, 0x50, 0x00]

def writerPrefix : Bytes :=
  (SystemWordWriter.code depositAddr 0).toList.take 64 ++
    [0x50, 0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x73] ++ depositAddr.toBytes ++ [0x5a, 0xf1]

def writerCode : ByteArray :=
  ⟨(writerPrefix ++ if full then writerSuffix else [0x00]).toArray⟩

end Blanc.Composition.BuilderRequestApplicabilityInput

namespace Blanc.Composition.BuilderRequestApplicabilityInput
open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.BuilderRequestPublic (depositAddr exitAddr)
open Blanc.Lift.WithdrawalRequest.FloodTx (txD senderE)

/-- A literal nonempty STOP runtime for the two mandatory checked endpoints. -/
def stopCode : ByteArray := ⟨#[0x00]⟩

def senderAcct (nonce : UInt64) (funds : Nat) : Acct :=
  { Acct.nil with nonce := nonce, bal := funds.toB256 }

def baseWorld (full : Bool) : State :=
  State.setPresent (State.setPresent (State.setPresent (State.setPresent .empty ordinaryAddr ordinaryAcct)
    systemAddress { Acct.nil with nonce := 1, code := writerCode full })
    depositAddr { Acct.nil with nonce := 1, code := BuilderRequest.Deposit.code })
    exitAddr { Acct.nil with nonce := 1, code := BuilderRequest.Exit.code }

/-- None retains the original input world; a parent hash selects the explicit
successor context with provisioned mandatory checked request endpoints. -/
def builderWorld (full : Bool) (parentHash : Option B256) : State :=
  match parentHash with
  | none => baseWorld full
  | some _ => ((baseWorld full).setPresent withdrawalRequestPredeployAddress
      { Acct.nil with nonce := 1, code := stopCode }).setPresent consolidationRequestPredeployAddress
      { Acct.nil with nonce := 1, code := stopCode }

def state (full : Bool) (parentHash : Option B256) : State :=
  (builderWorld full parentHash).setPresent senderE (senderAcct 2 (2 ^ 100))

def debit (full : Bool) (parentHash : Option B256) : State :=
  (builderWorld full parentHash).setPresent senderE (senderAcct 3 (2 ^ 100 - 2 ^ 21))

def benv (full : Bool) (parentHash : Option B256) : Benv :=
  { (default : Benv) with
    state := state full parentHash
    stat := { (default : Benv).stat with
      fork := .prague
      chainId := 1
      number := parentHash.elim 0 (fun _ => 1)
      time := parentHash.elim 0 (fun _ => 1)
      blockHashes := parentHash.elim [] (fun h => [0, h])
      origState := state full parentHash
      blockGasLimit := 60000000
      baseFeePerGas := 1 } }

def msg (full : Bool) (parentHash : Option B256) : Msg :=
  callMessage { (benv full parentHash).beginTransaction with state := debit full parentHash }
    (transactionTenv (benv full parentHash).beginTransaction txD 0 senderE 2 21000 []) txD systemAddress


/-- Finite account shadow of the exact transaction-debited input world. -/
def accounts (full : Bool) (parentHash : Option B256) : List (Adr × Acct) :=
  [(senderE, senderAcct 3 (2 ^ 100 - 2 ^ 21)),
    (exitAddr, { Acct.nil with nonce := 1, code := BuilderRequest.Exit.code }),
    (depositAddr, { Acct.nil with nonce := 1, code := BuilderRequest.Deposit.code }),
    (systemAddress, { Acct.nil with nonce := 1, code := writerCode full }),
    (ordinaryAddr, ordinaryAcct)] ++ parentHash.elim [] (fun _ =>
      [(withdrawalRequestPredeployAddress, { Acct.nil with nonce := 1, code := stopCode }),
       (consolidationRequestPredeployAddress, { Acct.nil with nonce := 1, code := stopCode })])

end Blanc.Composition.BuilderRequestApplicabilityInput


/-! ## Separate clean P5 replay input checks

The unrestricted coded-SYSTEM worlds above witness Form B success arms. They
are not clean P5 inputs. These checks instead accept a supplied pre-Gloas joint
state and use real BLS and the original joint interpreter.
-/
namespace Blanc.Composition.BuilderRequestApplicabilityInput
open Jaune JauneConsensus Blanc.Lift
open Blanc.Composition.BuilderRequestApplicability.Checks

/-- The exact two nontrivial pre-Gloas anchor obligations of `ValidJointG`:
the finalized epoch is not ahead of the slot, and the execution head hash is the
beacon state's latest execution payload hash. Pending-payload coherence and bid
witnesses are trivial at this constructor, without selecting a Gloas anchor. -/
def PreAnchor {P : Preset} (cfg : ChainConfig) (state : JointState P) : Prop :=
  BuilderRequest.GAnchorInv (.pre state) ∧ Blanc.GJointInv cfg (.pre state)

instance instDecidablePreAnchor {P : Preset} (cfg : ChainConfig) (state : JointState P) :
    Decidable (PreAnchor cfg state) := by
  unfold PreAnchor BuilderRequest.GAnchorInv Blanc.GJointInv
    Blanc.ExecHeadIsLatestBlockHash Blanc.ParentPayloadCoherence
    Blanc.ExpectedWithdrawalsLedger JauneConsensus.Facts.Gloas.Inv.FinalizedNotAheadF
  infer_instance

/-- Replay with the exact pre-Gloas anchor invariants checked, in addition to the
twelve finite fields on the computed states. No anchor property or successful
trace is an input. This remains partial: cleanliness, history value bounds and
the nontrivial activity requirements are not established here. -/
def replayAnchored {P : Preset} (cfg : ChainConfig) (ccfg : Config) (state : JointState P)
    (inputs : List (Blanc.JointGloasReplayStep.Input P)) :
    Option {out : GJointState P × List (GJointState P) //
      Blanc.JointGloasReplayStep.Admits cfg ccfg true (.pre state) out.1 inputs out.2 ∧
        FiniteApplicability ccfg state.exec out.2 ∧ PreAnchor cfg state} := do
  if anchor : PreAnchor cfg state then
    let cert ← replayFinite cfg ccfg state inputs
    some ⟨cert.val, cert.property.1, cert.property.2, anchor⟩
  else none

/-- All computed applicability evidence, tied to the same original inputs,
intermediate states and actual retained interpreter derivations. -/
def Applicable {P : Preset} (cfg : ChainConfig) (ccfg : Config) (state : JointState P)
    (inputs : List (Blanc.JointGloasReplayStep.Input P))
    (out : GJointState P × List (GJointState P) × List Blanc.KeptBlock) : Prop :=
  Blanc.JointGloasReplayStep.AdmitsKept cfg ccfg true (.pre state) out.1 inputs out.2.1 out.2.2 ∧
  FiniteApplicability ccfg state.exec out.2.1 ∧ PreAnchor cfg state ∧ HistoryChecked out.2.2

/-- Check full applicability from a supplied pre-Gloas checkpoint, using real
BLS and only original interpreters. No successful trace, clean history, value
bound or anchor invariant is an input. This permits empty runs; nontrivial P5
activity and agreement of independent clients must still be established. -/
def replayApplicable {P : Preset} (depth : Nat) (cfg : ChainConfig) (ccfg : Config) (state : JointState P)
    (inputs : List (Blanc.JointGloasReplayStep.Input P)) :
    Option {out : GJointState P × List (GJointState P) × List Blanc.KeptBlock //
      Applicable cfg ccfg state inputs out} := do
  if anchor : PreAnchor cfg state then do
    let cert ← Blanc.JointGloasReplayStep.replayFromPreKept depth cfg ccfg state inputs
    if finite : FiniteApplicability ccfg state.exec cert.val.2.1 then do
      let history ← checkHistory cert.val.2.2
      pure ⟨cert.val, cert.property, finite, anchor, history.property⟩
    else none
  else none

/-- A checked certificate supplies every field of the original `ValidJointG`,
with the exact checked input/state/block sequence. It assumes no activity or
client agreement beyond that sequence's original successful transitions. -/
theorem applicable_valid {P : Preset} {cfg : ChainConfig} {ccfg : Config} {state : JointState P}
    {inputs : List (Blanc.JointGloasReplayStep.Input P)}
    (cert : {out : GJointState P × List (GJointState P) × List Blanc.KeptBlock //
      Applicable cfg ccfg state inputs out}) :
    ∃ valid : BuilderRequest.ValidJointG cfg ccfg true state.exec (.pre state) cert.val.1,
      valid.run.steps.map (fun D => (D.block, D.env?)) = inputs ∧
      valid.run.states = cert.val.2.1 ∧ valid.run.blocks = cert.val.2.2 := by
  obtain ⟨⟨run, inputsEq, statesEq, blocksEq⟩, finite, anchor, history⟩ := cert.property
  obtain ⟨⟨sys, depositCode, depositStorage, exitCode, exitStorage⟩,
    ⟨quorum, inclusion, delay, below, slots⟩, ⟨validators, builders⟩⟩ := finite
  have checked : ∀ b ∈ run.blocks, KeptChecked b := by rw [blocksEq]; exact history.1
  let valid : BuilderRequest.ValidJointG cfg ccfg true state.exec (.pre state) cert.val.1 := {
    noSystemCode := sys
    preBlocks := []
    prefixHistory := .refl
    run := run
    anchorPending := True.intro
    anchorInv := anchor.1
    anchorWitness := PUnit.unit
    anchorJoint := anchor.2
    depositInstalled := depositCode
    depositFresh := depositStorage
    exitInstalled := exitCode
    exitFresh := exitStorage
    senders := fun b member => (checked b member).1.1
    authorities := fun b member => (checked b member).1.2.1
    creates := fun b member => (checked b member).1.2.2
    depositBudget := by simpa only [List.nil_append, blocksEq] using history.2.1
    exitFew := by simpa only [List.nil_append, blocksEq] using history.2.2
    quorumPositive := quorum
    inclusionDelay := inclusion
    exitDelayPos := delay
    exitDelayBelow := below
    slotsPerEpoch := slots
    validatorsBound := fun st member => validators st (statesEq ▸ member)
    buildersBound := fun st member => builders st (statesEq ▸ member)
    roots := fun b member => (checked b member).2.2.2.1
    depositNoSender := fun b member => (checked b member).2.1
    exitNoSender := fun b member => (checked b member).2.2.1
    creditsFit := ⟨fun b member => (checked b member).2.2.2.2.1,
      fun b member => (checked b member).2.2.2.2.2⟩
    codes := ⟨run.keptHistory, depositCode, exitCode⟩ }
  exact ⟨valid, inputsEq, statesEq, blocksEq⟩

end Blanc.Composition.BuilderRequestApplicabilityInput
