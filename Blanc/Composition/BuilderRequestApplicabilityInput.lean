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

