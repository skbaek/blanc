import Blanc.Lift.BuilderRequest.Deposit.Delivery
import Blanc.Lift.BuilderRequest.Exit.Delivery
import Blanc.Lift.BuilderRequest.ChainLink
import Blanc.ExecutionKeptChain

/-!
# Builder request contracts: public observers

Short observers reading a `State` or a kept-frame list directly. Nothing here
mentions the delivery model (`QueueState`, `Frame`, `Holds`); the correspondence
to the model is proved below in the bridge theorems. Each observer has a
one-sentence docstring.
-/

namespace Blanc.Composition.BuilderRequestPublic

open Jaune Blanc Blanc.Lift.BuilderRequest

/-- The deposit builder contract's address. -/
abbrev depositAddr : Adr := Deposit.Creation.address

/-- The exit builder contract's address. -/
abbrev exitAddr : Adr := Exit.Creation.address

/-- Slot 0 of an account's storage, as a number: the excess, or the inhibitor. -/
def storedExcess (w : State) (a : Adr) : Nat := ((w.getStor a).get 0).toNat

/-- Slot 1 of an account's storage, as a number: the submission count. -/
def storedCount (w : State) (a : Adr) : Nat := ((w.getStor a).get 1).toNat

/-- The queue length a storage claims: head slot minus tail slot. -/
def storedQueueLen (w : State) (a : Adr) : Nat :=
  (w.getStor a).get 3 |>.toNat - (w.getStor a).get 2 |>.toNat

/-- Slot 0 holds the inhibitor, so user frames cannot run. -/
def inhibited (w : State) (a : Adr) : Prop := (w.getStor a).get 0 = B256.max

/-- The account runs the named builder code. -/
def runsBuilderCode (w : State) (a : Adr) (code : ByteArray) : Prop :=
  w.getCode a = code

/-- The kept frames a history ran at an address, in order. -/
noncomputable def keptAt (blocks : List KeptBlock) (a : Adr) : List Exec.Frame :=
  ChainLink.History.kept a blocks

/-- The records the history's kept frames at the deposit contract submitted. -/
noncomputable def depositSubmitted (blocks : List KeptBlock) : List Deposit.Record :=
  ChainLink.History.submitted Deposit.contract blocks

/-- The records the history's kept frames at the exit contract submitted. -/
noncomputable def exitSubmitted (blocks : List KeptBlock) : List Exit.Record :=
  ChainLink.History.submitted Exit.contract blocks

/-- The fees the history's kept frames at an address paid, summed. -/
noncomputable def feesPaidAt (blocks : List KeptBlock) (a : Adr) : Nat :=
  ((keptAt blocks a).map fun f => f.sevm.value.toNat).sum

/-- The request bytes a history's blocks carry for one request type. -/
noncomputable def deliveredOf (ty : UInt8) (blocks : List KeptBlock) : Bytes :=
  ChainLink.History.delivered ty blocks

/-- No kept frame in the history ran with the system caller at this address. -/
def noSystemFramesAt (blocks : List KeptBlock) (a : Adr) : Prop :=
  ∀ f ∈ keptAt blocks a, f.sevm.caller ≠ systemAddress

/-- The deposit contract's request type, from its chain link. -/
def depositType : UInt8 := 3

/-- The exit contract's request type, from its chain link. -/
def exitType : UInt8 := 4

/-- The deposit request bytes a history's blocks carry. -/
noncomputable def depositRequests (blocks : List KeptBlock) : Bytes :=
  deliveredOf depositType blocks

/-- The exit request bytes a history's blocks carry. -/
noncomputable def exitRequests (blocks : List KeptBlock) : Bytes :=
  deliveredOf exitType blocks

/-- 1 ETH in wei, the deposit floor. -/
def oneEth : Nat := 10 ^ 18

/-- The load a storage claims: excess plus count, valid off the latch. -/
def storedLoad (w : State) (a : Adr) : Nat := storedExcess w a + storedCount w a

/-- The checked system call with this data succeeds with this result. -/
def callIsOk (benv : Benv) (a : Adr) (data : Bytes) (post : State)
    (out : MsgCallOutput) : Prop :=
  processCheckedSystemTransaction benv a data = .ok (post, out)

/-- How many system-caller frames ran at an address in the history. -/
def sysCallCount (blocks : List KeptBlock) (a : Adr) : Nat :=
  ((keptAt blocks a).filter (fun f => decide (f.sevm.caller = systemAddress))).length

/-- The natural-fee budget the history's deposit submissions paid. -/
noncomputable def depositFeeSum (blocks : List KeptBlock) : Nat :=
  ((((keptAt blocks depositAddr).filter (fun f => decide (f.sevm.data.length = 184))).map
    (ChainLink.History.naturalFee Deposit.contract))).sum

/-- The natural-fee budget the history's exit submissions paid. -/
noncomputable def exitFeeSum (blocks : List KeptBlock) : Nat :=
  ((((keptAt blocks exitAddr).filter (fun f => decide (f.sevm.data.length = 48))).map
    (ChainLink.History.naturalFee Exit.contract))).sum

/-- No system-caller, no authority, no created-address frames: the O19 premises. -/
structure HistoryClean (blocks : List KeptBlock) : Prop where
  /-- No kept block recovers the system address as a sender. -/
  senders : ChainLink.History.NoSender systemAddress blocks
  /-- No kept block carries its authority. -/
  authorities : ChainLink.History.NoAuthority systemAddress blocks
  /-- No kept block creates it. -/
  creates : ChainLink.History.NoCreate systemAddress blocks

/-- The deployed storage shape at a chain start. -/
structure DeployedStart (start : BlockChain) : Prop where
  /-- The deposit queue starts empty of excess. -/
  depExcess : storedExcess start.state depositAddr = 0
  /-- The deposit queue starts empty of count. -/
  depCount : storedCount start.state depositAddr = 0
  /-- The deposit queue starts empty of records. -/
  depQueue : storedQueueLen start.state depositAddr = 0
  /-- The exit contract starts inhibited. -/
  exitInhib : inhibited start.state exitAddr

/-- All four request contracts' code at a start. -/
structure FourCodes (start : BlockChain) : Prop where
  /-- EIP-7002's code is installed. -/
  w7002 : start.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode
  /-- EIP-7251's code is installed. -/
  w7251 : start.state.getCode consolidationRequestPredeployAddress =
    Blanc.consolidationRequestCode
  /-- The deposit code is installed. -/
  dep : runsBuilderCode start.state depositAddr Deposit.code
  /-- The exit code is installed. -/
  ext : runsBuilderCode start.state exitAddr Exit.code

end Blanc.Composition.BuilderRequestPublic
