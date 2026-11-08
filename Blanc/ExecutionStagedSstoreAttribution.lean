import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionTraceFrameEnv
import Blanc.ExecutionOccurrence

/-!
# Retained SSTOREs at the raw frames of a selected-domain history

The raw frames of a `ConfiguredHistoryTraceIn` are closed under descent
(`rawFrames_closed`): every raw frame root inside a raw frame's derivation is
itself a raw frame of the history. A committing raw frame whose own
derivation changes a storage cell of an initially code-bearing owner has a
last retained successful `SSTORE` of that cell (G2,
`Exec.exists_lastRetainedSstore_of_getStor_ne_noStateGas`, with
`stateGas = none` from `rawFrame_entryFacts`). The write sits on the
same-frame prefix of a committed frame of that derivation; that frame is a
raw frame of the history and executes at the owner.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

theorem BeaconStageTrace.rawFrames_closed {rules : ForkRules} {benv : Benv} {state : State}
    {bal : BalBuilder} (trace : BeaconStageTrace rules benv state bal) :
    RawFramesClosed trace.rawFrames :=
  match trace with
  | .skipped .. => RawFramesClosed.nil
  | .called _ _ message _ _ => message.message.rawFrames_closed

theorem HistoryStageTrace.rawFrames_closed {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) :
    RawFramesClosed trace.rawFrames :=
  match trace with
  | .skipped .. => RawFramesClosed.nil
  | .called _ _ _ _ message _ _ => message.message.rawFrames_closed

theorem RequestStageTrace.rawFrames_closed {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    RawFramesClosed trace.rawFrames :=
  match trace with
  | .skipped .. => RawFramesClosed.nil
  | .called _ requests _ => RawFramesClosed.append
      requests.withdrawal.message.rawFrames_closed
      requests.consolidation.message.rawFrames_closed

theorem StagedBodyTrace.rawFrames_closed {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    RawFramesClosed trace.rawFrames :=
  RawFramesClosed.append (RawFramesClosed.append (RawFramesClosed.append
    trace.beacon.rawFrames_closed trace.history.rawFrames_closed)
    trace.transactions.rawFrames_closed) trace.requests.rawFrames_closed

end ExecutionTrace

end Blanc
