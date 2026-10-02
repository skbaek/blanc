import Blanc.ExecutionSettlement
import Blanc.ExecutionTraceFrames

namespace Blanc.ExecutionTrace

open Jaune

def RetainedXlot.settledFrames {slot : Xlot} :
    RetainedXlot slot → List Exec.Frame
  | .none => []
  | .some run => Exec.committedFrames run

def ProcessMessageTrace.settledFrames
    (trace : ProcessMessageTrace msg out) : List Exec.Frame :=
  match trace with
  | ⟨_, .none, _⟩ => []
  | ⟨_, @RetainedXlot.some pc sevm pre raw run, _⟩ =>
      if Frame.settlementCommits (Frame.ofCall msg) raw = true then
        Exec.committedFrames run
      else []

def ProcessCreateMessageTrace.settledFrames
    (trace : ProcessCreateMessageTrace msg out) : List Exec.Frame :=
  match trace with
  | ⟨_, .none, _⟩ => []
  | ⟨_, @RetainedXlot.some pc sevm pre raw run, _⟩ =>
      if Frame.settlementCommits (Frame.ofCreate msg) raw = true then
        Exec.committedFrames run
      else []

def MessageCallTrace.settledFrames :
    MessageCallTrace msg state out → List Exec.Frame
  | .createCollision .. => []
  | .createRun _ _ _ _core trace _ => trace.settledFrames
  | .callRun _ _ _ _ _ _ _ _core trace _ => trace.settledFrames

def TransactionTrace.settledFrames
    (trace : TransactionTrace benv bout tx index state bout') :
    List Exec.Frame :=
  trace.message.settledFrames

def ApplyTransactionsTrace.settledFrames :
    ApplyTransactionsTrace txs benv bout finalBenv finalBout → List Exec.Frame
  | .nil _ _ => []
  | .cons head tail => head.settledFrames ++ tail.settledFrames

def SystemMessageTrace.settledFrames
    (trace : SystemMessageTrace benv target data state out) :
    List Exec.Frame :=
  trace.message.settledFrames

def RequestsTrace.settledFrames
    (trace : RequestsTrace benv bout state bout') : List Exec.Frame :=
  trace.withdrawal.settledFrames ++ trace.consolidation.settledFrames

def AppliedBodyTrace.settledFrames
    (trace : AppliedBodyTrace benv txs wds state bout) : List Exec.Frame :=
  trace.beacon.settledFrames ++ trace.history.settledFrames ++
    trace.transactions.settledFrames ++ trace.requests.settledFrames

def ConfiguredBlockTrace.settledFrames
    (trace : ConfiguredBlockTrace cfg pre post) : List Exec.Frame :=
  trace.bodyTrace.settledFrames

def ConfiguredHistoryTrace.settledFrames :
    ConfiguredHistoryTrace cfg checkpoint future → List Exec.Frame
  | .refl _ _ _ => []
  | .step prior block => prior.settledFrames ++ block.settledFrames

end Blanc.ExecutionTrace
