import Blanc.ExecutionTraceFrames
import Blanc.ExecutionHistoryAdmission

/-!
# Admission of the raw frame roots retained by execution traces

Structural admission is exactly the entry condition on every actually entered
raw frame targeting the selected address.  This bridge applies before any
settlement or commitment filtering.
-/

namespace Blanc.ExecutionTrace

open Jaune

theorem RetainedXlot.frameAdmitted_iff_rawFrames
    {slot : Xlot} (trace : RetainedXlot slot)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm := by
  cases trace with
  | none => simp only [FrameAdmitted, rawFrames, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | some run => rfl

theorem ProcessMessageTrace.frameAdmitted_iff_rawFrames
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm :=
  trace.retained.frameAdmitted_iff_rawFrames ca entry

theorem ProcessCreateMessageTrace.frameAdmitted_iff_rawFrames
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm :=
  trace.retained.frameAdmitted_iff_rawFrames ca entry

theorem MessageCallTrace.frameAdmitted_iff_rawFrames
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm := by
  cases trace <;>
    simp only [MessageCallTrace.FrameAdmitted, MessageCallTrace.rawFrames,
      ProcessMessageTrace.frameAdmitted_iff_rawFrames,
      ProcessCreateMessageTrace.frameAdmitted_iff_rawFrames,
      List.not_mem_nil, false_implies, implies_true]

theorem TransactionTrace.frameAdmitted_iff_rawFrames
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm :=
  trace.message.frameAdmitted_iff_rawFrames ca entry

theorem ApplyTransactionsTrace.frameAdmitted_iff_rawFrames
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm := by
  induction trace with
  | nil => simp only [FrameAdmitted, rawFrames, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | cons head tail ih =>
      simp only [ApplyTransactionsTrace.FrameAdmitted, ApplyTransactionsTrace.rawFrames,
        head.frameAdmitted_iff_rawFrames ca entry, ih,
        List.mem_append, or_imp, forall_and]

theorem SystemMessageTrace.frameAdmitted_iff_rawFrames
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm :=
  trace.message.frameAdmitted_iff_rawFrames ca entry

theorem RequestsTrace.frameAdmitted_iff_rawFrames
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm := by
  have parts : trace.FrameAdmitted ca entry ↔
      trace.withdrawal.FrameAdmitted ca entry ∧
        trace.consolidation.FrameAdmitted ca entry :=
    ⟨fun h => ⟨h.withdrawal, h.consolidation⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [parts]
  simp only [RequestsTrace.rawFrames, SystemMessageTrace.frameAdmitted_iff_rawFrames,
    List.mem_append, or_imp, forall_and]

theorem AppliedBodyTrace.frameAdmitted_iff_rawFrames
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm := by
  have parts : trace.FrameAdmitted ca entry ↔
      ((trace.beacon.FrameAdmitted ca entry ∧ trace.history.FrameAdmitted ca entry) ∧
        trace.transactions.FrameAdmitted ca entry) ∧ trace.requests.FrameAdmitted ca entry :=
    ⟨fun h => ⟨⟨⟨h.beacon, h.history⟩, h.transactions⟩, h.requests⟩,
      fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩⟩
  rw [parts]
  simp only [AppliedBodyTrace.rawFrames, SystemMessageTrace.frameAdmitted_iff_rawFrames,
    ApplyTransactionsTrace.frameAdmitted_iff_rawFrames,
    RequestsTrace.frameAdmitted_iff_rawFrames, List.mem_append, or_imp, forall_and]

theorem ConfiguredBlockTrace.frameAdmitted_iff_rawFrames
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm :=
  trace.bodyTrace.frameAdmitted_iff_rawFrames ca entry

theorem ConfiguredHistoryTrace.frameAdmitted_iff_rawFrames
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames,
        root.sevm.currentTarget = ca → entry root.sevm root.devm := by
  induction trace with
  | refl => simp only [FrameAdmitted, rawFrames, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTrace.FrameAdmitted, ConfiguredHistoryTrace.rawFrames,
        ih, block.frameAdmitted_iff_rawFrames ca entry, List.mem_append, or_imp, forall_and]

end Blanc.ExecutionTrace
