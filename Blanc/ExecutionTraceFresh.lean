import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionFrameEntry

/-!
# Fresh-entry admission through retained execution traces

The raw-frame theorem in `ExecutionFrameEntry` knows that a concrete `Exec`
starts fresh once its entering frame is known.  Retained message traces carry
that entry equation; this module derives fresh-entry admission from the trace
itself and provides conjunction transport for composing it with an independent
contract-specific entry condition.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Conjoin two entry conditions over one retained recursive slot. -/
theorem RetainedXlot.FrameAdmitted.and
    {slot : Xlot} {trace : RetainedXlot slot}
    {ca : Adr} {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left)
    (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca
      (fun sevm pre => left sevm pre ∧ right sevm pre) := by
  cases trace with
  | none => trivial
  | some run =>
      exact Exec.FrameAdmitted.and hleft hright

theorem ProcessMessageTrace.FrameAdmitted.and
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    {trace : ProcessMessageTrace msg out}
    {ca : Adr} {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left)
    (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca
      (fun sevm pre => left sevm pre ∧ right sevm pre) :=
  RetainedXlot.FrameAdmitted.and hleft hright

theorem ProcessCreateMessageTrace.FrameAdmitted.and
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    {trace : ProcessCreateMessageTrace msg out}
    {ca : Adr} {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left)
    (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca
      (fun sevm pre => left sevm pre ∧ right sevm pre) :=
  RetainedXlot.FrameAdmitted.and hleft hright

/-- Raw call-message traces automatically admit fresh entry at every retained
interpreter root. -/
theorem ProcessMessageTrace.freshFrameAdmitted
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry := by
  rcases trace with ⟨slot, retained, hrun⟩
  cases retained with
  | none => trivial
  | @some pc sevm pre execution run =>
      have henter : (Frame.ofCall msg).enter =
          FrameEntry.run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hrun).1
      exact Exec.FrameAdmitted.fresh_of_enter henter run ca

/-- Raw create-message traces automatically admit fresh entry at every
retained interpreter root. -/
theorem ProcessCreateMessageTrace.freshFrameAdmitted
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry := by
  rcases trace with ⟨slot, retained, hrun⟩
  cases retained with
  | none => trivial
  | @some pc sevm pre execution run =>
      have henter : (Frame.ofCreate msg).enter =
          FrameEntry.run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hrun).1
      exact Exec.FrameAdmitted.fresh_of_enter henter run ca

theorem MessageCallTrace.FrameAdmitted.and
    {msg : Msg} {state : State} {out : MsgCallOutput}
    {trace : MessageCallTrace msg state out}
    {ca : Adr} {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left)
    (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca
      (fun sevm pre => left sevm pre ∧ right sevm pre) := by
  cases trace with
  | createCollision => trivial
  | createRun target collision evm core coreTrace result =>
      exact ProcessCreateMessageTrace.FrameAdmitted.and hleft hright
  | callRun target delegated refund delegation execMsg execMsgEq evm core
      coreTrace result =>
      exact ProcessMessageTrace.FrameAdmitted.and hleft hright

/-- A settled message-call trace automatically admits fresh entry for every
interpreter core it actually retained. -/
theorem MessageCallTrace.freshFrameAdmitted
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry := by
  cases trace with
  | createCollision => trivial
  | createRun target collision evm core coreTrace result =>
      exact coreTrace.freshFrameAdmitted ca
  | callRun target delegated refund delegation execMsg execMsgEq evm core
      coreTrace result =>
      exact coreTrace.freshFrameAdmitted ca

theorem TransactionTrace.FrameAdmitted.and
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    {trace : TransactionTrace benv bout tx index state bout'}
    {ca : Adr} {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left)
    (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca
      (fun sevm pre => left sevm pre ∧ right sevm pre) :=
  MessageCallTrace.FrameAdmitted.and hleft hright

theorem TransactionTrace.freshFrameAdmitted
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry :=
  trace.message.freshFrameAdmitted ca

theorem ApplyTransactionsTrace.FrameAdmitted.and
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    {ca : Adr} {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left)
    (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca
      (fun sevm pre => left sevm pre ∧ right sevm pre) := by
  induction trace with
  | nil => trivial
  | cons head tail ih =>
      exact ⟨TransactionTrace.FrameAdmitted.and hleft.1 hright.1,
        ih hleft.2 hright.2⟩

theorem ApplyTransactionsTrace.freshFrameAdmitted
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry := by
  induction trace with
  | nil => trivial
  | cons head tail ih =>
      exact ⟨head.freshFrameAdmitted ca, ih⟩

theorem SystemMessageTrace.FrameAdmitted.and
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    {trace : SystemMessageTrace benv target data state out}
    {ca : Adr} {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left)
    (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca
      (fun sevm pre => left sevm pre ∧ right sevm pre) :=
  MessageCallTrace.FrameAdmitted.and hleft hright

theorem SystemMessageTrace.freshFrameAdmitted
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry :=
  trace.message.freshFrameAdmitted ca

theorem RequestsTrace.FrameAdmitted.and
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    {trace : RequestsTrace benv bout state bout'}
    {ca : Adr} {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left)
    (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca
      (fun sevm pre => left sevm pre ∧ right sevm pre) where
  withdrawal := SystemMessageTrace.FrameAdmitted.and
    hleft.withdrawal hright.withdrawal
  consolidation := SystemMessageTrace.FrameAdmitted.and
    hleft.consolidation hright.consolidation

theorem RequestsTrace.freshFrameAdmitted
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry where
  withdrawal := trace.withdrawal.freshFrameAdmitted ca
  consolidation := trace.consolidation.freshFrameAdmitted ca

theorem AppliedBodyTrace.FrameAdmitted.and
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    {trace : AppliedBodyTrace benv txs wds state bout}
    {ca : Adr} {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left)
    (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca
      (fun sevm pre => left sevm pre ∧ right sevm pre) where
  beacon := SystemMessageTrace.FrameAdmitted.and hleft.beacon hright.beacon
  history := SystemMessageTrace.FrameAdmitted.and hleft.history hright.history
  transactions := ApplyTransactionsTrace.FrameAdmitted.and
    hleft.transactions hright.transactions
  requests := RequestsTrace.FrameAdmitted.and hleft.requests hright.requests

theorem AppliedBodyTrace.freshFrameAdmitted
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry where
  beacon := trace.beacon.freshFrameAdmitted ca
  history := trace.history.freshFrameAdmitted ca
  transactions := trace.transactions.freshFrameAdmitted ca
  requests := trace.requests.freshFrameAdmitted ca

theorem ConfiguredBlockTrace.FrameAdmitted.and
    {cfg : ChainConfig} {pre post : BlockChain}
    {trace : ConfiguredBlockTrace cfg pre post}
    {ca : Adr} {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left)
    (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca
      (fun sevm pre => left sevm pre ∧ right sevm pre) :=
  AppliedBodyTrace.FrameAdmitted.and hleft hright

theorem ConfiguredBlockTrace.freshFrameAdmitted
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post)
    (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry :=
  trace.bodyTrace.freshFrameAdmitted ca

theorem ConfiguredHistoryTrace.FrameAdmitted.and
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {trace : ConfiguredHistoryTrace cfg checkpoint future}
    {ca : Adr} {left right : Sevm → Devm → Prop}
    (hleft : trace.FrameAdmitted ca left)
    (hright : trace.FrameAdmitted ca right) :
    trace.FrameAdmitted ca
      (fun sevm pre => left sevm pre ∧ right sevm pre) := by
  induction trace with
  | refl => trivial
  | step prior block ih =>
      exact ⟨ih hleft.1 hright.1,
        ConfiguredBlockTrace.FrameAdmitted.and hleft.2 hright.2⟩

/-- Configured histories automatically admit fresh entry at every interpreter
root in every retained block. -/
theorem ConfiguredHistoryTrace.freshFrameAdmitted
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (ca : Adr) :
    trace.FrameAdmitted ca Exec.FreshEntry := by
  induction trace with
  | refl => trivial
  | step prior block ih =>
      exact ⟨ih, block.freshFrameAdmitted ca⟩

end ExecutionTrace

end Blanc
