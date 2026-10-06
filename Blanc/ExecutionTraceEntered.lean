import Blanc.ExecutionTraceFrames
import Blanc.ExecutionTraceAdmission
import Blanc.ExecutionFrameEntry

/-!
# Entry conditions every entered frame satisfies, at every retained raw root

`Exec.FreshEntry` (empty stack and memory) is one fact about a freshly entered frame; others, such as
the cleared output buffer (`Frame.enter_run_output_empty`), hold for the same reason: every raw frame
root a trace retains is the initial machine of a frame that `Frame.enter` started.  This module states
that once, for an arbitrary condition `E` closed under frame entry (`EnteredCondition E`), along the
whole retained carrier chain from a raw execution to a configured history:

* `Exec.rawFrameDescendants_entered`, `RetainedXlot.rawFrames_entered` and the carrier rungs up to
  `ConfiguredHistoryTrace.rawFrames_entered`;
* `ConfiguredHistoryTrace.frameAdmitted_entered`: the corresponding trace admission;
* `enteredCondition_fresh`, `enteredCondition_output`: fresh stack and memory, and the cleared output
  buffer, are such conditions, so
  `ConfiguredHistoryTrace.frameAdmitted_output` admits `pre.output = []` at every frame root.
-/

namespace Blanc

open Jaune

/-- An entry condition that every successfully entered frame's initial machine satisfies. -/
def EnteredCondition (E : Sevm → Devm → Prop) : Prop :=
  ∀ {frame : Frame} {child : Evm}, frame.enter = .run child → E child.sta child.dyna

/-- The cleared output buffer is an entry condition. -/
theorem enteredCondition_output : EnteredCondition (fun _ pre => pre.output = []) :=
  fun henter => Frame.enter_run_output_empty henter

/-- The empty stack and memory are an entry condition. -/
theorem enteredCondition_fresh : EnteredCondition Exec.FreshEntry :=
  fun henter => Frame.enter_run_fresh henter

/-- Every raw descendant root satisfies an entry condition. -/
theorem Exec.rawFrameDescendants_entered {E : Sevm → Devm → Prop} (hE : EnteredCondition E)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out) :
    ∀ root ∈ Exec.rawFrameDescendants run, E root.sevm root.devm := by
  induction run with
  | halt hstep =>
      intro root member
      simp only [Exec.rawFrameDescendants, List.not_mem_nil] at member
  | cont hstep next ih =>
      intro root member
      exact ih root (by simpa only [Exec.rawFrameDescendants] using member)
  | doneErr hstep henter hresume =>
      intro root member
      simp only [Exec.rawFrameDescendants, List.not_mem_nil] at member
  | doneOk hstep henter hresume next ih =>
      intro root member
      exact ih root (by simpa only [Exec.rawFrameDescendants] using member)
  | runErr hstep henter child hresume ih =>
      intro root member
      simp only [Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact hE henter
      · exact ih root member
  | runOk hstep henter child hresume next ihChild ihNext =>
      intro root member
      simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at member
      rcases member with rfl | member | member
      · exact hE henter
      · exact ihChild root member
      · exact ihNext root member

namespace ExecutionTrace

theorem RetainedXlot.rawFrames_entered {E : Sevm → Devm → Prop} (hE : EnteredCondition E)
    {frame : Frame} {slot : Xlot} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out) :
    ∀ root ∈ retained.rawFrames, E root.sevm root.devm := by
  cases retained with
  | none => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
      intro root member
      simp only [rawFrames, Exec.rawFrameRoots, List.mem_cons] at member
      rcases member with rfl | member
      · exact hE (RunFrame.some_inv hrun).1
      · exact Exec.rawFrameDescendants_entered hE run root member

theorem ProcessMessageTrace.rawFrames_entered {E : Sevm → Devm → Prop} (hE : EnteredCondition E)
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm :=
  trace.retained.rawFrames_entered hE trace.run

theorem ProcessCreateMessageTrace.rawFrames_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm :=
  trace.retained.rawFrames_entered hE trace.run

theorem MessageCallTrace.rawFrames_entered {E : Sevm → Devm → Prop} (hE : EnteredCondition E)
    {msg : Msg} {state : State} {out : MsgCallOutput} (trace : MessageCallTrace msg state out) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm := by
  cases trace with
  | createCollision => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | createRun target collision evm core coreTrace result =>
      exact coreTrace.rawFrames_entered hE
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      exact coreTrace.rawFrames_entered hE

theorem TransactionTrace.rawFrames_entered {E : Sevm → Devm → Prop} (hE : EnteredCondition E)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {state : State}
    {bout' : BlockOutput} (trace : TransactionTrace benv bout tx index state bout') :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm :=
  trace.message.rawFrames_entered hE

theorem ApplyTransactionsTrace.rawFrames_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm := by
  induction trace with
  | nil => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | cons head tail ih =>
      intro root member
      simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact head.rawFrames_entered hE root member
      · exact ih root member

theorem SystemMessageTrace.rawFrames_entered {E : Sevm → Devm → Prop} (hE : EnteredCondition E)
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm :=
  trace.message.rawFrames_entered hE

theorem RequestsTrace.rawFrames_entered {E : Sevm → Devm → Prop} (hE : EnteredCondition E)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm := by
  intro root member
  simp only [RequestsTrace.rawFrames, List.mem_append] at member
  rcases member with member | member
  · exact trace.withdrawal.rawFrames_entered hE root member
  · exact trace.consolidation.rawFrames_entered hE root member

theorem AppliedBodyTrace.rawFrames_entered {E : Sevm → Devm → Prop} (hE : EnteredCondition E)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal} {state : State}
    {bout : BlockOutput} (trace : AppliedBodyTrace benv txs wds state bout) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm := by
  intro root member
  simp only [AppliedBodyTrace.rawFrames, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact trace.beacon.rawFrames_entered hE root member
  · exact trace.history.rawFrames_entered hE root member
  · exact trace.transactions.rawFrames_entered hE root member
  · exact trace.requests.rawFrames_entered hE root member

theorem ConfiguredBlockTrace.rawFrames_entered {E : Sevm → Devm → Prop} (hE : EnteredCondition E)
    {cfg : ChainConfig} {pre post : BlockChain} (trace : ConfiguredBlockTrace cfg pre post) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm :=
  trace.bodyTrace.rawFrames_entered hE

/-- **Every raw frame root a configured history retains satisfies every entry condition.** -/
theorem ConfiguredHistoryTrace.rawFrames_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    ∀ root ∈ trace.rawFrames, E root.sevm root.devm := by
  induction trace with
  | refl => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | step prior block ih =>
      intro root member
      simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact ih root member
      · exact block.rawFrames_entered hE root member

/-- Trace admission of an entry condition, at any address. -/
theorem ConfiguredHistoryTrace.frameAdmitted_entered {E : Sevm → Devm → Prop}
    (hE : EnteredCondition E) {cfg : ChainConfig} {checkpoint future : BlockChain} {ca : Adr}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : trace.FrameAdmitted ca E := by
  rw [ConfiguredHistoryTrace.frameAdmitted_iff_rawFrames]
  intro root member _
  exact trace.rawFrames_entered hE root member

/-- Every frame root of a configured history starts with an empty output buffer. -/
theorem ConfiguredHistoryTrace.frameAdmitted_output {cfg : ChainConfig}
    {checkpoint future : BlockChain} {ca : Adr}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    trace.FrameAdmitted ca (fun _ pre => pre.output = []) :=
  trace.frameAdmitted_entered enteredCondition_output

end ExecutionTrace

end Blanc
