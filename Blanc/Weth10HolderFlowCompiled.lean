import Blanc.ExecutionOccurrence
import Blanc.ExecDeterminism
import Blanc.Weth10HolderFlowAuthenticity
import Blanc.Weth10HolderFlowEth
import Blanc.Weth10HolderFlowLocal
import Blanc.Weth10HolderFlowSelectorFacts
import Blanc.Weth10Read

/-!
Compiled-program authenticity for the local WETH10 balance segments.

The public frame classifier is executable, but its successful result alone is
not evidence that the corresponding storage writes ran.  This module connects
that result to the generated WETH10 program and the exact functional theorems.
Callback-bearing entries expose the end of the frame's own balance prefix;
nested callback effects are deliberately not folded into that boundary.
-/

namespace Blanc

open Jaune
open scoped LogOutputHinv

namespace Weth10

/-- A classified frame has an exact local effect beginning at its entry
balance map.  The existential endpoint is the end of the frame's own balance
segment, which need not be the enclosing frame endpoint when a callback can
reenter WETH10. -/
def Exec.Frame.HasLocalOwnEffect (ca : Adr) (frame : Exec.Frame)
    (action : FlowAction) : Prop :=
  ∃ ownPost : HolderBalances,
    LocalOwnEffect action
      (Stor.rest (Devm.getStor frame.pre ca)) ownPost

/-- Public names used by the compiled classifier for the callback predicates
whose parent `pc` and same-slot `StepRun` are retained by the functional
layer. -/
abbrev RetainedTokenCallbackBoundary := RawTokenCallbackStepBoundary

abbrev RetainedFlashCallbackBoundary := RawFlashCallbackStepBoundary

/-- Exact operational storage shape of one classified frame.  Call-free
actions end at the committed frame endpoint.  Value calls retain their exact
accepted child trace and a WETH-silent suffix.  ERC-677 and flash callbacks
retain their concrete recursive message traces, while flash keeps the two
same-action balance segments on their actual sides of the callback gap. -/
inductive RichLocalStorageEffect (dp : DeployParams) (ca : Adr)
    (e : Sevm) (pre post : Devm) (action : FlowAction) : Prop
  | ordinaryMint
      (segment : LocalActionSegment .ordinaryMint action
        (Stor.rest (Devm.getStor pre ca))
        (Stor.rest (Devm.getStor post ca)))
  | ordinaryTransfer
      (segment : LocalActionSegment .ordinaryTransfer action
        (Stor.rest (Devm.getStor pre ca))
        (Stor.rest (Devm.getStor post ca)))
  | redemption (ownPre callPre guardPost : Devm)
      (owner : Adr) (amount target : B256)
      (entrySilent : Stor.Weth10Silent
        (Devm.getStor pre ca) (Devm.getStor ownPre ca))
      (entryCode : ownPre.getCode ca = pre.getCode ca)
      (segment : LocalActionSegment .redemption action
        (Stor.rest (Devm.getStor pre ca))
        (Stor.rest (Devm.getStor callPre ca)))
      (burn : BurnCallPrefix e ownPre callPre guardPost owner amount target)
      (trace : Nonempty
        (AcceptedValueCallTrace e target amount callPre guardPost))
      (suffix : Stor.Weth10Silent
        (Devm.getStor guardPost ca) (Devm.getStor post ca))
  | tokenCallback (kind : LocalSegmentKind) (callbackPre : Devm)
      (target : Adr) (rawTarget sel value tailLen inputSize : B256)
      (tail input : Bytes)
      (segment : LocalActionSegment kind action
        (Stor.rest (Devm.getStor pre ca))
        (Stor.rest (Devm.getStor callbackPre ca)))
      (callbackCode : callbackPre.getCode ca = pre.getCode ca)
      (callback : RetainedTokenCallbackBoundary dp e e.currentTarget
        target rawTarget sel value tailLen inputSize tail input
        callbackPre post)
  | redemptionThenTokenCallback
      (callPre callbackPre : Devm) (owner : Adr) (amount target : B256)
      (callbackTarget : Adr) (rawTarget sel callbackValue tailLen inputSize : B256)
      (tail input : Bytes)
      (segment : LocalActionSegment .redemption action
        (Stor.rest (Devm.getStor pre ca))
        (Stor.rest (Devm.getStor callPre ca)))
      (burn : BurnCallPrefix e pre callPre callbackPre owner amount target)
      (valueTrace : Nonempty
        (AcceptedValueCallTrace e target amount callPre callbackPre))
      (callback : RetainedTokenCallbackBoundary dp e e.currentTarget
        callbackTarget rawTarget sel callbackValue tailLen inputSize tail
        input callbackPre post)
  | flash (creditPost callbackPost settlePre debitPre : Devm)
      (rawReceiver : B256) (receiver : Adr) (amount : B256)
      (credit : LocalActionSegment .flashCredit action
        (Stor.rest (Devm.getStor pre ca))
        (Stor.rest (Devm.getStor creditPost ca)))
      (creditCode : creditPost.getCode ca = pre.getCode ca)
      (callback : RetainedFlashCallbackBoundary e e.currentTarget receiver
        amount (flashCallbackRuntimeSize e) (flashCallbackRuntimeInput e)
        creditPost callbackPost)
      (callbackToSettle : Devm.getStor callbackPost = Devm.getStor settlePre)
      (settlement : Func.Run ((weth10 dp).main :: weth10Aux) e
        settlePre flashSettle post)
      (settleToDebit : Stor.Weth10Silent
        (Devm.getStor settlePre ca) (Devm.getStor debitPre ca))
      (repayment : LocalActionSegment .flashRepayment action
        (Stor.rest (Devm.getStor debitPre ca))
        (Stor.rest (Devm.getStor post ca)))
      (burnRun : Func.Run ((weth10 dp).main :: weth10Aux) e
        debitPre flashBurn post)

/-- Rich operational storage evidence paired with the exact authentic frame
classification that selected the action. -/
structure Exec.Frame.HasRichLocalStorageEffect (dp : DeployParams)
    (ca : Adr) (frame : Exec.Frame) (action : FlowAction) : Prop where
  authentic : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame
  classified : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action
  effect : RichLocalStorageEffect dp ca frame.sevm frame.pre frame.post action

/-- Proper-descendant labels of one retained frame, excluding its own
classification.  This is kept frame-indexed so later callback occurrence
witnesses can identify the exact child derivations contributing each suffix. -/
def Exec.Frame.descendantFlowActions (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) : List FlowAction :=
  (Exec.descendantFrames frame.run).filterMap
    (Blanc.Weth10.Exec.Frame.flowAction? dp ca)

/-- Proper-descendant labels for an arbitrary proof-indexed execution. -/
def Exec.Deriv.descendantFlowActions (dp : DeployParams) (ca : Adr)
    (deriv : Exec.Deriv) : List FlowAction :=
  (Exec.descendantFrames deriv.exc).filterMap
    (Blanc.Weth10.Exec.Frame.flowAction? dp ca)

/-- One same-frame continuation edge, labelled by exactly the retained child
actions crossed by that edge.  Child-derivation edges are intentionally not
constructors: this relation follows the enclosing frame chronologically. -/
inductive Exec.Deriv.ParentStepActions (dp : DeployParams) (ca : Adr) :
    Exec.Deriv → Exec.Deriv → List FlowAction → Prop
  | cont
      {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
      (next : Exec pc' sevm post out) :
      ParentStepActions dp ca
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .cont hstep next⟩ []
  | doneOk
      {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {f : Jaune.Frame} {rsm : Resume}
      {r : Except (EvmError × State × AdrSet × Tra) Devm}
      {out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
      (henter : f.enter = .done r)
      (hresume : rsm.run r = .ok post)
      (next : Exec pc' sevm post out) :
      ParentStepActions dp ca
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .doneOk hstep henter hresume next⟩ []
  | runOk
      {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {f : Jaune.Frame} {rsm : Resume} {childEvm : Evm}
      {raw out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
      (henter : f.enter = .run childEvm)
      (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (hresume : rsm.run (f.settle raw) = .ok post)
      (next : Exec pc' sevm post out) :
      ParentStepActions dp ca
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out,
          .runOk hstep henter child hresume next⟩
        (if Blanc.Frame.settlementCommits f raw = true then
          Exec.flowActions dp ca child
         else [])

/-- Forget the WETH action label while preserving the exact same-frame
continuation edge and its recursive child proof. -/
theorem Exec.Deriv.ParentStepActions.toParentStep
    {dp : DeployParams} {ca : Adr}
    {next root : Exec.Deriv} {actions : List FlowAction}
    (edge : Exec.Deriv.ParentStepActions dp ca next root actions) :
    Blanc.Exec.Deriv.ParentStep next root := by
  cases edge with
  | cont hstep next => exact .cont hstep next
  | doneOk hstep henter hresume next =>
      exact .doneOk hstep henter hresume next
  | runOk hstep henter child hresume next =>
      exact .runOk hstep henter child hresume next

/-- A chronological same-frame prefix, labelled by all retained child action
lists crossed before its endpoint. -/
inductive Exec.Deriv.ParentPrefixActions (dp : DeployParams) (ca : Adr) :
    Exec.Deriv → Exec.Deriv → List FlowAction → Prop
  | refl (root : Exec.Deriv) : ParentPrefixActions dp ca root root []
  | step {root next tail : Exec.Deriv}
      {headActions tailActions : List FlowAction}
      (head : Exec.Deriv.ParentStepActions dp ca next root headActions)
      (rest : Exec.Deriv.ParentPrefixActions dp ca next tail tailActions) :
      Exec.Deriv.ParentPrefixActions dp ca root tail
        (headActions ++ tailActions)

/-- Forget the accumulated WETH action labels while preserving the exact
same-frame prefix. -/
theorem Exec.Deriv.ParentPrefixActions.toParentPrefix
    {dp : DeployParams} {ca : Adr}
    {root tail : Exec.Deriv} {actions : List FlowAction}
    (path : Exec.Deriv.ParentPrefixActions dp ca root tail actions) :
    Blanc.Exec.Deriv.ParentPrefix root tail := by
  induction path with
  | refl => exact .refl _
  | step head rest ih => exact .step head.toParentStep ih

/-- One labelled parent-continuation edge is exactly the corresponding split
of proper-descendant actions. -/
theorem Exec.Deriv.ParentStepActions.descendantFlowActions_eq
    {dp : DeployParams} {ca : Adr}
    {next root : Exec.Deriv} {actions : List FlowAction}
    (edge : Exec.Deriv.ParentStepActions dp ca next root actions) :
    Exec.Deriv.descendantFlowActions dp ca root =
      actions ++ Exec.Deriv.descendantFlowActions dp ca next := by
  cases edge with
  | cont =>
      simp [Exec.Deriv.descendantFlowActions, Exec.descendantFrames]
  | doneOk =>
      simp [Exec.Deriv.descendantFlowActions, Exec.descendantFrames]
  | runOk hstep henter child hresume next =>
      simp only [Exec.Deriv.descendantFlowActions,
        Exec.descendantFrames]
      split <;> rename_i hcommit
      · have hraw :=
          Blanc.Frame.raw_commits_of_settlementCommits hcommit
        simp [Exec.flowActions, Exec.committedFrames, hraw]
        rw [← List.cons_append, List.filterMap_append]
      · simp

/-- The weighted prefix relation accounts for every successful spawn before
its endpoint and leaves exactly that endpoint's remaining descendants. -/
theorem Exec.Deriv.ParentPrefixActions.descendantFlowActions_eq
    {dp : DeployParams} {ca : Adr}
    {root tail : Exec.Deriv} {actions : List FlowAction}
    (hprefix : Exec.Deriv.ParentPrefixActions dp ca root tail actions) :
    Exec.Deriv.descendantFlowActions dp ca root =
      actions ++ Exec.Deriv.descendantFlowActions dp ca tail := by
  induction hprefix with
  | refl => simp
  | step head rest ih =>
      rw [head.descendantFlowActions_eq, ih, List.append_assoc]

/-- Chronological prefixes compose without losing the child-list order. -/
theorem Exec.Deriv.ParentPrefixActions.trans
    {dp : DeployParams} {ca : Adr}
    {root mid tail : Exec.Deriv} {left right : List FlowAction}
    (hleft : Exec.Deriv.ParentPrefixActions dp ca root mid left)
    (hright : Exec.Deriv.ParentPrefixActions dp ca mid tail right) :
    Exec.Deriv.ParentPrefixActions dp ca root tail (left ++ right) := by
  induction hleft with
  | refl => simpa using hright
  | step head rest ih =>
      simpa only [List.append_assoc] using
        Exec.Deriv.ParentPrefixActions.step head (ih hright)

/-- Append one exact parent-continuation edge to a chronological prefix. -/
theorem Exec.Deriv.ParentPrefixActions.snoc
    {dp : DeployParams} {ca : Adr}
    {root current next : Exec.Deriv} {before selected : List FlowAction}
    (hprefix : Exec.Deriv.ParentPrefixActions dp ca root current before)
    (hedge : Exec.Deriv.ParentStepActions dp ca next current selected) :
    Exec.Deriv.ParentPrefixActions dp ca root next
      (before ++ selected) := by
  apply hprefix.trans
  simpa using Exec.Deriv.ParentPrefixActions.step hedge
    (Exec.Deriv.ParentPrefixActions.refl next)

/-- The non-circular root/descendant ledger split for a classified retained
frame.  Unlike an endpoint-only effect, this equation is indexed by the
frame's concrete `Exec` proof. -/
structure Exec.Frame.ClassifiedActionLedger (dp : DeployParams)
    (ca : Adr) (frame : Exec.Frame) (action : FlowAction) : Prop where
  rich : Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action
  actions_eq : Exec.flowActions dp ca frame.run =
    action :: Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame

/-- An executed nonterminal instruction together with its exact continuation
inside the retained frame's original `Exec` derivation.  For a spawning slot,
`xl` retains the same concrete child proof used by the parent step. -/
def Exec.Frame.NinstOccurrence (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame)
    (n : Ninst) (stepPre stepPost : Devm) (xl : Xlot) : Prop :=
  ∃ (pc : Nat)
      (current : Exec pc frame.sevm stepPre frame.out)
      (continuation : Exec (pc + n.size) frame.sevm stepPost frame.out)
      (before selected : List FlowAction),
    Exec.Deriv.ParentPrefixActions dp ca
      ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ before ∧
    Ninst.At frame.sevm.code pc n ∧
    Xlot.Filled xl ∧
    Ninst.StepRun pc frame.sevm stepPre n xl (.ok stepPost) ∧
    Exec.Deriv.Prec
      ⟨pc + n.size, frame.sevm, stepPost, frame.out, continuation⟩
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ ∧
    Exec.Deriv.ParentStepActions dp ca
      ⟨pc + n.size, frame.sevm, stepPost, frame.out, continuation⟩
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ selected

/-- Erase the WETH action chronology from an occurrence while preserving its
exact proof-indexed node, program counter, machine states, decoded
instruction, recursive slot, and step result. -/
theorem Exec.Frame.NinstOccurrence.toCommon
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {n : Ninst} {stepPre stepPost : Devm} {xl : Xlot}
    (occurrence : Blanc.Weth10.Exec.Frame.NinstOccurrence
      dp ca frame n stepPre stepPost xl) :
    ∃ (pc : Nat)
        (current : Exec pc frame.sevm stepPre frame.out)
        (common : Blanc.Exec.NinstOccurrence
          (Blanc.Exec.Frame.rootDeriv frame)),
      common.node =
          (⟨pc, frame.sevm, stepPre, frame.out, current⟩ : Blanc.Exec.Deriv) ∧
      common.instruction = n ∧
      common.slot = xl ∧
      common.stepResult = .ok stepPost := by
  rcases occurrence with
    ⟨pc, current, continuation, before, selected, path, decoded,
      filled, stepRun, prec, edge⟩
  have neutralPrefix := path.toParentPrefix
  rcases neutralPrefix.rawNodes_decomposition with
    ⟨earlier, decomposition⟩
  refine ⟨pc, current,
    { node := ⟨pc, frame.sevm, stepPre, frame.out, current⟩
      instruction := n
      slot := xl
      stepResult := .ok stepPost
      reached := ?_
      decoded := decoded
      filled := filled
      stepRun := stepRun }, rfl, rfl, rfl, rfl⟩
  change
    (⟨pc, frame.sevm, stepPre, frame.out, current⟩ : Blanc.Exec.Deriv) ∈
      (⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩ :
        Blanc.Exec.Deriv).exc.rawNodes
  rw [decomposition]
  exact List.mem_append.mpr (Or.inr (Blanc.Exec.mem_rawNodes_self current))

/-- An instruction occurrence exposes the exact chronological split of the
enclosing frame's proper-descendant ledger: all earlier settled children,
the selected instruction's settled child (or `[]`), then the continuation. -/
theorem Exec.Frame.NinstOccurrence.chronological_descendantFlowActions
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {n : Ninst} {stepPre stepPost : Devm} {xl : Xlot}
    (occurrence : Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame n stepPre stepPost xl) :
    ∃ (pc : Nat)
        (current : Exec pc frame.sevm stepPre frame.out)
        (continuation : Exec (pc + n.size) frame.sevm stepPost frame.out)
        (before selected : List FlowAction),
      Exec.Deriv.ParentPrefixActions dp ca
        ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
        ⟨pc, frame.sevm, stepPre, frame.out, current⟩ before ∧
      Ninst.At frame.sevm.code pc n ∧
      Xlot.Filled xl ∧
      Ninst.StepRun pc frame.sevm stepPre n xl (.ok stepPost) ∧
      Exec.Deriv.Prec
        ⟨pc + n.size, frame.sevm, stepPost, frame.out, continuation⟩
        ⟨pc, frame.sevm, stepPre, frame.out, current⟩ ∧
      Exec.Deriv.ParentStepActions dp ca
        ⟨pc + n.size, frame.sevm, stepPost, frame.out, continuation⟩
        ⟨pc, frame.sevm, stepPre, frame.out, current⟩ selected ∧
      Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame =
        before ++ selected ++
          Exec.Deriv.descendantFlowActions dp ca
            ⟨pc + n.size, frame.sevm, stepPost, frame.out, continuation⟩ := by
  rcases occurrence with
    ⟨pc, current, continuation, before, selected, hprefix, hat,
      hfilled, hstep, hprec, hedge⟩
  refine ⟨pc, current, continuation, before, selected, hprefix, hat,
    hfilled, hstep, hprec, hedge, ?_⟩
  have hp := hprefix.descendantFlowActions_eq
  have hs := hedge.descendantFlowActions_eq
  change Exec.Deriv.descendantFlowActions dp ca
    ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩ = _
  rw [hp, hs, List.append_assoc]

/-- Combine a classified root label with an occurrence's chronological
proper-descendant split. -/
theorem Exec.Frame.ClassifiedActionLedger.flowActions_eq_chronological
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (ledger : Blanc.Weth10.Exec.Frame.ClassifiedActionLedger dp ca frame action)
    {before selected suffix : List FlowAction}
    (hdesc : Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame =
      before ++ selected ++ suffix) :
    Exec.flowActions dp ca frame.run =
      action :: (before ++ selected ++ suffix) := by
  rw [ledger.actions_eq, hdesc]

/-- Locating a nonterminal instruction on the original same-frame execution
path constructs a rich occurrence with the *same* recursive slot and child
proof used by that `Exec` step. -/
theorem Exec.Frame.exists_ninstOccurrence_of_parentPrefix
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {pc : Nat} {stepPre : Devm} {n : Ninst}
    {before : List FlowAction}
    (current : Exec pc frame.sevm stepPre frame.out)
    (hprefix : Exec.Deriv.ParentPrefixActions dp ca
      ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ before)
    (hat : Ninst.At frame.sevm.code pc n) :
    ∃ (stepPost : Devm) (xl : Xlot),
      Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame n stepPre stepPost xl := by
  rcases frame with ⟨rootPc, sevm, rootPre, out, rootRun, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok final =>
      have hstepEq : Evm.step ⟨pc, sevm, stepPre⟩ =
          Ninst.step ⟨pc, sevm, stepPre⟩ n :=
        Evm.step_next hat
      cases current with
      | halt h =>
          exact (Ninst.step_ne_halt_ok (hstepEq.symm.trans h)).elim
      | cont h next =>
          rename_i pc' stepPost
          have hs := hstepEq.symm.trans h
          cases Ninst.step_cont_pc hs
          have hrun : Ninst.StepRun pc sevm stepPre n .none
              (.ok stepPost) := by
            simp only [Ninst.StepRun, hs, Step.Run]
            exact ⟨trivial, trivial⟩
          refine ⟨_, .none, pc, .cont h next, next, before, [],
            hprefix, hat, trivial, hrun, .cont h next, .cont h next⟩
      | doneOk h henter hresume next =>
          rename_i f rsm pc' r stepPost
          have hs := hstepEq.symm.trans h
          cases Ninst.step_spawn_pc hs
          have hrun : Ninst.StepRun pc sevm stepPre n .none
              (.ok stepPost) := by
            simp only [Ninst.StepRun, hs, Step.Run]
            exact ⟨_, RunFrame.of_done henter, hresume.symm⟩
          refine ⟨_, .none, pc, .doneOk h henter hresume next, next,
            before, [], hprefix, hat, trivial, hrun,
            .doneOk h henter hresume next,
            .doneOk h henter hresume next⟩
      | runOk h henter child hresume next =>
          rename_i f rsm pc' childEvm raw stepPost
          have hs := hstepEq.symm.trans h
          cases Ninst.step_spawn_pc hs
          have hrun : Ninst.StepRun pc sevm stepPre n
              (.some ⟨childEvm, raw⟩) (.ok stepPost) := by
            simp only [Ninst.StepRun, hs, Step.Run]
            exact ⟨_, RunFrame.of_run henter, hresume.symm⟩
          refine ⟨stepPost, .some ⟨childEvm, raw⟩, pc,
            .runOk h henter child hresume next, next, before, _, hprefix,
            hat, ⟨child⟩, hrun, .runOkCont h henter child hresume next,
            .runOk h henter child hresume next⟩

/-- Slot and outcome uniqueness for a pc-free external instruction, allowing
the two witnesses to name different program counters. -/
theorem Ninst.StepRun.unique_exec_of_filled
    {pc₁ pc₂ : Nat} {sevm : Sevm} {pre : Devm} {x : Xinst}
    {left right : Xlot} {out₁ out₂ : Execution}
    (hleftFilled : Xlot.Filled left)
    (hrightFilled : Xlot.Filled right)
    (hleft : Ninst.StepRun pc₁ sevm pre (.exec x) left out₁)
    (hright : Ninst.StepRun pc₂ sevm pre (.exec x) right out₂) :
    left = right ∧ out₁ = out₂ := by
  have hright' : Ninst.StepRun pc₁ sevm pre (.exec x) right out₂ :=
    Ninst.stepRun_pc_irrel (by simp [Ninst.pcFree]) hright
  unfold Ninst.StepRun at hleft hright'
  exact Blanc.Step.Run.unique_of_filled
    hleftFilled hrightFilled hleft hright'

/-- Advance one generated `.next` node while keeping the exact slot chosen by
the gas-exact compiled derivation.  The returned cursor is the original
frame's continuation after the selected instruction, labelled by the settled
child actions crossed at that instruction. -/
theorem Exec.Frame.advance_runCompiled_next
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {pc : Nat} {stepPre stepPost : Devm} {n : Ninst}
    {before : List FlowAction}
    (current : Exec pc frame.sevm stepPre frame.out)
    (hprefix : Exec.Deriv.ParentPrefixActions dp ca
      ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ before)
    (hat : Ninst.At frame.sevm.code pc n)
    (compiled : Ninst.RunCompiled frame.sevm stepPre n stepPost) :
    ∃ (xl : Xlot)
        (continuation : Exec (pc + n.size) frame.sevm stepPost frame.out)
        (selected : List FlowAction),
      Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame n stepPre stepPost xl ∧
      Exec.Deriv.ParentStepActions dp ca
        ⟨pc + n.size, frame.sevm, stepPost, frame.out, continuation⟩
        ⟨pc, frame.sevm, stepPre, frame.out, current⟩ selected ∧
      Exec.Deriv.ParentPrefixActions dp ca
        ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
        ⟨pc + n.size, frame.sevm, stepPost, frame.out, continuation⟩
        (before ++ selected) := by
  rcases frame with ⟨rootPc, sevm, rootPre, out, rootRun, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok final =>
      rcases compiled with ⟨xl, hfilled, hcompiled⟩
      have hstepEq : Evm.step ⟨pc, sevm, stepPre⟩ =
          Ninst.step ⟨pc, sevm, stepPre⟩ n :=
        Evm.step_next hat
      cases current with
      | halt h =>
          exact (Ninst.step_ne_halt_ok (hstepEq.symm.trans h)).elim
      | cont h next =>
          rename_i pc' actualPost
          have hs := hstepEq.symm.trans h
          have hc := hcompiled pc
          simp only [Ninst.StepRun, hs, Step.Run] at hc
          rcases hc with ⟨hxl, hpost⟩
          subst xl
          cases hpost
          cases Ninst.step_cont_pc hs
          let edge : Exec.Deriv.ParentStepActions dp ca
              ⟨pc + n.size, sevm, stepPost, .ok final, next⟩
              ⟨pc, sevm, stepPre, .ok final, .cont h next⟩ [] :=
            .cont h next
          refine ⟨.none, next, [], ?_, edge, hprefix.snoc edge⟩
          exact ⟨pc, .cont h next, next, before, [], hprefix, hat,
            trivial, hcompiled pc, .cont h next, edge⟩
      | doneOk h henter hresume next =>
          rename_i f rsm pc' r actualPost
          have hs := hstepEq.symm.trans h
          have hc := hcompiled pc
          simp only [Ninst.StepRun, hs, Step.Run] at hc
          rcases hc with ⟨r', hframe, hout⟩
          unfold RunFrame at hframe
          rw [henter] at hframe
          rcases hframe with ⟨hxl, hr⟩
          subst xl
          subst r'
          rw [hresume] at hout
          cases hout
          cases Ninst.step_spawn_pc hs
          let edge : Exec.Deriv.ParentStepActions dp ca
              ⟨pc + n.size, sevm, stepPost, .ok final, next⟩
              ⟨pc, sevm, stepPre, .ok final,
                .doneOk h henter hresume next⟩ [] :=
            .doneOk h henter hresume next
          refine ⟨.none, next, [], ?_, edge, hprefix.snoc edge⟩
          exact ⟨pc, .doneOk h henter hresume next, next, before, [],
            hprefix, hat, trivial, hcompiled pc,
            .doneOk h henter hresume next, edge⟩
      | runOk h henter child hresume next =>
          rename_i f rsm pc' childEvm raw actualPost
          have hs := hstepEq.symm.trans h
          have hc := hcompiled pc
          simp only [Ninst.StepRun, hs, Step.Run] at hc
          rcases hc with ⟨r', hframe, hout⟩
          unfold RunFrame at hframe
          rw [henter] at hframe
          rcases hframe with ⟨compiledRaw, hxl, hr⟩
          subst xl
          subst r'
          obtain ⟨compiledChild⟩ := hfilled
          have hraw : compiledRaw = raw := by
            have hc' := (exec_iff_exec_eq childEvm.pc childEvm.sta
              childEvm.dyna compiledRaw).mp ⟨compiledChild⟩
            have ha' := (exec_iff_exec_eq childEvm.pc childEvm.sta
              childEvm.dyna raw).mp ⟨child⟩
            exact hc'.symm.trans ha'
          subst compiledRaw
          rw [hresume] at hout
          cases hout
          cases Ninst.step_spawn_pc hs
          let selected :=
            if Blanc.Frame.settlementCommits f raw = true then
              Exec.flowActions dp ca child
            else []
          let edge : Exec.Deriv.ParentStepActions dp ca
              ⟨pc + n.size, sevm, stepPost, .ok final, next⟩
              ⟨pc, sevm, stepPre, .ok final,
                .runOk h henter child hresume next⟩ selected :=
            .runOk h henter child hresume next
          refine ⟨.some ⟨childEvm, raw⟩, next, selected, ?_, edge,
            hprefix.snoc edge⟩
          exact ⟨pc, .runOk h henter child hresume next, next, before,
            selected, hprefix, hat, ⟨child⟩, hcompiled pc,
            .runOkCont h henter child hresume next, edge⟩

/-- The first instruction of a compiled `.next` block is installed at the
block's starting program counter. -/
theorem ninstAt_of_subcode_next
    {code : ByteArray} {table : List (Nat × Func)} {pc : Nat}
    {n : Ninst} {tail : Func}
    (sub : subcode code.toList pc
      (Func.compile table pc (.next n tail))) :
    Ninst.At code pc n := by
  rcases of_subcode sub with ⟨cd, hcode, hslice⟩
  rcases of_bind_eq_some hcode with ⟨rest, hrest, hprefix⟩
  simp [pure] at hprefix
  rw [← hprefix] at hslice
  exact Ninst.at_of_slice (List.slice_prefix hslice)

/-- Follow one known childless machine continuation in the original frame.
Hidden compiler instructions (`PUSH2`, `JUMP[I]`, and `JUMPDEST`) use this
edge, so they contribute no child actions to the chronological prefix. -/
theorem Exec.Frame.advance_cont
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {pc nextPc : Nat} {stepPre nextPre : Devm}
    {before : List FlowAction}
    (current : Exec pc frame.sevm stepPre frame.out)
    (hprefix : Exec.Deriv.ParentPrefixActions dp ca
      ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ before)
    (hstep : Evm.step ⟨pc, frame.sevm, stepPre⟩ =
      .cont nextPc nextPre) :
    ∃ continuation : Exec nextPc frame.sevm nextPre frame.out,
      Exec.Deriv.ParentPrefixActions dp ca
        ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
        ⟨nextPc, frame.sevm, nextPre, frame.out, continuation⟩ before := by
  rcases frame with ⟨rootPc, sevm, rootPre, out, rootRun, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok final =>
      cases current with
      | halt h => cases hstep.symm.trans h
      | cont h next =>
          cases hstep.symm.trans h
          refine ⟨next, ?_⟩
          simpa using hprefix.snoc
            (Exec.Deriv.ParentStepActions.cont hstep next)
      | doneOk h henter hresume next => cases hstep.symm.trans h
      | runOk h henter child hresume next => cases hstep.symm.trans h

/-- Peel an executed source `Line` from a gas-exact compiled body while
threading the original frame cursor.  Besides the residual compiled run and
code slice, the result records the exact chronological child-action lists of
every spawning instruction in the peeled line. -/
theorem Exec.Frame.advance_runCompiled_prepend
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {line : Line} {tail : Func} {pc : Nat}
    {stepPre final : Devm} {before : List FlowAction}
    (current : Exec pc frame.sevm stepPre frame.out)
    (hprefix : Exec.Deriv.ParentPrefixActions dp ca
      ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ before)
    (compiled : Func.RunCompiled fs frame.sevm stepPre
      (line +++ tail) final)
    (sub : subcode frame.sevm.code.toList pc
      (Func.compile table pc (line +++ tail)))
    (boundary : noPushBefore frame.sevm.code pc 32 = true) :
    ∃ (tailPc : Nat) (tailPre : Devm)
        (tailExec : Exec tailPc frame.sevm tailPre frame.out)
        (crossed : List FlowAction),
      Exec.Deriv.ParentPrefixActions dp ca
        ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
        ⟨tailPc, frame.sevm, tailPre, frame.out, tailExec⟩
        (before ++ crossed) ∧
      Line.Run frame.sevm stepPre line tailPre ∧
      Func.RunCompiled fs frame.sevm tailPre tail final ∧
      subcode frame.sevm.code.toList tailPc
        (Func.compile table tailPc tail) ∧
      noPushBefore frame.sevm.code tailPc 32 = true := by
  induction line generalizing pc stepPre before with
  | nil =>
      exact ⟨pc, stepPre, current, [], by simpa using hprefix,
        .nil, compiled, sub, boundary⟩
  | cons n line ih =>
      change Func.RunCompiled fs frame.sevm stepPre
        (.next n (line +++ tail)) final at compiled
      cases compiled with
      | next hcompiled htail =>
          have hat : Ninst.At frame.sevm.code pc n :=
            ninstAt_of_subcode_next sub
          rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_next (frame := frame) current hprefix hat
              hcompiled with
            ⟨xl, continuation, selected, occurrence, hedge, hnextPrefix⟩
          obtain ⟨nextBoundary, nextSub⟩ :=
            Func.noPushBefore_next sub boundary
          rcases ih continuation hnextPrefix htail nextSub nextBoundary with
            ⟨tailPc, tailPre, tailExec, crossed, htailPrefix, hline,
              htailRun, htailSub, htailBoundary⟩
          refine ⟨tailPc, tailPre, tailExec, selected ++ crossed, ?_,
            .cons (Ninst.Run.of_runCompiled hcompiled) hline,
            htailRun, htailSub, htailBoundary⟩
          simpa only [List.append_assoc] using htailPrefix

/-- Follow the selected arm of one compiled source branch in the original
frame.  The disjunction reflects the executed stack flag: the left result is
the fall-through (`zero`) arm and the right result is the jumped (`succ`) arm.
All hidden compiler steps are childless, so the incoming action prefix is
preserved exactly. -/
theorem Exec.Frame.advance_runCompiled_branch
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {pc : Nat} {stepPre final : Devm}
    {before : List FlowAction}
    (current : Exec pc frame.sevm stepPre frame.out)
    (hprefix : Exec.Deriv.ParentPrefixActions dp ca
      ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ before)
    (compiled : Func.RunCompiled fs frame.sevm stepPre
      (.branch left right) final)
    (sub : subcode frame.sevm.code.toList pc
      (Func.compile table pc (.branch left right)))
    (boundary : noPushBefore frame.sevm.code pc 32 = true) :
    (∃ (armPc : Nat) (armPre : Devm)
        (armExec : Exec armPc frame.sevm armPre frame.out),
      Exec.Deriv.ParentPrefixActions dp ca
        ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
        ⟨armPc, frame.sevm, armPre, frame.out, armExec⟩ before ∧
      Func.RunCompiled fs frame.sevm armPre left final ∧
      subcode frame.sevm.code.toList armPc
        (Func.compile table armPc left) ∧
      noPushBefore frame.sevm.code armPc 32 = true) ∨
    (∃ (armPc : Nat) (armPre : Devm)
        (armExec : Exec armPc frame.sevm armPre frame.out),
      Exec.Deriv.ParentPrefixActions dp ca
        ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
        ⟨armPc, frame.sevm, armPre, frame.out, armExec⟩ before ∧
      Func.RunCompiled fs frame.sevm armPre right final ∧
      subcode frame.sevm.code.toList armPc
        (Func.compile table armPc right) ∧
      noPushBefore frame.sevm.code armPc 32 = true) := by
  rcases subcode_compile_branch_jumpable sub boundary with
    ⟨loc, hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  cases compiled with
  | zero hroom hpop hleft =>
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) current hprefix hstepPush with
        ⟨afterPush, hpPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hpPush hstepJumpi with
        ⟨armExec, hpArm⟩
      exact Or.inl ⟨pc + 4, _, armExec, hpArm, hleft,
        hsubLeft, hboundLeft⟩
  | succ hne hroom hpop hright =>
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) current hprefix hstepPush with
        ⟨afterPush, hpPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hpPush hstepJumpi with
        ⟨afterJump, hpJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterJump hpJump hstepJumpdest with
        ⟨armExec, hpArm⟩
      exact Or.inr ⟨loc + 1, _, armExec, hpArm, hright,
        hsubRight, hboundRight⟩

/-- A source-function cursor tied to the original retained frame execution.
The code slice and `noPushBefore` boundary make the cursor compositional
through generated branches and internal table calls; `actions` is the exact
chronological list of settled children crossed before the cursor. -/
structure Exec.Frame.CompiledCursor (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) (fs : List Func) (table : List (Nat × Func))
    (body : Func) (final : Devm) : Type where
  pc : Nat
  pre : Devm
  current : Exec pc frame.sevm pre frame.out
  actions : List FlowAction
  parentPrefix : Exec.Deriv.ParentPrefixActions dp ca
    ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
    ⟨pc, frame.sevm, pre, frame.out, current⟩ actions
  run : Func.RunCompiled fs frame.sevm pre body final
  codeSlice : subcode frame.sevm.code.toList pc
    (Func.compile table pc body)
  codeBoundary : noPushBefore frame.sevm.code pc 32 = true

/-- The observations preserved by generated entry and dispatch code. -/
structure Devm.DispatchSilent (pre post : Devm) : Prop where
  state : pre.state = post.state
  memory : pre.memory = post.memory
  logs : pre.logs = post.logs
  output : pre.output = post.output

theorem Devm.DispatchSilent.refl (pre : Devm) :
    Devm.DispatchSilent pre pre :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem Devm.DispatchSilent.trans
    {pre mid post : Devm}
    (h₁ : Devm.DispatchSilent pre mid)
    (h₂ : Devm.DispatchSilent mid post) :
    Devm.DispatchSilent pre post :=
  ⟨h₁.state.trans h₂.state, h₁.memory.trans h₂.memory,
    h₁.logs.trans h₂.logs, h₁.output.trans h₂.output⟩

theorem Devm.DispatchSilent.of_popBurnBy
    {words : List B256} {cost : Nat} {pre post : Devm}
    (h : Devm.PopBurnBy words cost pre post) :
    Devm.DispatchSilent pre post :=
  ⟨h.state, h.memory, h.logs, h.output⟩

theorem Devm.DispatchSilent.of_burnBy
    {cost : Nat} {pre post : Devm}
    (h : Devm.BurnBy cost pre post) : Devm.DispatchSilent pre post :=
  ⟨h.state, h.memory, h.logs, h.output⟩

theorem Devm.DispatchSilent.of_line
    {e : Sevm} {pre post : Devm} {line : Line}
    (hstate : Line.Inv Devm.state line)
    (hmemory : Line.Inv Devm.memory line)
    (hlogs : Line.Inv Devm.logs line)
    (houtput : Line.Inv Devm.output line)
    (run : Line.Run e pre line post) : Devm.DispatchSilent pre post :=
  ⟨Line.of_inv Devm.state hstate run,
    Line.of_inv Devm.memory hmemory run,
    Line.of_inv Devm.logs hlogs run,
    Line.of_inv Devm.output houtput run⟩

theorem Devm.DispatchSilent.of_pushEq
    {e : Sevm} {pre post : Devm} {word : B256}
    (run : Line.Run e pre [Ninst.pushB256 word, Ninst.eq] post) :
    Devm.DispatchSilent pre post := by
  rcases Line.of_run_cons run with ⟨mid, hpush, rest⟩
  rcases Line.of_run_cons rest with ⟨last, heq, hnil⟩
  cases hnil
  have hburn := of_run_pushB256 hpush
  rcases of_run_reg heq with ⟨pc, heqCore⟩
  simp only [Rinst.run, Rinst.runCore] at heqCore
  obtain ⟨left, right, heqBurn⟩ :=
    Devm.diffBurn_of_applyBinary heqCore
  exact ⟨Line.of_inv Devm.state (by line_inv) run,
    Line.of_inv Devm.memory (by line_inv) run,
    hburn.logs.trans heqBurn.logs,
    hburn.output.trans heqBurn.output⟩

theorem Devm.DispatchSilent.of_dupPushGt
    {e : Sevm} {pre post : Devm} {word : B256}
    (run : Line.Run e pre
      [Ninst.dup 0, Ninst.pushB256 word, Ninst.gt] post) :
    Devm.DispatchSilent pre post := by
  rcases Line.of_run_cons run with ⟨afterDup, hdup, restDup⟩
  rcases Line.of_run_cons restDup with ⟨afterPush, hpush, restPush⟩
  rcases Line.of_run_cons restPush with ⟨last, hgt, hnil⟩
  cases hnil
  rcases of_run_dup hdup with ⟨value, _hvalue, hdupBurn⟩
  have hpushBurn := of_run_pushB256 hpush
  rcases of_run_reg hgt with ⟨pc, hgtCore⟩
  simp only [Rinst.run, Rinst.runCore] at hgtCore
  obtain ⟨left, right, hgtBurn⟩ :=
    Devm.diffBurn_of_applyBinary hgtCore
  exact ⟨Line.of_inv Devm.state (by line_inv) run,
    Line.of_inv Devm.memory (by line_inv) run,
    hdupBurn.logs.trans (hpushBurn.logs.trans hgtBurn.logs),
    hdupBurn.output.trans (hpushBurn.output.trans hgtBurn.output)⟩

theorem Devm.DispatchSilent.of_entryFlag
    {e : Sevm} {pre post : Devm}
    (run : Line.Run e pre [Ninst.calldatasize, Ninst.iszero] post) :
    Devm.DispatchSilent pre post := by
  rcases Line.of_run_cons run with ⟨mid, hsize, rest⟩
  rcases Line.of_run_cons rest with ⟨last, hzero, hnil⟩
  cases hnil
  exact ⟨(of_run_calldatasize hsize).state.trans
      (Ninst.Hinv.inv (f := Devm.state) hzero),
    Line.of_inv Devm.memory (by line_inv) run,
    (of_run_calldatasize hsize).logs.trans
      (Ninst.Hinv.inv (f := Devm.logs) hzero),
    (of_run_calldatasize hsize).output.trans
      (Ninst.Hinv.inv (f := Devm.output) hzero)⟩

theorem Devm.DispatchSilent.of_callvalueFlag
    {e : Sevm} {pre post : Devm}
    (run : Line.Run e pre [Ninst.callvalue, Ninst.iszero] post) :
    Devm.DispatchSilent pre post := by
  rcases Line.of_run_cons run with ⟨mid, hvalue, rest⟩
  rcases Line.of_run_cons rest with ⟨last, hzero, hnil⟩
  cases hnil
  exact ⟨(of_run_callvalue hvalue).state.trans
      (Ninst.Hinv.inv (f := Devm.state) hzero),
    Line.of_inv Devm.memory (by line_inv) run,
    (of_run_callvalue hvalue).logs.trans
      (Ninst.Hinv.inv (f := Devm.logs) hzero),
    (of_run_callvalue hvalue).output.trans
      (Ninst.Hinv.inv (f := Devm.output) hzero)⟩

theorem Devm.DispatchSilent.of_fsig
    {e : Sevm} {pre post : Devm}
    (run : Line.Run e pre fsig post) : Devm.DispatchSilent pre post := by
  unfold fsig cdl shiftRight at run
  rcases Line.of_run_cons run with ⟨s₁, q₁, run⟩
  rcases Line.of_run_cons run with ⟨s₂, q₂, run⟩
  rcases Line.of_run_cons run with ⟨s₃, q₃, run⟩
  rcases Line.of_run_cons run with ⟨last, q₄, hnil⟩
  cases hnil
  rcases of_run_reg q₄ with ⟨pc, hshrCore⟩
  simp only [Rinst.run, Rinst.runCore] at hshrCore
  obtain ⟨left, right, hshrBurn⟩ :=
    Devm.diffBurn_of_applyBinary hshrCore
  have hloadState : s₁.state = s₂.state := by
    rcases of_run_reg q₂ with ⟨loadPc, hloadCore⟩
    simp only [Rinst.run, Rinst.runCore] at hloadCore
    rcases Except.bind_eq_ok hloadCore with
      ⟨⟨offset, popped⟩, hpop, loadTail⟩
    rcases Except.bind_eq_ok loadTail with
      ⟨burned, hburn, hpush⟩
    exact (Devm.pop_of_pop hpop).state.trans
      ((Devm.burn_of_chargeGas hburn).state.trans
        (Devm.push_of_push hpush).state)
  exact ⟨(of_run_pushB256 q₁).state.trans
      (hloadState.trans
        ((of_run_pushB256 q₃).state.trans hshrBurn.state)),
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons q₁ (Line.Run.cons q₂
        (Line.Run.cons q₃ (Line.Run.cons q₄ Line.Run.nil)))),
    (of_run_pushB256 q₁).logs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) q₂).trans
        ((of_run_pushB256 q₃).logs.trans hshrBurn.logs)),
    (of_run_pushB256 q₁).output.trans
      ((Ninst.Hinv.inv (f := Devm.output) q₂).trans
        ((of_run_pushB256 q₃).output.trans hshrBurn.output))⟩

/-- Peel a source line at a proof-indexed compiled cursor. -/
theorem Exec.Frame.CompiledCursor.peelLine
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {line : Line} {tail : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table (line +++ tail) final) :
    ∃ tailCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table tail final,
      Line.Run frame.sevm cursor.pre line tailCursor.pre := by
  rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_prepend (frame := frame) cursor.current cursor.parentPrefix
      cursor.run cursor.codeSlice cursor.codeBoundary with
    ⟨tailPc, tailPre, tailExec, crossed, htailPrefix, hline,
      htailRun, htailSub, htailBoundary⟩
  let tailCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table tail final :=
    ⟨tailPc, tailPre, tailExec, cursor.actions ++ crossed, htailPrefix,
      htailRun, htailSub, htailBoundary⟩
  exact ⟨tailCursor, hline⟩

/-- Select the actual branch arm at a proof-indexed compiled cursor. -/
theorem Exec.Frame.CompiledCursor.selectBranch
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (.branch left right) final) :
    Nonempty (Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table left final) ∨
      Nonempty (Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table right final) := by
  rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_branch (frame := frame) cursor.current cursor.parentPrefix
      cursor.run cursor.codeSlice cursor.codeBoundary with hleft | hright
  · rcases hleft with
      ⟨armPc, armPre, armExec, hpArm, hrun, hsub, hbound⟩
    exact Or.inl ⟨⟨armPc, armPre, armExec, cursor.actions, hpArm,
      hrun, hsub, hbound⟩⟩
  · rcases hright with
      ⟨armPc, armPre, armExec, hpArm, hrun, hsub, hbound⟩
    exact Or.inr ⟨⟨armPc, armPre, armExec, cursor.actions, hpArm,
      hrun, hsub, hbound⟩⟩

/-- Select the actual branch arm and retain the definitional fact that hidden
compiler jumps cross no recursive child actions. -/
theorem Exec.Frame.CompiledCursor.selectBranchWithActions
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (.branch left right) final) :
    (∃ arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table left final,
      arm.actions = cursor.actions) ∨
    (∃ arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table right final,
      arm.actions = cursor.actions) := by
  rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_branch (frame := frame) cursor.current cursor.parentPrefix
      cursor.run cursor.codeSlice cursor.codeBoundary with hleft | hright
  · rcases hleft with
      ⟨armPc, armPre, armExec, hpArm, hrun, hsub, hbound⟩
    exact Or.inl ⟨⟨armPc, armPre, armExec, cursor.actions, hpArm,
      hrun, hsub, hbound⟩, rfl⟩
  · rcases hright with
      ⟨armPc, armPre, armExec, hpArm, hrun, hsub, hbound⟩
    exact Or.inr ⟨⟨armPc, armPre, armExec, cursor.actions, hpArm,
      hrun, hsub, hbound⟩, rfl⟩

/-- Select the fall-through arm when successful execution of the jumped arm
is impossible.  Besides the original-frame cursor, retain the exact compiled
branch pop/burn relation used by functional endpoint proofs. -/
theorem Exec.Frame.CompiledCursor.selectBranchLeftWithBurn
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (.branch left right) final)
    (hnoRight : ∀ pre, ¬ Func.Run fs frame.sevm pre right final) :
    ∃ arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table left final,
      Devm.PopBurnBy [0] (gVerylow + gHigh) cursor.pre arm.pre ∧
      arm.actions = cursor.actions := by
  have compiled := cursor.run
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      _hjumpdest, _hjumpable, _hsubRight, _hboundRight⟩
  cases compiled with
  | zero hroom hpop hleft =>
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hpPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hpPush hstepJumpi with
        ⟨armExec, hpArm⟩
      let arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table left final :=
        ⟨cursor.pc + 4, _, armExec, cursor.actions, hpArm,
          hleft, hsubLeft, hboundLeft⟩
      exact ⟨arm, hpop, rfl⟩
  | succ hne hroom hpop hright =>
      exact absurd (Func.Run.of_runCompiled hright) (hnoRight _)

/-- Select the fall-through arm when the compiled branch flag is known zero. -/
theorem Exec.Frame.CompiledCursor.selectBranchZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {stack : Stack}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (.branch left right) final)
    (hstack : (0 : B256) :: stack <<+ cursor.pre.stack) :
    ∃ arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table left final,
      stack <<+ arm.pre.stack ∧ arm.actions = cursor.actions := by
  have compiled := cursor.run
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  cases compiled with
  | zero hroom hpop hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hpPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hpPush hstepJumpi with
        ⟨armExec, hpArm⟩
      let arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table left final :=
        ⟨cursor.pc + 4, _, armExec, cursor.actions, hpArm,
          hleft, hsubLeft, hboundLeft⟩
      exact ⟨arm, hw.2, rfl⟩
  | succ hne hroom hpop hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hne hw.1).elim

/-- Select the jumped arm when the compiled branch flag is known nonzero. -/
theorem Exec.Frame.CompiledCursor.selectBranchSucc
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {flag : B256} {stack : Stack}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (.branch left right) final)
    (hflag : flag ≠ 0)
    (hstack : flag :: stack <<+ cursor.pre.stack) :
    ∃ arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table right final,
      stack <<+ arm.pre.stack ∧ arm.actions = cursor.actions := by
  have compiled := cursor.run
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  cases compiled with
  | zero hroom hpop hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hflag hw.1.symm).elim
  | succ hne hroom hpop hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hpPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hpPush hstepJumpi with
        ⟨afterJump, hpJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterJump hpJump hstepJumpdest with
        ⟨armExec, hpArm⟩
      let arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table right final :=
        ⟨loc + 1, _, armExec, cursor.actions, hpArm,
          hright, hsubRight, hboundRight⟩
      exact ⟨arm, hw.2, rfl⟩

/-- Zero-branch selection together with entry-observation preservation. -/
private theorem Exec.Frame.CompiledCursor.selectBranchZeroSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {stack : Stack}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (.branch left right) final)
    (hstack : (0 : B256) :: stack <<+ cursor.pre.stack) :
    ∃ arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table left final,
      stack <<+ arm.pre.stack ∧ arm.actions = cursor.actions ∧
      Devm.DispatchSilent cursor.pre arm.pre := by
  have compiled := cursor.run
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      _hjumpdest, _hjumpable, _hsubRight, _hboundRight⟩
  cases compiled with
  | zero hroom hpop hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hpPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hpPush hstepJumpi with
        ⟨armExec, hpArm⟩
      let arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table left final :=
        ⟨cursor.pc + 4, _, armExec, cursor.actions, hpArm,
          hleft, hsubLeft, hboundLeft⟩
      exact ⟨arm, hw.2, rfl, Devm.DispatchSilent.of_popBurnBy hpop⟩
  | succ hne hroom hpop hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hne hw.1).elim

/-- Nonzero-branch selection together with entry-observation preservation. -/
private theorem Exec.Frame.CompiledCursor.selectBranchSuccSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {flag : B256} {stack : Stack}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (.branch left right) final)
    (hflag : flag ≠ 0)
    (hstack : flag :: stack <<+ cursor.pre.stack) :
    ∃ arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table right final,
      stack <<+ arm.pre.stack ∧ arm.actions = cursor.actions ∧
      Devm.DispatchSilent cursor.pre arm.pre := by
  have compiled := cursor.run
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, _hsubLeft, _hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  cases compiled with
  | zero hroom hpop hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hflag hw.1.symm).elim
  | succ hne hroom hpop hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hpPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hpPush hstepJumpi with
        ⟨afterJump, hpJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterJump hpJump hstepJumpdest with
        ⟨armExec, hpArm⟩
      let arm : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table right final :=
        ⟨loc + 1, _, armExec, cursor.actions, hpArm,
          hright, hsubRight, hboundRight⟩
      exact ⟨arm, hw.2, rfl, Devm.DispatchSilent.of_popBurnBy hpop⟩

/-- Select the head instruction of a cursor and retain both its exact
occurrence and the proof-indexed cursor immediately after it. -/
theorem Exec.Frame.CompiledCursor.selectNext
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {n : Ninst} {tail : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table (.next n tail) final) :
    ∃ stepPre stepPost xl,
      Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame n stepPre stepPost xl ∧
      Nonempty (Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table tail final) := by
  have compiled := cursor.run
  cases compiled with
  | next hcompiled htail =>
      have hat : Ninst.At frame.sevm.code cursor.pc n :=
        ninstAt_of_subcode_next cursor.codeSlice
      rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_next (frame := frame) cursor.current
          cursor.parentPrefix hat hcompiled with
        ⟨xl, continuation, selected, occurrence, hedge, hnextPrefix⟩
      obtain ⟨nextBoundary, nextSub⟩ :=
        Func.noPushBefore_next cursor.codeSlice cursor.codeBoundary
      exact ⟨cursor.pre, _, xl, occurrence,
        ⟨⟨cursor.pc + n.size, _, continuation,
          cursor.actions ++ selected, hnextPrefix, htail, nextSub,
          nextBoundary⟩⟩⟩

/-- Select the head instruction while retaining the exact settled child list
crossed by that instruction.  This is the chronological strengthening of
`selectNext` used at callback and value-call sites. -/
theorem Exec.Frame.CompiledCursor.selectNextWithActions
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {n : Ninst} {tail : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table (.next n tail) final) :
    ∃ (tailCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table tail final)
        (xl : Xlot) (selected : List FlowAction),
      Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame n cursor.pre tailCursor.pre xl ∧
      Exec.Deriv.ParentStepActions dp ca
        ⟨tailCursor.pc, frame.sevm, tailCursor.pre, frame.out,
          tailCursor.current⟩
        ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
        selected ∧
      tailCursor.actions = cursor.actions ++ selected := by
  cases hrun : cursor.run with
  | next hcompiled htail =>
      have hat : Ninst.At frame.sevm.code cursor.pc n :=
        ninstAt_of_subcode_next cursor.codeSlice
      rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_next (frame := frame) cursor.current
          cursor.parentPrefix hat hcompiled with
        ⟨xl, continuation, selected, occurrence, hedge, hnextPrefix⟩
      obtain ⟨nextBoundary, nextSub⟩ :=
        Func.noPushBefore_next cursor.codeSlice cursor.codeBoundary
      let tailCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table tail final :=
        ⟨cursor.pc + n.size, _, continuation,
          cursor.actions ++ selected, hnextPrefix, htail, nextSub,
          nextBoundary⟩
      exact ⟨tailCursor, xl, selected, occurrence, hedge, rfl⟩

/-- Align an independently derived filled external-instruction step with the
same source node on the original compiled cursor.  Both the slot and resumed
parent state are forced by deterministic execution. -/
theorem Exec.Frame.CompiledCursor.alignExecStep
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {x : Xinst} {tail : Func} {final rawPost : Devm}
    {rawSlot : Xlot} {rawPc : Nat}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (.next (.exec x) tail) final)
    (rawFilled : rawSlot.Filled)
    (rawStep : Ninst.StepRun rawPc frame.sevm cursor.pre
      (.exec x) rawSlot (.ok rawPost)) :
    ∃ (tailCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table tail final)
        (selected : List FlowAction),
      tailCursor.pre = rawPost ∧
      Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame (.exec x)
        cursor.pre rawPost rawSlot ∧
      Exec.Deriv.ParentStepActions dp ca
        ⟨tailCursor.pc, frame.sevm, tailCursor.pre, frame.out,
          tailCursor.current⟩
        ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
        selected ∧
      tailCursor.actions = cursor.actions ++ selected := by
  rcases cursor.selectNextWithActions with
    ⟨tailCursor, actualSlot, selected, occurrence, edge, hactions⟩
  have occurrenceCopy := occurrence
  rcases occurrenceCopy with
    ⟨actualPc, current, continuation, before, actualSelected,
      hprefix, hat, actualFilled, actualStep, hprec, actualEdge⟩
  have halign := Ninst.StepRun.unique_exec_of_filled
    rawFilled actualFilled rawStep actualStep
  have hslot : rawSlot = actualSlot := halign.1
  have hpost : rawPost = tailCursor.pre :=
    Except.ok.inj halign.2
  subst actualSlot
  subst rawPost
  exact ⟨tailCursor, selected, rfl, occurrence, edge, hactions⟩

theorem Xinst.step_call_spawn_ofCall
    {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume}
    (hspawn : Xinst.step sevm devm .call = .spawn frame resume) :
    ∃ msg, frame = Frame.ofCall msg := by
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hspawn
  repeat' split at hspawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  all_goals first
    | cases hspawn
    | exact ⟨_, (genericCall_step_spawn_exact hspawn).1⟩

theorem Ninst.step_call_spawn_ofCall
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume}
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.call =
      .spawn frame resume pc') :
    ∃ msg, frame = Frame.ofCall msg := by
  have hx : Xinst.step sevm pre .call = .spawn frame resume := by
    exact XStep.toStep_spawn (by
      simpa only [Ninst.call, Ninst.step_exec] using hspawn)
  exact Xinst.step_call_spawn_ofCall hx


/-- Whether the raw outcome retained by a recursive slot commits.  The empty
slot is vacuously committing because it contributes no child actions. -/
def RetainedXlot.RawCommits {xl : Xlot} : RetainedXlot xl → Prop
  | .none => True
  | .some (out := out) _ => Execution.commits out = true

/-- The selected action list of an exact source `CALL` is precisely the list
of its retained raw child.  Complete CALL settlement cannot prune a raw clean
child (unlike CREATE code-deposit settlement); childless and immediately
completed CALLs select the empty list. -/
theorem Exec.Deriv.ParentStepActions.selected_eq_retained_of_call
    {dp : DeployParams} {ca : Adr}
    {pc nextPc : Nat} {sevm : Sevm} {pre post : Devm} {out : Execution}
    {current : Exec pc sevm pre out}
    {continuation : Exec nextPc sevm post out}
    {xl : Xlot} {selected : List FlowAction}
    (hat : Ninst.At sevm.code pc Ninst.call)
    (filled : xl.Filled)
    (step : Ninst.StepRun pc sevm pre Ninst.call xl (.ok post))
    (retained : RetainedXlot xl)
    (commits : Blanc.Weth10.RetainedXlot.RawCommits retained)
    (edge : Exec.Deriv.ParentStepActions dp ca
      ⟨nextPc, sevm, post, out, continuation⟩
      ⟨pc, sevm, pre, out, current⟩ selected) :
    selected = Blanc.Weth10.RetainedXlot.flowActions dp ca retained := by
  cases edge with
  | cont hstep next =>
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call .none (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨trivial, trivial⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled (show Xlot.Filled .none from trivial) step actual).1
      subst xl
      cases retained
      rfl
  | doneOk hstep henter hresume next =>
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call .none (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨_, RunFrame.of_done henter, hresume.symm⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled (show Xlot.Filled .none from trivial) step actual).1
      subst xl
      cases retained
      rfl
  | runOk hstep henter child hresume next =>
      rename_i frame resume childEvm raw
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call
            (.some ⟨childEvm, raw⟩) (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨_, RunFrame.of_run henter, hresume.symm⟩
      have actualFilled : Xlot.Filled (.some ⟨childEvm, raw⟩) :=
        ⟨child⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled actualFilled step actual).1
      subst xl
      cases retained with
      | some retainedRun =>
          have hrun : retainedRun = child := Subsingleton.elim _ _
          subst retainedRun
          rcases Ninst.step_call_spawn_ofCall hs with ⟨msg, rfl⟩
          have hcommit : Frame.settlementCommits
              (Frame.ofCall msg) raw = true :=
            Frame.settlementCommits_ofCall_of_raw_commits commits
          simp [hcommit, RetainedXlot.flowActions]

/-- Align a committed retained CALL boundary with its exact source occurrence
and advance the original-frame cursor by precisely that child's action list. -/
theorem Exec.Frame.CompiledCursor.alignCommittedCallStep
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {tail : Func} {final rawPost : Devm}
    {rawSlot : Xlot} {rawPc : Nat}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (.next Ninst.call tail) final)
    (rawFilled : rawSlot.Filled)
    (rawStep : Ninst.StepRun rawPc frame.sevm cursor.pre
      Ninst.call rawSlot (.ok rawPost))
    (retained : RetainedXlot rawSlot)
    (commits : Blanc.Weth10.RetainedXlot.RawCommits retained) :
    ∃ tailCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table tail final,
      tailCursor.pre = rawPost ∧
      Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame Ninst.call
        cursor.pre rawPost rawSlot ∧
      tailCursor.actions =
        cursor.actions ++
          Blanc.Weth10.RetainedXlot.flowActions dp ca retained := by
  rcases cursor.alignExecStep rawFilled rawStep with
    ⟨tailCursor, selected, hpre, occurrence, edge, hactions⟩
  have hat : Ninst.At frame.sevm.code cursor.pc Ninst.call :=
    ninstAt_of_subcode_next cursor.codeSlice
  have exactStep : Ninst.StepRun cursor.pc frame.sevm cursor.pre
      Ninst.call rawSlot (.ok tailCursor.pre) := by
    have transported :=
      Ninst.stepRun_pc_irrel (pc' := cursor.pc)
        (by simp [Ninst.pcFree]) rawStep
    simpa only [hpre] using transported
  have hselected := edge.selected_eq_retained_of_call
    hat rawFilled exactStep retained commits
  exact ⟨tailCursor, hpre, occurrence, by
    rw [hactions, hselected]⟩

/-- Source instructions which cannot create a recursive execution slot. -/
def NinstIsChildless : Ninst → Prop
  | .reg _ => True
  | .push _ _ => True
  | .exec _ => False

private theorem Exec.Deriv.ParentStepActions.eq_nil_of_isChildless
    {dp : DeployParams} {ca : Adr}
    {n : Ninst} {next : Exec.Deriv} {current : Exec.Deriv}
    {selected : List FlowAction}
    (hat : Ninst.At current.sevm.code current.pc n)
    (hchildless : NinstIsChildless n)
    (edge : Exec.Deriv.ParentStepActions dp ca next current selected) :
    selected = [] := by
  cases edge with
  | cont => rfl
  | doneOk => rfl
  | runOk hstep henter child hresume tail =>
      have hspawn := (Evm.step_next hat).symm.trans hstep
      rcases Ninst.step_spawn_inv hspawn with ⟨x, rfl, hx⟩
      exact hchildless.elim

/-- Advance one childless source instruction without changing the cursor's
chronological child-action prefix. -/
theorem Exec.Frame.CompiledCursor.selectNextChildless
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {n : Ninst} {tail : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table (.next n tail) final)
    (hchildless : NinstIsChildless n) :
    ∃ (tailCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table tail final)
        (xl : Xlot),
      Ninst.Run frame.sevm cursor.pre n tailCursor.pre ∧
      Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame n cursor.pre tailCursor.pre xl ∧
      tailCursor.actions = cursor.actions := by
  cases hrun : cursor.run with
  | next hcompiled htail =>
      have hat : Ninst.At frame.sevm.code cursor.pc n :=
        ninstAt_of_subcode_next cursor.codeSlice
      rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_next (frame := frame) cursor.current
          cursor.parentPrefix hat hcompiled with
        ⟨xl, continuation, selected, occurrence, hedge, hnextPrefix⟩
      have hselected : selected = [] :=
        hedge.eq_nil_of_isChildless hat hchildless
      subst selected
      obtain ⟨nextBoundary, nextSub⟩ :=
        Func.noPushBefore_next cursor.codeSlice cursor.codeBoundary
      let tailCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table tail final :=
        ⟨cursor.pc + n.size, _, continuation, cursor.actions, by
          simpa using hnextPrefix, htail, nextSub, nextBoundary⟩
      exact ⟨tailCursor, xl, Ninst.Run.of_runCompiled hcompiled,
        occurrence, rfl⟩

/-- Peel a line containing no external execution instruction while preserving
the exact child-action prefix. -/
theorem Exec.Frame.CompiledCursor.peelChildlessLine
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {line : Line} {tail : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table (line +++ tail) final)
    (hchildless : ∀ n ∈ line, NinstIsChildless n) :
    ∃ tailCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table tail final,
      Line.Run frame.sevm cursor.pre line tailCursor.pre ∧
      tailCursor.actions = cursor.actions := by
  induction line with
  | nil => exact ⟨cursor, .nil, rfl⟩
  | cons n line ih =>
      change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
        (.next n (line +++ tail)) final at cursor
      rcases cursor.selectNextChildless (hchildless n (by simp)) with
        ⟨nextCursor, xl, hrun, occurrence, hactions⟩
      rcases ih nextCursor (fun i hi => hchildless i (by simp [hi])) with
        ⟨tailCursor, hline, htailActions⟩
      exact ⟨tailCursor, .cons hrun hline, htailActions.trans hactions⟩

/-- Structural pc-freedom of a dispatch tree's stored leaf bodies. -/
private def CompiledDispatchPcFree : DispatchTree → Prop
  | .leaf _ body => body.pcFreeBody = true
  | .fork left right =>
      CompiledDispatchPcFree left ∧ CompiledDispatchPcFree right

private theorem compiledDispatchPcFree_build
    (n : Nat) (entries : List (B256 × Func))
    (hentries : ∀ entry ∈ entries, entry.2.pcFreeBody = true) :
    CompiledDispatchPcFree (DispatchTree.build n entries) := by
  induction n generalizing entries with
  | zero =>
      cases entries with
      | nil =>
          simp [DispatchTree.build, CompiledDispatchPcFree, Func.rev,
            Func.pcFreeBody, Ninst.pushB256, Ninst.pcFree]
      | cons head tail =>
          cases tail with
          | nil => exact hentries head (by simp)
          | cons second rest => exact hentries head (by simp)
  | succ n ih =>
      cases entries with
      | nil =>
          simp [DispatchTree.build, CompiledDispatchPcFree, Func.rev,
            Func.pcFreeBody, Ninst.pushB256, Ninst.pcFree]
      | cons head tail =>
          cases tail with
          | nil => exact hentries head (by simp)
          | cons second rest =>
              simp only [DispatchTree.build, CompiledDispatchPcFree]
              constructor
              · apply ih
                intro entry hmem
                exact hentries entry (List.mem_of_mem_take hmem)
              · apply ih
                intro entry hmem
                exact hentries entry (List.mem_of_mem_drop hmem)

private theorem compiledDispatchWith_pcFree
    {tree : DispatchTree} (h : CompiledDispatchPcFree tree) :
    (dispatchWith fallbackSlot tree).pcFreeBody = true := by
  induction tree with
  | leaf selector body =>
      simpa [CompiledDispatchPcFree, dispatchWith, Func.pcFreeBody,
        Ninst.pcFree, Ninst.pushB256] using h
  | fork left right ihLeft ihRight =>
      rcases h with ⟨hleft, hright⟩
      simp [dispatchWith, Func.pcFreeBody, Ninst.pcFree,
        Ninst.pushB256, ihLeft hleft, ihRight hright]

/-! The pc-freedom proof below deliberately never reduces the complete closed
WETH10 syntax tree.  Each source-shape equality unfolds one small constructor
boundary, while the recursive facts are proved over symbolic lists and trees. -/

private theorem pcFreeBody_prepend (line : Line) (rest : Func) :
    (line +++ rest).pcFreeBody =
      (line.all Ninst.pcFree && rest.pcFreeBody) := by
  induction line with
  | nil => rfl
  | cons n line ih =>
      simp only [prepend, Func.pcFreeBody, List.all_cons, ih, Bool.and_assoc]

private theorem prependStore_pcFreeBody
    (w : B256) (i : Nat) (rest : Func)
    (hrest : rest.pcFreeBody = true) :
    (prependStore w i rest).pcFreeBody = true := by
  simp [prependStore, Func.pcFreeBody, Ninst.pcFree, Ninst.pushB256, hrest]

private theorem prependStoresRev_pcFreeBody
    (stores : List (B256 × Nat)) (rest : Func)
    (hrest : rest.pcFreeBody = true) :
    (prependStoresRev stores rest).pcFreeBody = true := by
  induction stores generalizing rest with
  | nil => exact hrest
  | cons iw stores ih =>
      simp only [prependStoresRev]
      exact ih _ (prependStore_pcFreeBody iw.1 iw.2 rest hrest)

private theorem revWith_pcFreeBody (reason : String) :
    (Func.revWith reason).pcFreeBody = true := by
  unfold Func.revWith Func.revData
  apply prependStoresRev_pcFreeBody
  rfl

private theorem weth10Funcs_shape (dp : DeployParams) :
    weth10Funcs dp =
      [ (selector "name" [], nonpayable name),
        (selector "approve" [.address, .uint256], nonpayable approve),
        (selector "totalSupply" [], nonpayable totalSupply),
        (selector "withdrawTo" [.address, .uint256], nonpayable withdrawTo),
        (selector "transferFrom" [.address, .address, .uint256],
          nonpayable transferFrom),
        (selector "withdraw" [.uint256], nonpayable withdraw),
        (selector "PERMIT_TYPEHASH" [], nonpayable permitTypehash),
        (selector "decimals" [], nonpayable decimals),
        (selector "DOMAIN_SEPARATOR" [], nonpayable (domainSeparator dp)),
        (selector "transferAndCall" [.address, .uint256, .dynBytes],
          nonpayable transferAndCall),
        (selector "flashLoan" [.address, .address, .uint256, .dynBytes],
          nonpayable flashLoan),
        (selector "depositToAndCall" [.address, .dynBytes], depositToAndCall),
        (selector "maxFlashLoan" [.address], nonpayable maxFlashLoan),
        (selector "balanceOf" [.address], nonpayable balanceOfEndpoint),
        (selector "nonces" [.address], nonpayable nonces),
        (selector "CALLBACK_SUCCESS" [], nonpayable callbackSuccess),
        (selector "flashMinted" [], nonpayable flashMinted),
        (selector "withdrawFrom" [.address, .address, .uint256],
          nonpayable withdrawFrom),
        (selector "symbol" [], nonpayable symbol),
        (selector "transfer" [.address, .uint256], nonpayable transfer),
        (selector "depositTo" [.address], depositTo),
        (selector "approveAndCall" [.address, .uint256, .dynBytes],
          nonpayable approveAndCall),
        (selector "deploymentChainId" [],
          nonpayable (deploymentChainId dp)),
        (selector "deposit" [], deposit),
        (selector "permit"
          [.address, .address, .uint256, .uint256, .uint 8, .bytes 32,
            .bytes 32],
          nonpayable (permit dp)),
        (selector "flashFee" [.address, .uint256], nonpayable flashFee),
        (selector "allowance" [.address, .address], nonpayable allowance) ] := by
  rfl

private theorem weth10Funcs_pcFreeBody (dp : DeployParams) :
    ∀ entry ∈ weth10Funcs dp, entry.2.pcFreeBody = true := by
  intro entry member
  rw [weth10Funcs_shape] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals cases h
  all_goals rfl

private theorem weth10Aux_shape :
    weth10Aux =
      [ Func.rev,
        flashTokenError,
        individualLimitError,
        totalLimitError,
        flashFailedError,
        allowanceError,
        burnBalanceError,
        expiredPermitError,
        invalidPermitError,
        transferBalanceError,
        ethTransferError,
        etherTransferError,
        bubbleRevert,
        boolReturn,
        flashSettle,
        transferFromCore,
        withdrawFromCore,
        flashBurn,
        permitRecover ] := by
  rfl

private theorem weth10Aux_pcFreeBody :
    ∀ body ∈ weth10Aux, body.pcFreeBody = true := by
  intro body member
  rw [weth10Aux_shape] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h
  all_goals cases h
  all_goals first | rfl | exact revWith_pcFreeBody _

private theorem weth10Main_shape (dp : DeployParams) :
    weth10Main dp =
      [Ninst.calldatasize, Ninst.iszero] +++
        (receiveEther <?>
          (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))) := by
  rfl

private theorem weth10_shape (dp : DeployParams) :
    weth10 dp = ⟨weth10Main dp, weth10Aux⟩ := by
  rfl

theorem weth10_pcFree (dp : DeployParams) :
    Prog.pcFree (weth10 dp) = true := by
  have hentries := weth10Funcs_pcFreeBody dp
  have htree : CompiledDispatchPcFree (weth10Tree dp) :=
    compiledDispatchPcFree_build (weth10Funcs dp).length
      (weth10Funcs dp) hentries
  have hdispatch := compiledDispatchWith_pcFree htree
  have hprefix :
      (fsig +++
        dispatchWith fallbackSlot (weth10Tree dp)).pcFreeBody = true := by
    rw [pcFreeBody_prepend, hdispatch]
    rfl
  have hreceive : receiveEther.pcFreeBody = true := by rfl
  have hmain : (weth10Main dp).pcFreeBody = true := by
    rw [weth10Main_shape, pcFreeBody_prepend]
    simp only [Func.pcFreeBody, hreceive, hprefix]
    decide
  have haux : weth10Aux.all Func.pcFreeBody = true := by
    simpa only [List.all_eq_true] using weth10Aux_pcFreeBody
  rw [weth10_shape]
  simp only [Prog.pcFree, Func.pcFree, hmain, List.all_cons, haux]
  rfl

/-- Exact gas burns from the same source state have the same target state. -/
theorem Devm.eq_of_burnBy
    {cost : Nat} {pre left right : Devm}
    (hleft : Devm.BurnBy cost pre left)
    (hright : Devm.BurnBy cost pre right) : left = right := by
  apply Devm.eq_of_proj
  · exact hleft.stack.symm.trans hright.stack
  · exact hleft.memory.symm.trans hright.memory
  · have hl := hleft.gasLeft
    have hr := hright.gasLeft
    omega
  · exact hleft.logs.symm.trans hright.logs
  · exact hleft.refundCounter.symm.trans hright.refundCounter
  · exact hleft.output.symm.trans hright.output
  · exact hleft.accountsToDelete.symm.trans hright.accountsToDelete
  · exact hleft.returnData.symm.trans hright.returnData
  · exact hleft.error.symm.trans hright.error
  · exact hleft.accessedAddresses.symm.trans hright.accessedAddresses
  · exact hleft.accessedStorageKeys.symm.trans hright.accessedStorageKeys
  · exact hleft.state.symm.trans hright.state
  · exact hleft.createdAccounts.symm.trans hright.createdAccounts
  · exact hleft.transientStorage.symm.trans hright.transientStorage

/-- The actual retained root execution, advanced past the runtime's entry
`JUMPDEST`, is a compiled cursor at `weth10Main`. -/
theorem Exec.Frame.compiledMainCursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame) :
    ∃ cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (weth10 dp).main frame.post,
      cursor.actions = [] := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hcode := context.invocation.2.2.2
      have hcompiled := Prog.runCompiled_of_exec e pre (weth10 dp) post
        (weth10_pcFree dp) run hcode
      rcases hcompiled with ⟨compiledMid, hcompiledBurn, hmain⟩
      have hget :
          (table 0 (((weth10 dp).main) :: weth10Aux))[0]? =
            some (0, (weth10 dp).main) := rfl
      rcases subcode_of_get?_eq_some hcode hget with ⟨hjumpdest, hsub⟩
      have hboundary : noPushBefore e.code 1 32 = true :=
        (Prog.jumpable_of_get?_table hcode hget).2
      rcases jumpdest_at_exact run hjumpdest with
        ⟨actualMid, continuation, hburn, hgas, hprec⟩
      have hmid : actualMid = compiledMid :=
        Devm.eq_of_burnBy (Devm.BurnBy.of_burn hburn hgas)
          hcompiledBurn
      subst compiledMid
      have hstep : Evm.step ⟨0, e, pre⟩ = .cont 1 actualMid :=
        Evm.jumpdest_cont hjumpdest
          (Devm.BurnBy.of_burn hburn hgas)
      have hrootPrefix : Exec.Deriv.ParentPrefixActions dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨0, e, pre, .ok post, run⟩ [] :=
        Exec.Deriv.ParentPrefixActions.refl _
      rcases Blanc.Weth10.Exec.Frame.advance_cont
          (frame := ⟨0, e, pre, .ok post, run, committed⟩)
          run hrootPrefix hstep with
        ⟨actualContinuation, hentryPrefix⟩
      have hprefix : Exec.Deriv.ParentPrefixActions dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨1, e, actualMid, .ok post, actualContinuation⟩ [] := by
        simpa using hentryPrefix
      exact ⟨⟨1, actualMid, actualContinuation, [], hprefix, hmain,
        hsub, hboundary⟩, rfl⟩

/-- Entry-silent companion of `compiledMainCursor`, retaining the exact
post-`JUMPDEST` state used by the original execution. -/
private theorem Exec.Frame.compiledMainCursorSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame) :
    ∃ cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (weth10 dp).main frame.post,
      cursor.actions = [] ∧
      Devm.DispatchSilent frame.pre cursor.pre := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hcode := context.invocation.2.2.2
      have hcompiled := Prog.runCompiled_of_exec e pre (weth10 dp) post
        (weth10_pcFree dp) run hcode
      rcases hcompiled with ⟨compiledMid, hcompiledBurn, hmain⟩
      have hget :
          (table 0 (((weth10 dp).main) :: weth10Aux))[0]? =
            some (0, (weth10 dp).main) := rfl
      rcases subcode_of_get?_eq_some hcode hget with ⟨hjumpdest, hsub⟩
      have hboundary : noPushBefore e.code 1 32 = true :=
        (Prog.jumpable_of_get?_table hcode hget).2
      rcases jumpdest_at_exact run hjumpdest with
        ⟨actualMid, continuation, hburn, hgas, hprec⟩
      have hmid : actualMid = compiledMid :=
        Devm.eq_of_burnBy (Devm.BurnBy.of_burn hburn hgas)
          hcompiledBurn
      subst compiledMid
      have hstep : Evm.step ⟨0, e, pre⟩ = .cont 1 actualMid :=
        Evm.jumpdest_cont hjumpdest
          (Devm.BurnBy.of_burn hburn hgas)
      have hrootPrefix : Exec.Deriv.ParentPrefixActions dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨0, e, pre, .ok post, run⟩ [] :=
        Exec.Deriv.ParentPrefixActions.refl _
      rcases Blanc.Weth10.Exec.Frame.advance_cont
          (frame := ⟨0, e, pre, .ok post, run, committed⟩)
          run hrootPrefix hstep with
        ⟨actualContinuation, hentryPrefix⟩
      have hprefix : Exec.Deriv.ParentPrefixActions dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨1, e, actualMid, .ok post, actualContinuation⟩ [] := by
        simpa using hentryPrefix
      exact ⟨⟨1, actualMid, actualContinuation, [], hprefix, hmain,
        hsub, hboundary⟩, rfl,
        Devm.DispatchSilent.of_burnBy hcompiledBurn⟩

/-- A matching compiled dispatch leaf advances to its stored body while
removing the selector word from the stack. -/
private theorem Exec.Frame.CompiledCursor.reachDispatchLeaf
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)} {final : Devm}
    {sig w : B256} {f body : Func} {k : Nat} {stack : Stack}
    (hmem : (sig, f) ∈ [(w, body)])
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (dispatchWith k (.leaf w body)) final)
    (hstack : sig :: stack <<+ cursor.pre.stack) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table f final,
      stack <<+ bodyCursor.pre.stack ∧
      bodyCursor.actions = cursor.actions := by
  have heq : (sig, f) = (w, body) := List.mem_singleton.mp hmem
  injection heq with hsig hfun
  subst w
  subst body
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
    ([Ninst.pushB256 sig, Ninst.eq] +++ (f <?> .call k)) final at cursor
  rcases cursor.peelChildlessLine
      (by simp [NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, hline, hbranchActions⟩
  have hflag : (sig =? sig) :: stack <<+ branchCursor.pre.stack := by
    rcases Line.of_run_cons hline with ⟨afterPush, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨afterEq, heq, hnil⟩
    cases hnil
    have hpushed : sig :: sig :: stack <<+ afterPush.stack := by
      simpa using prefix_of_push (of_run_pushB256 hpush) hstack
    exact prefix_of_eq heq hpushed
  rw [show (sig =? sig) = 1 from by simp [B256.eqCheck]] at hflag
  rcases branchCursor.selectBranchSucc
      (left := .call k) (right := f) (flag := (1 : B256))
      (stack := stack) (by decide) hflag with
    ⟨bodyCursor, hbodyStack, hbodyActions⟩
  exact ⟨bodyCursor, hbodyStack, hbodyActions.trans hbranchActions⟩

/-- Reach the selected body of a generated sorted dispatch tree while keeping
the cursor tied to the original retained `Exec`. -/
private theorem Exec.Frame.CompiledCursor.reachDispatchWith_build :
    ∀ {n : Nat} {xs : List (B256 × Func)} {sig : B256} {f : Func}
      {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
      {fs : List Func} {table : List (Nat × Func)} {k : Nat}
      {final : Devm} {stack : Stack},
      DispatchTree.sorted xs = true →
      xs.length ≤ n + 1 →
      (sig, f) ∈ xs →
      (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
        (dispatchWith k (DispatchTree.build n xs)) final) →
      (sig :: stack <<+ cursor.pre.stack) →
      ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table f final,
        stack <<+ bodyCursor.pre.stack ∧
        bodyCursor.actions = cursor.actions := by
  intro n
  induction n with
  | zero =>
      intro xs sig f dp ca frame fs table k final stack hsorted hlen hmem
        cursor hstack
      rcases xs with _ | ⟨⟨w, body⟩, _ | ⟨y, ys⟩⟩
      · cases hmem
      · exact cursor.reachDispatchLeaf hmem hstack
      · exfalso
        simp only [List.length_cons] at hlen
        omega
  | succ n ih =>
      intro xs sig f dp ca frame fs table k final stack hsorted hlen hmem
        cursor hstack
      rcases xs with _ | ⟨⟨w, body⟩, _ | ⟨y, ys⟩⟩
      · cases hmem
      · exact cursor.reachDispatchLeaf hmem hstack
      · simp only [List.length_cons] at hlen
        have htakeLen :
            (((w, body) :: y :: ys).take
              ((((w, body) :: y :: ys).length + 1) / 2)).length ≤
              n + 1 := by
          simp only [List.length_take, List.length_cons]
          omega
        have hdropLen :
            (((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2)).length ≤
              n + 1 := by
          simp only [List.length_drop, List.length_cons]
          omega
        obtain ⟨z, zs, hdrop⟩ :
            ∃ z zs, ((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2) = z :: zs := by
          rcases hd : ((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2) with _ | ⟨z, zs⟩
          · exfalso
            have hl := congrArg List.length hd
            simp only [List.length_drop, List.length_cons,
              List.length_nil] at hl
            omega
          · exact ⟨z, zs, rfl⟩
        have hsortedSplit : DispatchTree.sorted
            (((w, body) :: y :: ys).take
                ((((w, body) :: y :: ys).length + 1) / 2) ++
              ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2)) = true := by
          rw [List.take_append_drop]
          exact hsorted
        have hsortedTake := DispatchTree.sorted_append_left hsortedSplit
        have hsortedDrop := DispatchTree.sorted_append_right hsortedSplit
        have hmemSplit :
            (sig, f) ∈ ((w, body) :: y :: ys).take
                ((((w, body) :: y :: ys).length + 1) / 2) ∨
              (sig, f) ∈ ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2) := by
          apply List.mem_append.mp
          rw [List.take_append_drop]
          exact hmem
        change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
          ([Ninst.dup 0,
              Ninst.pushB256 (leftmostFsig
                (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2)))),
              Ninst.gt] +++
            (dispatchWith k
                (DispatchTree.build n
                  (((w, body) :: y :: ys).take
                    ((((w, body) :: y :: ys).length + 1) / 2))) <?>
              dispatchWith k
                (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2))))) final at cursor
        rcases cursor.peelChildlessLine
            (by simp [NinstIsChildless, Ninst.pushB256]) with
          ⟨branchCursor, hline, hbranchActions⟩
        have hflagPrefix :
            (leftmostFsig (DispatchTree.build n
                (((w, body) :: y :: ys).drop
                  ((((w, body) :: y :: ys).length + 1) / 2))) >? sig) ::
              sig :: stack <<+ branchCursor.pre.stack := by
          rcases Line.of_run_cons hline with
            ⟨afterDup, hdup, hrestDup⟩
          rcases Line.of_run_cons hrestDup with
            ⟨afterPush, hpush, hrestPush⟩
          rcases Line.of_run_cons hrestPush with
            ⟨afterGt, hgt, hnil⟩
          cases hnil
          have hdupStack : sig :: sig :: stack <<+ afterDup.stack :=
            prefix_of_dup_val hdup (by show_nth) hstack
          have hpushStack :
              leftmostFsig (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2))) ::
                sig :: sig :: stack <<+ afterPush.stack := by
            simpa using prefix_of_push (of_run_pushB256 hpush) hdupStack
          exact prefix_of_gt hgt hpushStack
        have hleftmost :
            leftmostFsig (DispatchTree.build n
              (((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2))) = z.fst := by
          rw [hdrop, DispatchTree.leftmostFsig_build]
        rw [hleftmost] at hflagPrefix
        rcases hmemSplit with hmemTake | hmemDrop
        · have hlt : sig < z.fst := by
            have hz : z ∈ ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2) := by
              rw [hdrop]
              exact List.mem_cons_self ..
            exact DispatchTree.fst_lt_of_sorted_append
              hsortedSplit hmemTake hz
          have hcheck : (z.fst >? sig) = 1 := by
            simp [B256.gtCheck, hlt]
          rw [hcheck] at hflagPrefix
          rcases branchCursor.selectBranchSucc (flag := (1 : B256))
              (by decide) hflagPrefix with
            ⟨leftCursor, hleftStack, hleftActions⟩
          rcases ih hsortedTake htakeLen hmemTake leftCursor hleftStack with
            ⟨bodyCursor, hbodyStack, hbodyActions⟩
          exact ⟨bodyCursor, hbodyStack,
            hbodyActions.trans (hleftActions.trans hbranchActions)⟩
        · have hle : z.fst ≤ sig := by
            have hsortedZ : DispatchTree.sorted (z :: zs) = true := by
              rw [← hdrop]
              exact hsortedDrop
            rw [hdrop] at hmemDrop
            exact DispatchTree.fst_le_of_sorted_mem hsortedZ hmemDrop
          have hcheck : (z.fst >? sig) = 0 := by
            simp [B256.gtCheck, not_lt_of_ge hle]
          rw [hcheck] at hflagPrefix
          rcases branchCursor.selectBranchZero hflagPrefix with
            ⟨rightCursor, hrightStack, hrightActions⟩
          rcases ih hsortedDrop hdropLen hmemDrop rightCursor hrightStack with
            ⟨bodyCursor, hbodyStack, hbodyActions⟩
          exact ⟨bodyCursor, hbodyStack,
            hbodyActions.trans (hrightActions.trans hbranchActions)⟩

/-- Public cursor form of sorted dispatch reachability.  Unlike the functional
reachability theorem, the returned body cursor remains an exact continuation
of the input frame's original `Exec` proof. -/
theorem Exec.Frame.CompiledCursor.reachDispatchWith
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)} {final : Devm}
    {funcs : List (B256 × Func)} {sig : B256} {f : Func}
    {k : Nat} {stack : Stack}
    (hsorted : DispatchTree.sorted funcs = true)
    (hmem : (sig, f) ∈ funcs)
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (dispatchWith k (DispatchTree.ofSorted funcs)) final)
    (hstack : sig :: stack <<+ cursor.pre.stack) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table f final,
      stack <<+ bodyCursor.pre.stack ∧
      bodyCursor.actions = cursor.actions :=
  cursor.reachDispatchWith_build hsorted (Nat.le_succ _) hmem hstack

/-- A matching dispatch leaf with its exact entry-observation silence. -/
private theorem Exec.Frame.CompiledCursor.reachDispatchLeafSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)} {final : Devm}
    {sig w : B256} {f body : Func} {k : Nat} {stack : Stack}
    (hmem : (sig, f) ∈ [(w, body)])
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (dispatchWith k (.leaf w body)) final)
    (hstack : sig :: stack <<+ cursor.pre.stack) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table f final,
      stack <<+ bodyCursor.pre.stack ∧
      bodyCursor.actions = cursor.actions ∧
      Devm.DispatchSilent cursor.pre bodyCursor.pre := by
  have heq : (sig, f) = (w, body) := List.mem_singleton.mp hmem
  injection heq with hsig hfun
  subst w
  subst body
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
    ([Ninst.pushB256 sig, Ninst.eq] +++ (f <?> .call k)) final at cursor
  rcases cursor.peelChildlessLine
      (by simp [NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, hline, hbranchActions⟩
  have hlineSilent : Devm.DispatchSilent cursor.pre branchCursor.pre :=
    Devm.DispatchSilent.of_pushEq hline
  have hflag : (sig =? sig) :: stack <<+ branchCursor.pre.stack := by
    rcases Line.of_run_cons hline with ⟨afterPush, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨afterEq, heq, hnil⟩
    cases hnil
    have hpushed : sig :: sig :: stack <<+ afterPush.stack := by
      simpa using prefix_of_push (of_run_pushB256 hpush) hstack
    exact prefix_of_eq heq hpushed
  rw [show (sig =? sig) = 1 from by simp [B256.eqCheck]] at hflag
  rcases branchCursor.selectBranchSuccSilent
      (left := .call k) (right := f) (flag := (1 : B256))
      (stack := stack) (by decide) hflag with
    ⟨bodyCursor, hbodyStack, hbodyActions, hbranchSilent⟩
  exact ⟨bodyCursor, hbodyStack, hbodyActions.trans hbranchActions,
    hlineSilent.trans hbranchSilent⟩

/-- Reach the selected dispatch body while preserving the exact entry
observations of the supplied original-execution cursor. -/
private theorem Exec.Frame.CompiledCursor.reachDispatchWithSilent_build :
    ∀ {n : Nat} {xs : List (B256 × Func)} {sig : B256} {f : Func}
      {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
      {fs : List Func} {table : List (Nat × Func)} {k : Nat}
      {final : Devm} {stack : Stack},
      DispatchTree.sorted xs = true →
      xs.length ≤ n + 1 →
      (sig, f) ∈ xs →
      (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
        (dispatchWith k (DispatchTree.build n xs)) final) →
      (sig :: stack <<+ cursor.pre.stack) →
      ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table f final,
        stack <<+ bodyCursor.pre.stack ∧
        bodyCursor.actions = cursor.actions ∧
        Devm.DispatchSilent cursor.pre bodyCursor.pre := by
  intro n
  induction n with
  | zero =>
      intro xs sig f dp ca frame fs table k final stack hsorted hlen hmem
        cursor hstack
      rcases xs with _ | ⟨⟨w, body⟩, _ | ⟨y, ys⟩⟩
      · cases hmem
      · exact cursor.reachDispatchLeafSilent hmem hstack
      · exfalso
        simp only [List.length_cons] at hlen
        omega
  | succ n ih =>
      intro xs sig f dp ca frame fs table k final stack hsorted hlen hmem
        cursor hstack
      rcases xs with _ | ⟨⟨w, body⟩, _ | ⟨y, ys⟩⟩
      · cases hmem
      · exact cursor.reachDispatchLeafSilent hmem hstack
      · simp only [List.length_cons] at hlen
        have htakeLen :
            (((w, body) :: y :: ys).take
              ((((w, body) :: y :: ys).length + 1) / 2)).length ≤
              n + 1 := by
          simp only [List.length_take, List.length_cons]
          omega
        have hdropLen :
            (((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2)).length ≤
              n + 1 := by
          simp only [List.length_drop, List.length_cons]
          omega
        obtain ⟨z, zs, hdrop⟩ :
            ∃ z zs, ((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2) = z :: zs := by
          rcases hd : ((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2) with _ | ⟨z, zs⟩
          · exfalso
            have hl := congrArg List.length hd
            simp only [List.length_drop, List.length_cons,
              List.length_nil] at hl
            omega
          · exact ⟨z, zs, rfl⟩
        have hsortedSplit : DispatchTree.sorted
            (((w, body) :: y :: ys).take
                ((((w, body) :: y :: ys).length + 1) / 2) ++
              ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2)) = true := by
          rw [List.take_append_drop]
          exact hsorted
        have hsortedTake := DispatchTree.sorted_append_left hsortedSplit
        have hsortedDrop := DispatchTree.sorted_append_right hsortedSplit
        have hmemSplit :
            (sig, f) ∈ ((w, body) :: y :: ys).take
                ((((w, body) :: y :: ys).length + 1) / 2) ∨
              (sig, f) ∈ ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2) := by
          apply List.mem_append.mp
          rw [List.take_append_drop]
          exact hmem
        change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
          ([Ninst.dup 0,
              Ninst.pushB256 (leftmostFsig
                (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2)))),
              Ninst.gt] +++
            (dispatchWith k
                (DispatchTree.build n
                  (((w, body) :: y :: ys).take
                    ((((w, body) :: y :: ys).length + 1) / 2))) <?>
              dispatchWith k
                (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2))))) final at cursor
        rcases cursor.peelChildlessLine
            (by simp [NinstIsChildless, Ninst.pushB256]) with
          ⟨branchCursor, hline, hbranchActions⟩
        have hlineSilent :
            Devm.DispatchSilent cursor.pre branchCursor.pre :=
          Devm.DispatchSilent.of_dupPushGt hline
        have hflagPrefix :
            (leftmostFsig (DispatchTree.build n
                (((w, body) :: y :: ys).drop
                  ((((w, body) :: y :: ys).length + 1) / 2))) >? sig) ::
              sig :: stack <<+ branchCursor.pre.stack := by
          rcases Line.of_run_cons hline with
            ⟨afterDup, hdup, hrestDup⟩
          rcases Line.of_run_cons hrestDup with
            ⟨afterPush, hpush, hrestPush⟩
          rcases Line.of_run_cons hrestPush with
            ⟨afterGt, hgt, hnil⟩
          cases hnil
          have hdupStack : sig :: sig :: stack <<+ afterDup.stack :=
            prefix_of_dup_val hdup (by show_nth) hstack
          have hpushStack :
              leftmostFsig (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2))) ::
                sig :: sig :: stack <<+ afterPush.stack := by
            simpa using prefix_of_push (of_run_pushB256 hpush) hdupStack
          exact prefix_of_gt hgt hpushStack
        have hleftmost :
            leftmostFsig (DispatchTree.build n
              (((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2))) = z.fst := by
          rw [hdrop, DispatchTree.leftmostFsig_build]
        rw [hleftmost] at hflagPrefix
        rcases hmemSplit with hmemTake | hmemDrop
        · have hlt : sig < z.fst := by
            have hz : z ∈ ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2) := by
              rw [hdrop]
              exact List.mem_cons_self ..
            exact DispatchTree.fst_lt_of_sorted_append
              hsortedSplit hmemTake hz
          have hcheck : (z.fst >? sig) = 1 := by
            simp [B256.gtCheck, hlt]
          rw [hcheck] at hflagPrefix
          rcases branchCursor.selectBranchSuccSilent (flag := (1 : B256))
              (by decide) hflagPrefix with
            ⟨leftCursor, hleftStack, hleftActions, hleftSilent⟩
          rcases ih hsortedTake htakeLen hmemTake leftCursor hleftStack with
            ⟨bodyCursor, hbodyStack, hbodyActions, hbodySilent⟩
          exact ⟨bodyCursor, hbodyStack,
            hbodyActions.trans (hleftActions.trans hbranchActions),
            hlineSilent.trans (hleftSilent.trans hbodySilent)⟩
        · have hle : z.fst ≤ sig := by
            have hsortedZ : DispatchTree.sorted (z :: zs) = true := by
              rw [← hdrop]
              exact hsortedDrop
            rw [hdrop] at hmemDrop
            exact DispatchTree.fst_le_of_sorted_mem hsortedZ hmemDrop
          have hcheck : (z.fst >? sig) = 0 := by
            simp [B256.gtCheck, not_lt_of_ge hle]
          rw [hcheck] at hflagPrefix
          rcases branchCursor.selectBranchZeroSilent hflagPrefix with
            ⟨rightCursor, hrightStack, hrightActions, hrightSilent⟩
          rcases ih hsortedDrop hdropLen hmemDrop rightCursor hrightStack with
            ⟨bodyCursor, hbodyStack, hbodyActions, hbodySilent⟩
          exact ⟨bodyCursor, hbodyStack,
            hbodyActions.trans (hrightActions.trans hbranchActions),
            hlineSilent.trans (hrightSilent.trans hbodySilent)⟩

/-- Public entry-silent companion of `reachDispatchWith`. -/
theorem Exec.Frame.CompiledCursor.reachDispatchWithSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)} {final : Devm}
    {funcs : List (B256 × Func)} {sig : B256} {f : Func}
    {k : Nat} {stack : Stack}
    (hsorted : DispatchTree.sorted funcs = true)
    (hmem : (sig, f) ∈ funcs)
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (dispatchWith k (DispatchTree.ofSorted funcs)) final)
    (hstack : sig :: stack <<+ cursor.pre.stack) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table f final,
      stack <<+ bodyCursor.pre.stack ∧
      bodyCursor.actions = cursor.actions ∧
      Devm.DispatchSilent cursor.pre bodyCursor.pre :=
  cursor.reachDispatchWithSilent_build hsorted (Nat.le_succ _)
    hmem hstack

private theorem Exec.descendantFrames_eq_nil_of_halt_step
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {haltOut : Execution}
    (run : Exec pc sevm pre out)
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .halt haltOut) :
    Exec.descendantFrames run = [] := by
  cases run with
  | halt h => simp [Exec.descendantFrames]
  | cont h next => cases hstep.symm.trans h
  | doneErr h henter hresume => cases hstep.symm.trans h
  | doneOk h henter hresume next => cases hstep.symm.trans h
  | runErr h henter child hresume => cases hstep.symm.trans h
  | runOk h henter child hresume next => cases hstep.symm.trans h

/-- Closing a cursor at a terminal source instruction accounts for every
proper descendant of the retained frame.  There is no hidden continuation
after the terminal instruction. -/
theorem Exec.Frame.CompiledCursor.finishLast
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {i : Linst} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table (.last i) final) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = cursor.actions := by
  have htail : Exec.Deriv.descendantFlowActions dp ca
      ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩ = [] := by
    have hat : Linst.At frame.sevm.code cursor.pc i :=
      Linst.at_of_slice cursor.codeSlice
    have hstep := Evm.step_last (devm := cursor.pre) hat
    simp [Exec.Deriv.descendantFlowActions,
      Exec.descendantFrames_eq_nil_of_halt_step cursor.current hstep]
  have hp := cursor.parentPrefix.descendantFlowActions_eq
  change Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame =
    cursor.actions ++ Exec.Deriv.descendantFlowActions dp ca
      ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩ at hp
  rw [htail] at hp
  simpa using hp

/-- Entry-silent exact cursor for a successful recognized selector. -/
theorem Exec.Frame.compiledSelectorBodyCursorSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {body : Func}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux)) body frame.post,
      [] <<+ bodyCursor.pre.stack ∧ bodyCursor.actions = [] ∧
      Devm.DispatchSilent frame.pre bodyCursor.pre := by
  rcases Blanc.Weth10.Exec.Frame.compiledMainCursorSilent (frame := frame) context with
    ⟨mainCursor, hmainActions, hmainSilent⟩
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ([Ninst.calldatasize, Ninst.iszero] +++
      (receiveEther <?>
        (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))))
    frame.post at mainCursor
  rcases mainCursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨entryBranchCursor, hentryLine, hentryActions⟩
  have hentrySilent :
      Devm.DispatchSilent mainCursor.pre entryBranchCursor.pre :=
    Devm.DispatchSilent.of_entryFlag hentryLine
  have hflagPrefix :
      [frame.sevm.data.length.toB256 =? 0] <<+
        entryBranchCursor.pre.stack := by
    rcases Line.of_run_cons hentryLine with
      ⟨afterSize, hsize, hrestSize⟩
    rcases Line.of_run_cons hrestSize with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    have hsizePrefix : [frame.sevm.data.length.toB256] <<+
        afterSize.stack :=
      prefix_of_push (of_run_calldatasize hsize) nil_pref
    exact prefix_of_iszero hzero hsizePrefix
  have hflagZero : (frame.sevm.data.length.toB256 =? 0) = 0 := by
    simp [B256.eqCheck, hnonempty]
  rw [hflagZero] at hflagPrefix
  rcases entryBranchCursor.selectBranchZeroSilent hflagPrefix with
    ⟨dispatchPrefixCursor, hdispatchStack, hdispatchActions,
      hdispatchSilent⟩
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))
    frame.post at dispatchPrefixCursor
  rcases dispatchPrefixCursor.peelChildlessLine
      (by simp [fsig, cdl, shiftRight, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨dispatchCursor, hfsig, hfsigActions⟩
  have hfsigSilent :
      Devm.DispatchSilent dispatchPrefixCursor.pre dispatchCursor.pre :=
    Devm.DispatchSilent.of_fsig hfsig
  have hselectorPrefix : Sevm.selector frame.sevm :: [] <<+
      dispatchCursor.pre.stack :=
    prefix_of_fsig nil_pref hfsig
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (dispatchWith fallbackSlot
      (DispatchTree.ofSorted (weth10Funcs dp))) frame.post at dispatchCursor
  rcases dispatchCursor.reachDispatchWithSilent (weth10Funcs_sorted dp)
      hmem hselectorPrefix with
    ⟨bodyCursor, hbodyStack, hbodyActions, hbodySilent⟩
  refine ⟨bodyCursor, hbodyStack, ?_, ?_⟩
  · exact hbodyActions.trans (hfsigActions.trans
      (hdispatchActions.trans (hentryActions.trans hmainActions)))
  · exact hmainSilent.trans (hentrySilent.trans
      (hdispatchSilent.trans (hfsigSilent.trans hbodySilent)))

/-- A successful authentic non-receive invocation reaches the cursor for its
exact listed selector body.  This is the proof-indexed counterpart of
`reach_of_dispatchWith`: the returned cursor belongs to the original retained
frame and therefore remembers every earlier child action. -/
theorem Exec.Frame.compiledSelectorBodyCursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {body : Func}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux)) body frame.post,
      [] <<+ bodyCursor.pre.stack ∧ bodyCursor.actions = [] := by
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorSilent (frame := frame) context hnonempty hmem with
    ⟨bodyCursor, hstack, hactions, _hsilent⟩
  exact ⟨bodyCursor, hstack, hactions⟩

/-- A successful nonpayable wrapper reaches its exact body cursor while
preserving the wrapper's entry observations. -/
theorem Exec.Frame.CompiledCursor.enterNonpayableSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (nonpayable body) final) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table body final,
      [] <<+ bodyCursor.pre.stack ∧
      bodyCursor.actions = cursor.actions ∧
      Devm.DispatchSilent cursor.pre bodyCursor.pre := by
  have hvalue : frame.sevm.value = 0 :=
    value_eq_zero_of_run_nonpayable
      (Func.Run.of_runCompiled cursor.run)
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
    ([Ninst.callvalue, Ninst.iszero] +++ (body <?> Func.rev)) final at cursor
  rcases cursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨branchCursor, hline, hbranchActions⟩
  have hlineSilent : Devm.DispatchSilent cursor.pre branchCursor.pre :=
    Devm.DispatchSilent.of_callvalueFlag hline
  have hflagPrefix : [frame.sevm.value =? 0] <<+
      branchCursor.pre.stack := by
    rcases Line.of_run_cons hline with
      ⟨afterValue, hcallvalue, hrestValue⟩
    rcases Line.of_run_cons hrestValue with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    have hvaluePrefix : [frame.sevm.value] <<+ afterValue.stack :=
      prefix_of_push (of_run_callvalue hcallvalue) nil_pref
    exact prefix_of_iszero hzero hvaluePrefix
  rw [hvalue] at hflagPrefix
  have hone : ((0 : B256) =? 0) = 1 := by simp [B256.eqCheck]
  rw [hone] at hflagPrefix
  rcases branchCursor.selectBranchSuccSilent (flag := (1 : B256))
      (by decide) hflagPrefix with
    ⟨bodyCursor, hbodyStack, hbodyActions, hbranchSilent⟩
  exact ⟨bodyCursor, hbodyStack, hbodyActions.trans hbranchActions,
    hlineSilent.trans hbranchSilent⟩

/-- A successful cursor at a nonpayable wrapper reaches its guarded body on
the original execution. -/
theorem Exec.Frame.CompiledCursor.enterNonpayable
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (nonpayable body) final) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table body final,
      [] <<+ bodyCursor.pre.stack ∧
      bodyCursor.actions = cursor.actions := by
  rcases cursor.enterNonpayableSilent with
    ⟨bodyCursor, hstack, hactions, _hsilent⟩
  exact ⟨bodyCursor, hstack, hactions⟩

/-- Follow one generated internal source call while preserving the original
frame execution and its chronological child-action prefix.  The installed
program equation is explicit because the cursor's local code slice alone
cannot identify the called table body. -/
theorem Exec.Frame.CompiledCursor.enterCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
          (table 0 (f₀ :: aux)) body final,
        bodyCursor.actions = cursor.actions := by
  cases hrun : cursor.run with
  | call hget hroom hburn hbody =>
      rcases subcode_compile_call cursor.codeSlice with
        ⟨loc, p, hgetTable, hloc, hpushAt, hjump⟩
      have hpf := (Prog.get?_table (m := 0)).symm.trans
        (congrArg (Prod.snd <$> ·) hgetTable)
      rw [hget] at hpf
      simp only [Option.map_eq_map, Option.map_some,
        Option.some.injEq] at hpf
      subst p
      rcases subcode_of_get?_eq_some hcode hgetTable with
        ⟨hjumpdest, hsub⟩
      have hjumpable := Prog.jumpable_of_get?_table hcode hgetTable
      rcases hpushAt with ⟨le, hpush⟩
      rcases Evm.call_steps (le := le) hpush hjump hjumpdest
          hjumpable.1 hloc hroom hburn with
        ⟨hstepPush, hstepJump, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) cursor.current cursor.parentPrefix
          hstepPush with
        ⟨afterPush, hprefixPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hprefixPush hstepJump with
        ⟨afterJump, hprefixJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterJump hprefixJump hstepJumpdest with
        ⟨bodyExec, hprefixBody⟩
      let bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
          (table 0 (f₀ :: aux)) _ final :=
        ⟨loc + 1, _, bodyExec, cursor.actions, hprefixBody,
          hbody, hsub, hjumpable.2⟩
      exact ⟨_, hget, bodyCursor, rfl⟩

/-- Reach the exact external `CALL` instruction in a successful generated
ERC-677 callback body.  Every source instruction before the call is
childless, so the returned cursor has crossed no retained child actions. -/
theorem Exec.Frame.CompiledCursor.reachCallBoolCallback
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {table : List (Nat × Func)}
    {sel targetArg dataArg : B256} {value : Line} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux) table
      (callBoolCallback sel targetArg dataArg value) final)
    (hvalue : ∀ n ∈ value, NinstIsChildless n) :
    ∃ callCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux) table
        (.next Ninst.call (.call boolReturnSlot)) final,
      callCursor.actions = cursor.actions := by
  unfold callBoolCallback at cursor
  rcases cursor.peelChildlessLine
      (line := arg targetArg ++
        [Ninst.dup 0, Ninst.extcodesize, Ninst.iszero])
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, _hcheck, hcheckActions⟩
  rcases branchCursor.selectBranchWithActions with hsuccess | hrev
  · rcases hsuccess with ⟨successCursor, hbranchActions⟩
    rcases successCursor.selectNextChildless (by
        simp [NinstIsChildless]) with
      ⟨valueCursor, _, _hpop, _, hpopActions⟩
    rcases valueCursor.peelChildlessLine hvalue with
      ⟨headCursor, _hvalueRun, hvalueActions⟩
    rcases headCursor.peelChildlessLine
        (line := storeTokenCallbackHead sel)
        (by simp [storeTokenCallbackHead, mstoreAt,
          NinstIsChildless, Ninst.pushB256]) with
      ⟨zerosCursor, _hhead, hheadActions⟩
    rcases zerosCursor.peelChildlessLine
        (line := pushList [0, 0])
        (by simp [pushList, NinstIsChildless, Ninst.pushB256]) with
      ⟨tailCursor, _hzeros, hzerosActions⟩
    rcases tailCursor.peelChildlessLine
        (line := forwardArgTail dataArg 4)
        (by simp [forwardArgTail, arg, cdl, mstoreAt,
          NinstIsChildless, Ninst.pushB256]) with
      ⟨sizeCursor, _htail, htailActions⟩
    rcases sizeCursor.peelChildlessLine
        (line := tokenCallbackArgsSize)
        (by simp [tokenCallbackArgsSize, NinstIsChildless,
          Ninst.pushB256]) with
      ⟨offsetCursor, _hsize, hsizeActions⟩
    rcases offsetCursor.peelChildlessLine
        (line := [Ninst.pushB256 callbackArgsOffset, Ninst.pushB256 0])
        (by simp [NinstIsChildless, Ninst.pushB256]) with
      ⟨targetCursor, _hoffsets, hoffsetsActions⟩
    rcases targetCursor.peelChildlessLine
        (line := arg targetArg)
        (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
      ⟨gasCursor, _htarget, htargetActions⟩
    rcases gasCursor.selectNextChildless (by
        simp [NinstIsChildless]) with
      ⟨callCursor, _, _hgas, _, hgasActions⟩
    refine ⟨callCursor, ?_⟩
    calc
      callCursor.actions = gasCursor.actions := hgasActions
      _ = targetCursor.actions := htargetActions
      _ = offsetCursor.actions := hoffsetsActions
      _ = sizeCursor.actions := hsizeActions
      _ = tailCursor.actions := htailActions
      _ = zerosCursor.actions := hzerosActions
      _ = headCursor.actions := hheadActions
      _ = valueCursor.actions := hvalueActions
      _ = successCursor.actions := hpopActions
      _ = branchCursor.actions := hbranchActions
      _ = cursor.actions := hcheckActions
  · rcases hrev with ⟨revCursor, _⟩
    exact absurd (Func.Run.of_runCompiled revCursor.run) not_run_rev

/-- Reach the ERC-677 `CALL` while retaining the exact successful source
prefix facts at the returned cursor state.  In particular, the
`RawTokenCallbackCallPrefix` is indexed by `callCursor.pre`, rather than by an
independently re-extracted intermediate state. -/
theorem Exec.Frame.CompiledCursor.reachCallBoolCallbackWithPrefix
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {table : List (Nat × Func)}
    {sel targetArg dataArg valueWord : B256} {value : Line}
    {final : Devm} {img : Bytes}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux) table
      (callBoolCallback sel targetArg dataArg value) final)
    (hvalueChildless : ∀ n ∈ value, NinstIsChildless n)
    (h_value_stack : ∀ {a b : Devm} {xs : Stack},
      xs <<+ a.stack → Line.Run frame.sevm a value b →
        valueWord :: xs <<+ b.stack)
    (h_value_stor : Line.Inv Devm.getStor value)
    (h_value_bal : Line.Inv Devm.getBal value)
    (h_value_code : Line.Inv Devm.getCode value)
    (h_value_mem : Line.Inv Devm.memory value)
    (h_value_logs : Line.Inv Devm.logs value)
    (h_value_output : Line.Inv Devm.output value)
    (h_wf : Mem.Wf cursor.pre.memory)
    (h_reads : Mem.Reads cursor.pre.memory img) :
    ∃ callCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux) table
        (.next Ninst.call (.call boolReturnSlot)) final,
      callCursor.actions = cursor.actions ∧
      RawTokenCallbackCallPrefix frame.sevm sel targetArg dataArg valueWord
        img cursor.pre callCursor.pre := by
  unfold callBoolCallback at cursor
  rcases cursor.peelChildlessLine
      (line := arg targetArg ++
        [Ninst.dup 0, Ninst.extcodesize, Ninst.iszero])
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, hcheck, hcheckActions⟩
  rcases branchCursor.selectBranchLeftWithBurn
      (fun _ => not_run_rev) with
    ⟨successCursor, hpopCheck, hbranchActions⟩
  rcases successCursor.selectNextChildless (by
      simp [NinstIsChildless]) with
    ⟨valueCursor, _, hpop, _, hpopActions⟩
  rcases valueCursor.peelChildlessLine hvalueChildless with
    ⟨headCursor, hvalueRun, hvalueActions⟩
  rcases headCursor.peelChildlessLine
      (line := storeTokenCallbackHead sel)
      (by simp [storeTokenCallbackHead, mstoreAt,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨zerosCursor, hhead, hheadActions⟩
  rcases zerosCursor.peelChildlessLine
      (line := pushList [0, 0])
      (by simp [pushList, NinstIsChildless, Ninst.pushB256]) with
    ⟨tailCursor, hzeros, hzerosActions⟩
  rcases tailCursor.peelChildlessLine
      (line := forwardArgTail dataArg 4)
      (by simp [forwardArgTail, arg, cdl, mstoreAt,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨sizeCursor, htail, htailActions⟩
  rcases sizeCursor.peelChildlessLine
      (line := tokenCallbackArgsSize)
      (by simp [tokenCallbackArgsSize, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨offsetCursor, hsize, hsizeActions⟩
  rcases offsetCursor.peelChildlessLine
      (line := [Ninst.pushB256 callbackArgsOffset, Ninst.pushB256 0])
      (by simp [NinstIsChildless, Ninst.pushB256]) with
    ⟨targetCursor, hoffsets, hoffsetsActions⟩
  rcases targetCursor.peelChildlessLine
      (line := arg targetArg)
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨gasCursor, htarget, htargetActions⟩
  rcases gasCursor.selectNextChildless (by
      simp [NinstIsChildless]) with
    ⟨callCursor, _, hgas, _, hgasActions⟩
  have hprefix := rawTokenCallbackCallPrefix_of_runs
    sel targetArg dataArg valueWord value h_value_stack h_value_stor
    h_value_bal h_value_code h_value_mem h_value_logs h_value_output
    h_wf h_reads hcheck (Devm.PopBurn.of_popBurnBy hpopCheck) hpop
    hvalueRun hhead hzeros htail hsize hoffsets htarget hgas
  refine ⟨callCursor, ?_, hprefix⟩
  calc
    callCursor.actions = gasCursor.actions := hgasActions
    _ = targetCursor.actions := htargetActions
    _ = offsetCursor.actions := hoffsetsActions
    _ = sizeCursor.actions := hsizeActions
    _ = tailCursor.actions := htailActions
    _ = zerosCursor.actions := hzerosActions
    _ = headCursor.actions := hheadActions
    _ = valueCursor.actions := hvalueActions
    _ = successCursor.actions := hpopActions
    _ = branchCursor.actions := hbranchActions
    _ = cursor.actions := hcheckActions

/-- A childless line ending in a terminal instruction closes the chronological
cursor without crossing any additional retained child. -/
theorem Exec.Frame.CompiledCursor.finishTerminalChildlessLine
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {line : Line} {i : Linst} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (line +++ Func.last i) final)
    (hchildless : ∀ n ∈ line, NinstIsChildless n) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = cursor.actions := by
  rcases cursor.peelChildlessLine hchildless with
    ⟨lastCursor, _hline, hactions⟩
  exact lastCursor.finishLast.trans hactions

/-- The successful Boolean decoder after an ERC-677 `CALL` contains no
external execution.  Its revert/bubble arms cannot produce the retained
frame's committed final state, while its decode arm is childless. -/
theorem Exec.Frame.CompiledCursor.finishBoolReturnCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (.call boolReturnSlot) final)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = cursor.actions := by
  rcases cursor.enterCall hcode with
    ⟨body, hget, bodyCursor, hbodyActions⟩
  have hbody : body = boolReturn := by
    simpa [weth10, weth10Aux, boolReturnSlot] using hget.symm
  subst body
  unfold boolReturn at bodyCursor
  rcases bodyCursor.selectNextChildless (by
      simp [NinstIsChildless]) with
    ⟨firstBranchCursor, _, _hiszero, _, hiszeroActions⟩
  rcases firstBranchCursor.selectBranchWithActions with
      hdecode | hbubble
  · rcases hdecode with ⟨decodePrefixCursor, hdecodeActions⟩
    rcases decodePrefixCursor.peelChildlessLine
        (line := retdataShorterThan 32)
        (by simp [retdataShorterThan, NinstIsChildless,
          Ninst.pushB256]) with
      ⟨secondBranchCursor, _hshort, hshortActions⟩
    rcases secondBranchCursor.selectBranchWithActions with
        hreturn | hrev
    · rcases hreturn with ⟨returnCursor, hreturnActions⟩
      change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        ((pushList [32, 0, 0] ++
          [Ninst.retdatacopy, Ninst.pushB256 0, Ninst.mload,
            Ninst.iszero, Ninst.iszero] ++
          mstoreAt 0 ++ pushList [32, 0]) +++ Func.ret) final
        at returnCursor
      have hdesc := returnCursor.finishTerminalChildlessLine (by
        simp [pushList, mstoreAt, NinstIsChildless, Ninst.pushB256])
      exact hdesc.trans (hreturnActions.trans
        (hshortActions.trans (hdecodeActions.trans
          (hiszeroActions.trans hbodyActions))))
    · rcases hrev with ⟨revCursor, _⟩
      exact absurd (Func.Run.of_runCompiled revCursor.run) not_run_rev
  · rcases hbubble with ⟨bubbleCursor, _⟩
    rcases bubbleCursor.enterCall hcode with
      ⟨bubbleBody, hbubbleGet, bubbleBodyCursor, _⟩
    have hb : bubbleBody = bubbleRevert := by
      simpa [weth10, weth10Aux, bubbleRevertSlot] using hbubbleGet.symm
    subst bubbleBody
    exact (not_run_bubbleRevert
      (Func.Run.of_runCompiled bubbleBodyCursor.run)).elim

/-- Exact original-execution chronology for one generated ERC-677 callback.
The raw callback boundary, retained child, source occurrence, and chronological
descendant equation all share the same explicit `callPre`, `callPost`, slot,
and parent `pc`. -/
def Exec.Frame.CompiledTokenCallbackChronology
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (sel targetArg dataArg valueWord : B256) (pre post : Devm)
    (prefixActions : List FlowAction) : Prop :=
  ∃ (inputSize : B256) (input : Bytes)
      (callPre callPost parent child : Devm) (xl : Xlot) (pc : Nat)
      (retained : RetainedXlot xl),
    RawTokenCallbackIndexedStepBoundary dp frame.sevm
      frame.sevm.currentTarget (Sevm.argWord frame.sevm targetArg).toAdr
      (Sevm.argWord frame.sevm targetArg) sel valueWord
      (Sevm.tailLen frame.sevm dataArg) inputSize
      (Sevm.tailBytes frame.sevm dataArg) input pre post callPre callPost
      parent child xl pc ∧
    Blanc.Weth10.RetainedXlot.RawCommits retained ∧
    Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame Ninst.call callPre callPost xl ∧
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame =
      prefixActions ++ Blanc.Weth10.RetainedXlot.flowActions dp ca retained

/-- Construct the exact callback chronology directly from the original
compiled cursor.  The terminal Boolean decoder proves that no unaccounted
recursive child occurs after the selected callback edge. -/
theorem Exec.Frame.CompiledCursor.compiledTokenCallbackChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {sel targetArg dataArg valueWord : B256} {value : Line}
    {final : Devm} {img : Bytes}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (callBoolCallback sel targetArg dataArg value) final)
    (hvalueChildless : ∀ n ∈ value, NinstIsChildless n)
    (h_value_stack : ∀ {a b : Devm} {xs : Stack},
      xs <<+ a.stack → Line.Run frame.sevm a value b →
        valueWord :: xs <<+ b.stack)
    (h_value_stor : Line.Inv Devm.getStor value)
    (h_value_bal : Line.Inv Devm.getBal value)
    (h_value_code : Line.Inv Devm.getCode value)
    (h_value_mem : Line.Inv Devm.memory value)
    (h_value_logs : Line.Inv Devm.logs value)
    (h_value_output : Line.Inv Devm.output value)
    (h_wf : Mem.Wf cursor.pre.memory)
    (h_reads : Mem.Reads cursor.pre.memory img)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    Blanc.Weth10.Exec.Frame.CompiledTokenCallbackChronology dp ca frame sel targetArg dataArg
      valueWord cursor.pre final cursor.actions := by
  rcases cursor.reachCallBoolCallbackWithPrefix hvalueChildless
      h_value_stack h_value_stor h_value_bal h_value_code h_value_mem
      h_value_logs h_value_output h_wf h_reads with
    ⟨callCursor, hcallActions, hprefix⟩
  have hcompiled := callCursor.run
  cases hcompiled with
  | next hcallCompiled hboolCompiled =>
      have hcall := Ninst.Run.of_runCompiled hcallCompiled
      have hbool := Func.Run.of_runCompiled hboolCompiled
      rcases rawTokenCallbackIndexedStepBoundary_of_prefix dp sel
          targetArg dataArg valueWord hprefix hcall hbool with
        ⟨inputSize, input, parent, child, xl, pc, hraw⟩
      have hrawData := hraw
      rcases hrawData with
        ⟨_htarget, _hsize, delegated, code, gasWord, avail, hstep,
          _hdepth, _hstack, _hinput, _hreads, _hstor, _hbal, _hcode,
          _hlogs, _houtput, _hparentState, _hparentMemory,
          _hparentLogs, _hparentOutput, _hdelegation, hfilled,
          hmessage, hclean, _hresume, _hcallPostState, _hreturnData,
          _hmemory, _hcallPostStack, _hbool⟩
      obtain ⟨retained⟩ := exists_retainedXlot_of_filled hfilled
      have hcommits : Blanc.Weth10.RetainedXlot.RawCommits retained := by
        cases retained with
        | none => trivial
        | some retainedRun =>
            exact Frame.raw_commits_of_settlementCommits
              (ProcessMessage.settlementCommits_of_some_ok_clean
                hmessage hclean)
      rcases callCursor.alignCommittedCallStep hfilled hstep retained
          hcommits with
        ⟨tailCursor, _htailPre, occurrence, htailActions⟩
      have hdesc := tailCursor.finishBoolReturnCall hcode
      refine ⟨inputSize, input, callCursor.pre, _, parent, child, xl,
        pc, retained, hraw, hcommits, occurrence, ?_⟩
      calc
        Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = tailCursor.actions := hdesc
        _ = callCursor.actions ++
            Blanc.Weth10.RetainedXlot.flowActions dp ca retained :=
          htailActions
        _ = cursor.actions ++
            Blanc.Weth10.RetainedXlot.flowActions dp ca retained := by
          rw [hcallActions]

/-- Exact selector-level chronology for `depositToAndCall`.  The literal
mint-prefix endpoint is also the indexed callback entry, so its local WETH
write/log facts and world-balance/code preservation align with the retained
child occurrence rather than with a separately extracted functional run. -/
def Exec.Frame.CompiledDepositToAndCallChronology
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame) : Prop :=
  ∃ callbackPre,
    Devm.getStor callbackPre frame.sevm.currentTarget =
        (Devm.getStor frame.pre frame.sevm.currentTarget).set
          (normalizedAddressArg frame.sevm 0)
          (frame.sevm.value +
            (Devm.getStor frame.pre frame.sevm.currentTarget).get
              (normalizedAddressArg frame.sevm 0)) ∧
    callbackPre.logs = frame.pre.logs ++ [mintToTransferLog frame.sevm] ∧
    Devm.getBal callbackPre = Devm.getBal frame.pre ∧
    Devm.getCode callbackPre = Devm.getCode frame.pre ∧
    callbackPre.output = frame.pre.output ∧
    Blanc.Weth10.Exec.Frame.CompiledTokenCallbackChronology dp ca frame
      onTokenTransferSelector 0 1 frame.sevm.value callbackPre frame.post []

/-- Construct the exact `depositToAndCall` mint/callback chronology from the
authentic retained frame. -/
theorem Exec.Frame.compiledDepositToAndCallChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = depositToAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.CompiledDepositToAndCallChronology dp ca frame := by
  have hmem :
      (Sevm.selector frame.sevm, depositToAndCall) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [depositToAndCallSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorSilent (frame := frame) context hnonempty hmem with
    ⟨bodyCursor, _hbodyStack, hbodyActions, hentrySilent⟩
  unfold depositToAndCall at bodyCursor
  rcases bodyCursor.peelChildlessLine
      (line := mintToPrefix)
      (by simp [mintToPrefix, addressArg, arg, cdl, normalizeAddress,
        pushAddressMask, mstoreAt, logWith, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨callbackCursor, hmint, hcallbackActions⟩
  have hwfBody : Mem.Wf bodyCursor.pre.memory := by
    rw [← hentrySilent.memory]
    exact context.memory_wf
  have hreadsBody : Mem.Reads bodyCursor.pre.memory [] := by
    rw [← hentrySilent.memory]
    exact context.memory_reads_empty
  rcases mintToPrefix_effect hwfBody hreadsBody hmint with
    ⟨hstor, hlogs, hbal, hcode, houtput⟩
  rcases mintToPrefix_callbackMemoryFrame hwfBody hreadsBody hmint with
    ⟨hwfCallback, hreadsCallback⟩
  have hchron := callbackCursor.compiledTokenCallbackChronology
    (sel := onTokenTransferSelector) (targetArg := 0) (dataArg := 1)
    (valueWord := frame.sevm.value) (value := [Ninst.callvalue])
    (img := frame.sevm.value.toBytes)
    (by simp [NinstIsChildless])
    (by
      intro a b xs hp hline
      rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
      cases hnil
      exact prefix_of_push (of_run_callvalue hcv) hp)
    (by line_inv) (by line_inv) (by line_inv) (by line_inv)
    (by
      intro e' a b hline
      rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
      cases hnil
      exact (of_run_callvalue hcv).logs)
    (by
      intro e' a b hline
      rcases Line.of_run_cons hline with ⟨c, hcv, hnil⟩
      cases hnil
      exact (of_run_callvalue hcv).output)
    hwfCallback hreadsCallback
    context.invocation.2.2.2
  have hcallbackActionsNil : callbackCursor.actions = [] :=
    hcallbackActions.trans hbodyActions
  have hstorEntry := getStor_eq_of_state_eq hentrySilent.state
    frame.sevm.currentTarget
  have hbalEntry : Devm.getBal frame.pre = Devm.getBal bodyCursor.pre :=
    funext (getBal_eq_of_state_eq hentrySilent.state)
  have hcodeEntry : Devm.getCode frame.pre = Devm.getCode bodyCursor.pre :=
    funext (getCode_eq_of_state_eq hentrySilent.state)
  have hstor' := by
    simpa only [← hstorEntry] using hstor
  have hlogs' := by
    simpa only [← hentrySilent.logs] using hlogs
  have hbal' := hbal.trans hbalEntry.symm
  have hcode' := hcode.trans hcodeEntry.symm
  have houtput' := houtput.trans hentrySilent.output.symm
  refine ⟨callbackCursor.pre, hstor', hlogs', hbal', hcode', houtput', ?_⟩
  simpa only [hcallbackActionsNil] using hchron

/-- Exact selector-level chronology for `approveAndCall`.  The approval
prefix is balance-region silent and world-balance/code/output preserving;
the only proper child ledger is the same retained zero-value callback exposed
by the indexed raw boundary. -/
def Exec.Frame.CompiledApproveAndCallChronology
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame) : Prop :=
  ∃ callbackPre,
    Stor.Weth10Silent
      (Devm.getStor frame.pre frame.sevm.currentTarget)
      (Devm.getStor callbackPre frame.sevm.currentTarget) ∧
    callbackPre.logs = frame.pre.logs ++ [approveApprovalLog frame.sevm] ∧
    Devm.getBal callbackPre = Devm.getBal frame.pre ∧
    Devm.getCode callbackPre = Devm.getCode frame.pre ∧
    callbackPre.output = frame.pre.output ∧
    Blanc.Weth10.Exec.Frame.CompiledTokenCallbackChronology dp ca frame
      onTokenApprovalSelector 0 2 (Sevm.argWord frame.sevm 1)
      callbackPre frame.post []

/-- Construct the exact `approveAndCall` approval/callback chronology from
the authentic retained frame. -/
theorem Exec.Frame.compiledApproveAndCallChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = approveAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.CompiledApproveAndCallChronology dp ca frame := by
  have hmem :
      (Sevm.selector frame.sevm, nonpayable approveAndCall) ∈
        weth10Funcs dp := by
    rw [hselector]
    simp [approveAndCallSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorSilent (frame := frame) context hnonempty hmem with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hbodyStack, hbodyActions, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  unfold approveAndCall at bodyCursor
  rcases bodyCursor.peelChildlessLine
      (line := approvePrefix)
      (by simp [approvePrefix, allowanceKeyFromMemory, Blanc.logApprove,
        argCopy, cdc, arg, cdl, mstoreAt, logWith, pushList,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨callbackCursor, hprefix, hcallbackActions⟩
  have hwfBody : Mem.Wf bodyCursor.pre.memory := by
    rw [← hbodySilent.memory]
    exact context.memory_wf
  have hreadsBody : Mem.Reads bodyCursor.pre.memory [] := by
    rw [← hbodySilent.memory]
    exact context.memory_reads_empty
  rcases approvePrefix_callbackFrame hbodyStack hwfBody hreadsBody
      hprefix with
    ⟨_hstor, hlogs, hbal, hcode, houtput, hwfCallback,
      callbackImg, hreadsCallback⟩
  have hchron := callbackCursor.compiledTokenCallbackChronology
    (sel := onTokenApprovalSelector) (targetArg := 0) (dataArg := 2)
    (valueWord := Sevm.argWord frame.sevm 1) (value := arg 1)
    (img := callbackImg)
    (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256])
    (by
      intro a b xs hp hline
      exact prefix_of_arg hp hline)
    (by unfold arg cdl; line_inv)
    (by unfold arg cdl; line_inv)
    (by unfold arg cdl; line_inv)
    (by unfold arg cdl; line_inv)
    (by unfold arg cdl; line_inv)
    (by unfold arg cdl; line_inv)
    hwfCallback hreadsCallback context.invocation.2.2.2
  have hcallbackActionsNil : callbackCursor.actions = [] :=
    hcallbackActions.trans (hbodyActions.trans hwrapperActions)
  have hstorEntry := getStor_eq_of_state_eq hbodySilent.state
    frame.sevm.currentTarget
  have hsilent : Stor.Weth10Silent
      (Devm.getStor frame.pre frame.sevm.currentTarget)
      (Devm.getStor callbackCursor.pre frame.sevm.currentTarget) :=
    (Stor.Weth10Silent.of_eq hstorEntry).trans
      (approvePrefix_storage_silent hprefix)
  have hbalEntry : Devm.getBal frame.pre = Devm.getBal bodyCursor.pre :=
    funext (getBal_eq_of_state_eq hbodySilent.state)
  have hcodeEntry : Devm.getCode frame.pre = Devm.getCode bodyCursor.pre :=
    funext (getCode_eq_of_state_eq hbodySilent.state)
  have hlogs' := by
    simpa only [← hbodySilent.logs] using hlogs
  refine ⟨callbackCursor.pre, hsilent, hlogs', hbal.trans hbalEntry.symm,
    hcode.trans hcodeEntry.symm,
    houtput.trans hbodySilent.output.symm, ?_⟩
  simpa only [hcallbackActionsNil] using hchron

/-! ## Exact compiled value-redemption chronology -/

/-- The two concrete sources from which WETH10 redemption bodies obtain the
booked-balance owner.  Keeping this source symbolic lets one cursor proof cover
caller withdrawals and normalized-owner allowance withdrawals alike. -/
private inductive RedemptionOwnerSource where
  | caller
  | arg (k : B256)

private def RedemptionOwnerSource.line : RedemptionOwnerSource → Line
  | .caller => [Ninst.caller]
  | .arg k => addressArg k

private def RedemptionOwnerSource.word (source : RedemptionOwnerSource)
    (e : Sevm) : B256 :=
  match source with
  | .caller => e.caller.toB256
  | .arg k => normalizedAddressArg e k

private theorem RedemptionOwnerSource.valid
    (source : RedemptionOwnerSource) (e : Sevm) :
    ValidAdr (source.word e) := by
  cases source with
  | caller => exact validAdr_toB256 e.caller
  | arg k => exact normalizedAddress_valid (Sevm.argWord e k)

private theorem RedemptionOwnerSource.childless
    (source : RedemptionOwnerSource) :
    ∀ n ∈ source.line, NinstIsChildless n := by
  cases source with
  | caller => simp [RedemptionOwnerSource.line, NinstIsChildless]
  | arg k =>
      simp [RedemptionOwnerSource.line, addressArg, Blanc.arg, cdl,
        normalizeAddress, pushAddressMask, NinstIsChildless,
        Ninst.pushB256]

private theorem RedemptionOwnerSource.prefix_of_line
    (source : RedemptionOwnerSource)
    {e : Sevm} {pre post : Devm} {tail : Stack}
    (hstack : tail <<+ pre.stack)
    (run : Line.Run e pre source.line post) :
    source.word e :: tail <<+ post.stack := by
  cases source with
  | caller =>
      simp only [RedemptionOwnerSource.line] at run
      rcases Line.of_run_cons run with ⟨last, hcaller, hnil⟩
      cases hnil
      exact prefix_of_push (of_run_caller hcaller) hstack
  | arg k =>
      simpa only [RedemptionOwnerSource.line,
        RedemptionOwnerSource.word, normalizedAddressArg] using
        prefix_of_addressArg hstack run

private def redemptionLoadBalanceAmount
    (source : RedemptionOwnerSource) (amountArg : B256) : Line :=
  source.line ++ [Ninst.dup 0, Ninst.sload] ++ arg amountArg ++
    [Ninst.swap 0]

private def valueRedemptionCheckLine (source : RedemptionOwnerSource)
    (amountArg : B256) : Line :=
  redemptionLoadBalanceAmount source amountArg ++ balanceTooSmall

private theorem prefix_of_redemptionLoadBalanceAmount
    (source : RedemptionOwnerSource) (amountArg : B256)
    {e : Sevm} {pre post : Devm} {tail : Stack}
    (hstack : tail <<+ pre.stack)
    (run : Line.Run e pre
      (redemptionLoadBalanceAmount source amountArg) post) :
    ∃ balance,
      balance = (Devm.getStor pre e.currentTarget).get (source.word e) ∧
      (balance :: Sevm.argWord e amountArg :: source.word e :: tail) <<+
        post.stack := by
  cases source with
  | caller =>
      simpa only [redemptionLoadBalanceAmount,
        RedemptionOwnerSource.line, RedemptionOwnerSource.word,
        loadCallerBalanceAmount] using
        prefix_of_loadCallerBalanceAmount hstack run
  | arg k =>
      rcases prefix_of_loadArgBalanceAmount k amountArg hstack run with
        ⟨balance, key, hkey, hbalance, hp⟩
      refine ⟨balance, ?_, ?_⟩
      · simpa only [RedemptionOwnerSource.word, normalizedAddressArg,
          hkey] using hbalance
      · simpa only [RedemptionOwnerSource.word, normalizedAddressArg,
          hkey] using hp

private theorem valueRedemptionCheckLine_childless
    (source : RedemptionOwnerSource) (amountArg : B256) :
    ∀ n ∈ valueRedemptionCheckLine source amountArg,
      NinstIsChildless n := by
  cases source with
  | caller =>
      simp [valueRedemptionCheckLine, redemptionLoadBalanceAmount,
        RedemptionOwnerSource.line, balanceTooSmall, Blanc.arg, cdl,
        NinstIsChildless, Ninst.pushB256]
  | arg k =>
      simp [valueRedemptionCheckLine, redemptionLoadBalanceAmount,
        RedemptionOwnerSource.line, addressArg, normalizeAddress,
        pushAddressMask, balanceTooSmall, Blanc.arg, cdl,
        NinstIsChildless, Ninst.pushB256]

private structure RedemptionLineObservations (pre post : Devm) : Prop where
  storage : Devm.getStor pre = Devm.getStor post
  balance : Devm.getBal pre = Devm.getBal post
  code : Devm.getCode pre = Devm.getCode post
  memory : pre.memory = post.memory
  logs : pre.logs = post.logs
  output : pre.output = post.output

private theorem RedemptionOwnerSource.line_observations
    (source : RedemptionOwnerSource)
    {e : Sevm} {pre post : Devm}
    (run : Line.Run e pre source.line post) :
    RedemptionLineObservations pre post := by
  cases source with
  | caller =>
      simp only [RedemptionOwnerSource.line] at run
      exact ⟨Line.of_inv Devm.getStor (by line_inv) run,
        Line.of_inv Devm.getBal (by line_inv) run,
        Line.of_inv Devm.getCode (by line_inv) run,
        Line.of_inv Devm.memory (by line_inv) run,
        Line.of_inv Devm.logs (by line_inv) run,
        Line.of_inv Devm.output (by line_inv) run⟩
  | arg k =>
      simp only [RedemptionOwnerSource.line] at run
      exact ⟨Line.of_inv Devm.getStor (by line_inv) run,
        Line.of_inv Devm.getBal (by line_inv) run,
        Line.of_inv Devm.getCode (by line_inv) run,
        Line.of_inv Devm.memory (by line_inv) run,
        Line.of_inv Devm.logs (by line_inv) run,
        Line.of_inv Devm.output (by line_inv) run⟩

private theorem valueRedemptionCheckLine_observations
    (source : RedemptionOwnerSource) (amountArg : B256)
    {e : Sevm} {pre post : Devm}
    (run : Line.Run e pre (valueRedemptionCheckLine source amountArg) post) :
    RedemptionLineObservations pre post := by
  cases source with
  | caller =>
      unfold valueRedemptionCheckLine redemptionLoadBalanceAmount
        RedemptionOwnerSource.line at run
      exact ⟨Line.of_inv Devm.getStor (by line_inv) run,
        Line.of_inv Devm.getBal (by line_inv) run,
        Line.of_inv Devm.getCode (by line_inv) run,
        Line.of_inv Devm.memory (by line_inv) run,
        Line.of_inv Devm.logs (by line_inv) run,
        Line.of_inv Devm.output (by line_inv) run⟩
  | arg k =>
      unfold valueRedemptionCheckLine redemptionLoadBalanceAmount
        RedemptionOwnerSource.line at run
      exact ⟨Line.of_inv Devm.getStor (by line_inv) run,
        Line.of_inv Devm.getBal (by line_inv) run,
        Line.of_inv Devm.getCode (by line_inv) run,
        Line.of_inv Devm.memory (by line_inv) run,
        Line.of_inv Devm.logs (by line_inv) run,
        Line.of_inv Devm.output (by line_inv) run⟩

/-- The childless source prefix immediately before a value `CALL` has placed
the seven operands on the exact call-boundary stack and has preserved every
parent observation relevant to holder-flow accounting. -/
structure ValueCallOperandPrefix (e : Sevm) (pre callPre : Devm)
    (value target : B256) (tail : Stack) : Prop where
  stack : ∃ gasWord : B256,
    (gasWord :: target :: value :: 0 :: 0 :: 0 :: 0 :: tail) <<+
      callPre.stack
  storage : Devm.getStor pre = Devm.getStor callPre
  balance : Devm.getBal pre = Devm.getBal callPre
  code : Devm.getCode pre = Devm.getCode callPre
  memory : pre.memory = callPre.memory
  logs : pre.logs = callPre.logs
  output : pre.output = callPre.output

private def sendValueToCallerPrefix : Line :=
  pushList [0, 0, 0, 0] ++ [Ninst.swap 3, Ninst.caller, Ninst.gas]

private def sendValueToArgPrefix (k : B256) : Line :=
  pushList [0, 0, 0, 0] ++ [Ninst.swap 3] ++ arg k ++ [Ninst.gas]

private theorem sendValueToCallerPrefix_effect
    {e : Sevm} {pre callPre : Devm} {value : B256} {tail : Stack}
    (hstack : value :: tail <<+ pre.stack)
    (run : Line.Run e pre sendValueToCallerPrefix callPre) :
    ValueCallOperandPrefix e pre callPre value e.caller.toB256 tail := by
  unfold sendValueToCallerPrefix pushList at run
  simp only [List.map] at run
  rcases Line.of_run_cons run with ⟨s₁, hpush₁, run₁⟩
  have hp₁ : (0 : B256) :: value :: tail <<+ s₁.stack :=
    prefix_of_push (of_run_pushB256 hpush₁) hstack
  rcases Line.of_run_cons run₁ with ⟨s₂, hpush₂, run₂⟩
  have hp₂ : (0 : B256) :: 0 :: value :: tail <<+ s₂.stack :=
    prefix_of_push (of_run_pushB256 hpush₂) hp₁
  rcases Line.of_run_cons run₂ with ⟨s₃, hpush₃, run₃⟩
  have hp₃ : (0 : B256) :: 0 :: 0 :: value :: tail <<+ s₃.stack :=
    prefix_of_push (of_run_pushB256 hpush₃) hp₂
  rcases Line.of_run_cons run₃ with ⟨s₄, hpush₄, run₄⟩
  have hp₄ : (0 : B256) :: 0 :: 0 :: 0 :: value :: tail <<+
      s₄.stack :=
    prefix_of_push (of_run_pushB256 hpush₄) hp₃
  rcases Line.of_run_cons run₄ with ⟨s₅, hswap, run₅⟩
  have hswapCore : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: value :: tail)
      (value :: 0 :: 0 :: 0 :: 0 :: tail) :=
    Stack.swapCore_succ (Stack.swapCore_succ
      (Stack.swapCore_succ Stack.swapCore_zero))
  have hp₅ : value :: 0 :: 0 :: 0 :: 0 :: tail <<+ s₅.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp₄
  rcases Line.of_run_cons run₅ with ⟨s₆, hcaller, run₆⟩
  have hp₆ : e.caller.toB256 :: value :: 0 :: 0 :: 0 :: 0 :: tail <<+
      s₆.stack := prefix_of_push (of_run_caller hcaller) hp₅
  rcases Line.of_run_cons run₆ with ⟨last, hgas, hnil⟩
  cases hnil
  rcases of_run_gas hgas with ⟨gasWord, hpushGas⟩
  exact ⟨⟨gasWord, prefix_of_push hpushGas hp₆⟩,
    Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run,
    Line.of_inv Devm.getCode (by line_inv) run,
    Line.of_inv Devm.memory (by line_inv) run,
    Line.of_inv Devm.logs (by line_inv) run,
    Line.of_inv Devm.output (by line_inv) run⟩

private theorem sendValueToArgPrefix_effect (k : B256)
    {e : Sevm} {pre callPre : Devm} {value : B256} {tail : Stack}
    (hstack : value :: tail <<+ pre.stack)
    (run : Line.Run e pre (sendValueToArgPrefix k) callPre) :
    ValueCallOperandPrefix e pre callPre value (Sevm.argWord e k) tail := by
  unfold sendValueToArgPrefix pushList at run
  simp only [List.map] at run
  rcases Line.of_run_cons run with ⟨s₁, hpush₁, run₁⟩
  have hp₁ : (0 : B256) :: value :: tail <<+ s₁.stack :=
    prefix_of_push (of_run_pushB256 hpush₁) hstack
  rcases Line.of_run_cons run₁ with ⟨s₂, hpush₂, run₂⟩
  have hp₂ : (0 : B256) :: 0 :: value :: tail <<+ s₂.stack :=
    prefix_of_push (of_run_pushB256 hpush₂) hp₁
  rcases Line.of_run_cons run₂ with ⟨s₃, hpush₃, run₃⟩
  have hp₃ : (0 : B256) :: 0 :: 0 :: value :: tail <<+ s₃.stack :=
    prefix_of_push (of_run_pushB256 hpush₃) hp₂
  rcases Line.of_run_cons run₃ with ⟨s₄, hpush₄, run₄⟩
  have hp₄ : (0 : B256) :: 0 :: 0 :: 0 :: value :: tail <<+
      s₄.stack :=
    prefix_of_push (of_run_pushB256 hpush₄) hp₃
  rcases Line.of_run_cons run₄ with ⟨s₅, hswap, run₅⟩
  have hswapCore : Stack.Swap (3 : Fin 16).val
      ((0 : B256) :: 0 :: 0 :: 0 :: value :: tail)
      (value :: 0 :: 0 :: 0 :: 0 :: tail) :=
    Stack.swapCore_succ (Stack.swapCore_succ
      (Stack.swapCore_succ Stack.swapCore_zero))
  have hp₅ : value :: 0 :: 0 :: 0 :: 0 :: tail <<+ s₅.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp₄
  rcases of_run_append (arg k) run₅ with ⟨s₆, harg, run₆⟩
  have hp₆ : Sevm.argWord e k :: value :: 0 :: 0 :: 0 :: 0 :: tail <<+
      s₆.stack := prefix_of_arg hp₅ harg
  rcases Line.of_run_cons run₆ with ⟨last, hgas, hnil⟩
  cases hnil
  rcases of_run_gas hgas with ⟨gasWord, hpushGas⟩
  exact ⟨⟨gasWord, prefix_of_push hpushGas hp₆⟩,
    Line.of_inv Devm.getStor (by line_inv) run,
    Line.of_inv Devm.getBal (by line_inv) run,
    Line.of_inv Devm.getCode (by line_inv) run,
    Line.of_inv Devm.memory (by line_inv) run,
    Line.of_inv Devm.logs (by line_inv) run,
    Line.of_inv Devm.output (by line_inv) run⟩

/-- Exact proof-indexed chronology for one caller-owned burn followed by an
accepted value `CALL`.  The accepted trace and source occurrence share the
same retained slot; the five post-call observations explicitly delimit the
otherwise arbitrary committed child/reentrant segment. -/
def Exec.Frame.CompiledValueRedemptionChronology
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (pre : Devm) (owner : Adr) (amount target : B256)
    (prefixActions : List FlowAction) : Prop :=
  ∃ (callPre guardPost : Devm)
      (trace : AcceptedValueCallTrace frame.sevm target amount
        callPre guardPost),
    BurnCallPrefix frame.sevm pre callPre guardPost owner amount target ∧
    trace.slot = trace.retained.slot ∧
    Blanc.Weth10.RetainedXlot.RawCommits trace.retained.retained ∧
    Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame Ninst.call callPre trace.callPost
      trace.retained.slot ∧
    Devm.getStor guardPost = Devm.getStor frame.post ∧
    Devm.getBal guardPost = Devm.getBal frame.post ∧
    Devm.getCode guardPost = Devm.getCode frame.post ∧
    guardPost.logs = frame.post.logs ∧
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame =
      prefixActions ++ Blanc.Weth10.RetainedXlot.flowActions dp ca
        trace.retained.retained

/-- Rebase only the call-free entry observations of an exact redemption
chronology.  The accepted child, source occurrence, and chronological ledger
remain literally unchanged. -/
theorem Exec.Frame.CompiledValueRedemptionChronology.of_entry_eq
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {pre pre' : Devm} {owner : Adr} {amount target : B256}
    {prefixActions : List FlowAction}
    (chronology : Blanc.Weth10.Exec.Frame.CompiledValueRedemptionChronology dp ca frame pre owner
      amount target prefixActions)
    (hstor : Devm.getStor pre' = Devm.getStor pre)
    (hbal : Devm.getBal pre' = Devm.getBal pre)
    (hcode : Devm.getCode pre' = Devm.getCode pre)
    (hlogs : pre'.logs = pre.logs)
    (houtput : pre'.output = pre.output) :
    Blanc.Weth10.Exec.Frame.CompiledValueRedemptionChronology dp ca frame pre' owner amount target
      prefixActions := by
  rcases chronology with ⟨callPre, guardPost, trace, burn, rest⟩
  exact ⟨callPre, guardPost, trace,
    burn.of_entry_eq hstor hbal hcode hlogs houtput, rest⟩

private def valueRedemptionEventLine (amountArg : B256) : Line :=
  arg amountArg ++ [Ninst.pushB256 0] ++ emitTransfer ++
    [Ninst.swap 0, Ninst.pop]

private def valueRedemptionBody (source : RedemptionOwnerSource)
    (amountArg : B256) (sendPrefix : Line) (sendErrorSlot : Nat)
    (success : Func) : Func :=
  valueRedemptionCheckLine source amountArg +++
  ((.call burnBalanceErrorSlot) <?>
    (debitLoadedBalance +++
      source.line +++
      valueRedemptionEventLine amountArg +++
      sendPrefix +++
      Ninst.call ::: Ninst.iszero :::
      ((.call sendErrorSlot) <?> success)))

private theorem withdraw_eq_valueRedemptionBody :
    withdraw = valueRedemptionBody .caller 0 sendValueToCallerPrefix
      ethTransferErrorSlot Func.stop := by
  rfl

private theorem withdrawTo_eq_valueRedemptionBody :
    withdrawTo = valueRedemptionBody .caller 1 (sendValueToArgPrefix 0)
      ethTransferErrorSlot Func.stop := by
  rfl

private theorem transferZeroThen_eq_valueRedemptionBody (success : Func) :
    transferZeroThen success =
      valueRedemptionBody .caller 1 sendValueToCallerPrefix
        ethTransferErrorSlot success := by
  rfl

private theorem transferZero_eq_valueRedemptionBody :
    transferZeroThen returnTrue =
      valueRedemptionBody .caller 1 sendValueToCallerPrefix
        ethTransferErrorSlot returnTrue := by
  rfl

private theorem transferFromZero_eq_valueRedemptionBody :
    transferFromZero =
      valueRedemptionBody (.arg 0) 2 sendValueToCallerPrefix
        ethTransferErrorSlot returnTrue := by
  rfl

private theorem withdrawFromCore_eq_valueRedemptionBody :
    withdrawFromCore =
      valueRedemptionBody (.arg 0) 2 (sendValueToArgPrefix 1)
        etherTransferErrorSlot Func.stop := by
  rfl

theorem not_run_call_revWith
    {fs : List Func} {e : Sevm} {k : Nat} {reason : String}
    {final : Devm}
    (hget : fs[k]? = some (Func.revWith reason)) :
    ∀ pre, ¬ Func.Run fs e pre (.call k) final := by
  intro pre run
  rcases of_run_call run with ⟨body, bodyPre, hbody, _hburn, hrun⟩
  rw [hget] at hbody
  have heq : body = Func.revWith reason := Option.some.inj hbody.symm
  subst body
  exact Func.not_run_revWith hrun

private theorem ProcessMessageTrace.rawCommits_of_clean
    {msg : Msg} {child : Devm}
    (trace : ProcessMessageTrace msg (.ok child))
    (hclean : child.error.isSome = false) :
    Blanc.Weth10.RetainedXlot.RawCommits trace.retained := by
  rcases trace with ⟨slot, retained, hprocess⟩
  cases retained with
  | none => trivial
  | some retainedRun =>
      exact Frame.raw_commits_of_settlementCommits
        (ProcessMessage.settlementCommits_of_some_ok_clean
          hprocess hclean)

/-- Strengthen the accepted-value trace constructor with the slot identity
that its two raw witnesses share by construction. -/
private theorem exists_acceptedValueCallTrace_same_slot
    {e : Sevm} {target value : B256} {callPre guardPost : Devm}
    {img : Bytes}
    (accepted : AcceptedValueCall e target value callPre guardPost)
    (hwf : Mem.Wf callPre.memory)
    (hreads : Mem.Reads callPre.memory img) :
    ∃ trace : AcceptedValueCallTrace e target value callPre guardPost,
      trace.slot = trace.retained.slot ∧
      Mem.Wf guardPost.memory ∧ Mem.Reads guardPost.memory img := by
  rcases accepted with
    ⟨g, callPost, testPost, hstack, hcall, hiszero, hpop⟩
  rcases of_run_call_val_with_depth_frame hstack hcall with
      hfailed | hsuccess
  · exfalso
    have htest := prefix_of_iszero hiszero hfailed.1
    have hpopStack := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append,
      List.cons_append] at hpopStack
    rw [hpopStack] at htest
    have hzero : ((0 : B256) =? 0) = 0 :=
      pref_head_unique htest (pref_append [(0 : B256)] guardPost.stack)
    rw [show ((0 : B256) =? 0) = 1 from by
      simp [B256.eqCheck]] at hzero
    exact B256.zero_ne_one hzero.symm
  · rcases hsuccess with
      ⟨parent, child, slot, delegated, na, code, availableGas, pc, hstep,
        hdepth, _hcallStack, hparentState, hparentMemory,
        _hparentLogs, _hparentOutput, hdelegation, hfilled, hmessage,
        hclean, _hresume, hcallPostState, _hreturnData, hcallPostMemory,
        _hcallPostStack⟩
    rcases exists_retainedXlot_of_filled hfilled with ⟨retained⟩
    have hresolution :
        (getDelegatedCodeAddress (callPre.getCode target.toAdr) = none ∧
            code = callPre.getCode target.toAdr ∧ delegated = false) ∨
          (∃ delegatedTarget,
            getDelegatedCodeAddress (callPre.getCode target.toAdr) =
              some delegatedTarget ∧
            code = callPre.getCode delegatedTarget ∧ delegated = true) := by
      rcases hdelegation with
        ⟨hnone, _, hcode, hdp⟩ | ⟨d, hsome, _, hcode, hdp⟩
      · exact Or.inl ⟨hnone, hcode, hdp⟩
      · exact Or.inr ⟨d, hsome, hcode, hdp⟩
    have hna : na =
        (getDelegatedCodeAddress (callPre.getCode target.toAdr)).getD
          target.toAdr := by
      rcases hdelegation with
        ⟨hnone, heq, _, _⟩ | ⟨d, hsome, heq, _, _⟩
      · rw [heq, hnone]; rfl
      · rw [heq, hsome]; rfl
    rw [hna] at hmessage
    let childMessage :=
      callMsg e parent
        (min g.toNat (except64th availableGas) +
          (if value.toNat = 0 then 0 else gCallStipend))
        value e.currentTarget target.toAdr
        ((getDelegatedCodeAddress (callPre.getCode target.toAdr)).getD
          target.toAdr)
        true false
        ((callPre.memory.read (0 : B256).toNat (0 : B256).toNat).1)
        code delegated
    let childTrace : ProcessMessageTrace childMessage (.ok child) :=
      ⟨slot, retained, by simpa only [childMessage] using hmessage⟩
    have hguardState : guardPost.state = child.state := by
      calc
        guardPost.state = testPost.state := hpop.state.symm
        _ = callPost.state :=
          (Ninst.Hinv.inv (f := Devm.state) hiszero).symm
        _ = child.state := hcallPostState
    let trace : AcceptedValueCallTrace e target value callPre guardPost :=
      ⟨g, callPost, parent, child, slot, pc, hstep, hdepth,
        delegated, code, availableGas, hparentState, hresolution,
        childMessage, rfl, childTrace, hclean, hguardState⟩
    have hcallPostMemory' : callPost.memory = parent.memory := by
      simpa only [show (0 : B256).toNat = 0 from rfl, List.take_zero,
        Mem.write] using hcallPostMemory
    have hwfCallPost : Mem.Wf callPost.memory := by
      rw [hcallPostMemory', hparentMemory]
      exact Mem.Wf.extends _ hwf
    have hreadsCallPost : Mem.Reads callPost.memory img := by
      rw [hcallPostMemory', hparentMemory]
      exact Mem.Reads.extends _ hreads
    have hmemory : callPost.memory = guardPost.memory :=
      (Ninst.Hinv.inv (f := Devm.memory) hiszero).trans hpop.memory
    exact ⟨trace, rfl, by rw [← hmemory]; exact hwfCallPost,
      by rw [← hmemory]; exact hreadsCallPost⟩

private theorem debitLoadedBalance_logOutput_compiled
    {e : Sevm} {pre post : Devm}
    (run : Line.Run e pre debitLoadedBalance post) :
    pre.logs = post.logs ∧ pre.output = post.output := by
  unfold debitLoadedBalance at run
  rcases Line.of_run_cons run with ⟨afterSub, hsub, run⟩
  rcases Line.of_run_cons run with ⟨afterSwap, hswap, run⟩
  rcases Line.of_run_cons run with ⟨last, hstore, hnil⟩
  cases hnil
  have hsubLogs : pre.logs = afterSub.logs := by
    rcases of_run_reg hsub with ⟨pc, hrun⟩
    simp only [Rinst.run, Rinst.runCore] at hrun
    exact (Devm.diffBurn_of_applyBinary hrun).choose_spec.choose_spec.logs
  have hsubOutput : pre.output = afterSub.output := by
    rcases of_run_reg hsub with ⟨pc, hrun⟩
    simp only [Rinst.run, Rinst.runCore] at hrun
    exact (Devm.diffBurn_of_applyBinary hrun).choose_spec.choose_spec.output
  exact ⟨hsubLogs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) hswap).trans
        (Ninst.Hinv.inv (f := Devm.logs) hstore)),
    hsubOutput.trans
      ((Ninst.Hinv.inv (f := Devm.output) hswap).trans
        (Ninst.Hinv.inv (f := Devm.output) hstore))⟩

private theorem stop_getCode_inv :
    Func.Inv Devm.getCode Devm.getCode Func.stop := by
  intro fs e pre post run
  cases run with
  | last h =>
      simp only [Linst.Run, Linst.run] at h
      exact congrArg Devm.getCode (Except.ok.inj h)

/-- Walk a successful value-redemption body on the original compiled
execution up to its literal continuation cursor.  Both fixed reverter arms
are excluded from that same cursor, and the selected external `CALL` is tied
to the retained child before control is returned to `success`. -/
private theorem Exec.Frame.CompiledCursor.compiledValueRedemptionContinuation
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {source : RedemptionOwnerSource} {amountArg : B256}
    {sendPrefix : Line} {success : Func} {final : Devm}
    {sendErrorSlot : Nat} {sendErrorReason : String}
    {target : B256} {img : Bytes}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (valueRedemptionBody source amountArg sendPrefix sendErrorSlot
        success) final)
    (hstack : [] <<+ cursor.pre.stack)
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img)
    (hsendChildless : ∀ n ∈ sendPrefix, NinstIsChildless n)
    (hsend : ∀ {pre callPre : Devm} {value : B256} {tail : Stack},
      value :: tail <<+ pre.stack →
      Line.Run frame.sevm pre sendPrefix callPre →
      ValueCallOperandPrefix frame.sevm pre callPre value target tail)
    (hburnError :
      (((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance")))
    (hsendError :
      (((weth10 dp).main :: weth10Aux)[sendErrorSlot]? =
        some (Func.revWith sendErrorReason))) :
    ∃ (callPre : Devm)
        (successCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux)) success final)
        (trace : AcceptedValueCallTrace frame.sevm target
          (Sevm.argWord frame.sevm amountArg) callPre successCursor.pre),
      BurnCallPrefix frame.sevm cursor.pre callPre successCursor.pre
        (source.word frame.sevm).toAdr
        (Sevm.argWord frame.sevm amountArg) target ∧
      trace.slot = trace.retained.slot ∧
      Blanc.Weth10.RetainedXlot.RawCommits trace.retained.retained ∧
      Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame Ninst.call callPre trace.callPost
        trace.retained.slot ∧
      successCursor.actions = cursor.actions ++
        Blanc.Weth10.RetainedXlot.flowActions dp ca
          trace.retained.retained ∧
      Mem.Wf successCursor.pre.memory ∧
      Mem.Reads successCursor.pre.memory
        (Bytes.writeAt img 0 (Sevm.argWord frame.sevm amountArg).toBytes) := by
  unfold valueRedemptionBody at cursor
  rcases cursor.peelChildlessLine
      (line := valueRedemptionCheckLine source amountArg)
      (valueRedemptionCheckLine_childless source amountArg) with
    ⟨balanceBranchCursor, hcheck, hcheckActions⟩
  rcases balanceBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith hburnError) with
    ⟨successCursor, hbalancePopBy, hsuccessActions⟩
  have hbalancePop := Devm.PopBurn.of_popBurnBy hbalancePopBy
  unfold valueRedemptionCheckLine at hcheck
  rcases of_run_append (redemptionLoadBalanceAmount source amountArg)
      hcheck with
    ⟨afterLoad, hload, hguard⟩
  rcases prefix_of_redemptionLoadBalanceAmount source amountArg hstack
      hload with
    ⟨balance, hbalance, hloadStack⟩
  have hguardStack :
      (balance <? Sevm.argWord frame.sevm amountArg) :: balance ::
        Sevm.argWord frame.sevm amountArg :: source.word frame.sevm :: []
        <<+ balanceBranchCursor.pre.stack :=
    prefix_of_balanceTooSmall hloadStack hguard
  have hpopStack := hbalancePop.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpopStack
  rw [hpopStack] at hguardStack
  have hflag : (balance <? Sevm.argWord frame.sevm amountArg) = 0 :=
    pref_head_unique hguardStack (pref_append [0] successCursor.pre.stack)
  have hcovered : Sevm.argWord frame.sevm amountArg ≤ balance := by
    rw [← B256.not_lt]
    intro hlt
    rw [B256.ltCheck, if_pos hlt] at hflag
    exact B256.zero_ne_one hflag.symm
  rw [hflag] at hguardStack
  have hsuccessStack :
      balance :: Sevm.argWord frame.sevm amountArg ::
        source.word frame.sevm :: [] <<+ successCursor.pre.stack :=
    cons_pref_cons_inv hguardStack
  rcases successCursor.peelChildlessLine
      (line := debitLoadedBalance)
      (by simp [debitLoadedBalance, NinstIsChildless]) with
    ⟨afterDebitCursor, hdebit, hdebitActions⟩
  have hcheckObs :=
    valueRedemptionCheckLine_observations source amountArg hcheck
  have hstorPreSuccess : Devm.getStor cursor.pre =
      Devm.getStor successCursor.pre :=
    hcheckObs.storage.trans (PopBurn.Inv.inv hbalancePop)
  have hbalanceSuccess : balance =
      (Devm.getStor successCursor.pre frame.sevm.currentTarget).get
        (source.word frame.sevm) := by
    rw [← congrFun hstorPreSuccess frame.sevm.currentTarget]
    exact hbalance
  obtain ⟨hdecrease, hcovered', hflash⟩ :=
    debitLoadedBalance_storage (source.valid frame.sevm)
      hbalanceSuccess hcovered hsuccessStack hdebit
  rcases afterDebitCursor.peelChildlessLine
      (line := source.line) source.childless with
    ⟨eventCursor, howner, hownerActions⟩
  have hownerObs := source.line_observations howner
  have hownerStack : source.word frame.sevm :: [] <<+
      eventCursor.pre.stack := source.prefix_of_line nil_pref howner
  rcases eventCursor.peelChildlessLine
      (line := valueRedemptionEventLine amountArg)
      (by simp [valueRedemptionEventLine, arg, cdl, emitTransfer,
        Blanc.transferFromLog, mstoreAt, logWith, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨sendCursor, hevent, heventActions⟩
  have hmemoryPreEvent : cursor.pre.memory = eventCursor.pre.memory := by
    calc
      cursor.pre.memory = balanceBranchCursor.pre.memory :=
        hcheckObs.memory
      _ = successCursor.pre.memory := hbalancePop.memory
      _ = afterDebitCursor.pre.memory :=
        Line.of_inv Devm.memory (by line_inv) hdebit
      _ = eventCursor.pre.memory :=
        hownerObs.memory
  have hwfEvent : Mem.Wf eventCursor.pre.memory := by
    rw [← hmemoryPreEvent]
    exact hwf
  have hreadsEvent : Mem.Reads eventCursor.pre.memory img := by
    rw [← hmemoryPreEvent]
    exact hreads
  rcases burnEventTail_effect_frame hownerStack hwfEvent hreadsEvent
      (by simpa only [valueRedemptionEventLine] using hevent) with
    ⟨hsendStack, heventLogs, heventStor, heventBal, heventCode,
      heventOutput, hwfSend, hreadsSend⟩
  rcases sendCursor.peelChildlessLine
      (line := sendPrefix) hsendChildless with
    ⟨callCursor, hsendRun, hsendActions⟩
  have sendEvidence := hsend hsendStack hsendRun
  rcases callCursor.selectNextWithActions with
    ⟨testCursor, actualSlot, actualSelected, actualOccurrence,
      _actualEdge, htestActions⟩
  have actualOccurrenceData := actualOccurrence
  rcases actualOccurrenceData with
    ⟨actualPc, _actualCurrent, _actualContinuation, _actualBefore,
      _actualSelected', _actualPrefix, _actualAt, actualFilled,
      actualStep, _actualPrec, _actualEdge'⟩
  have hcall : Ninst.Run frame.sevm callCursor.pre Ninst.call
      testCursor.pre := ⟨actualSlot, actualFilled, actualPc, actualStep⟩
  rcases testCursor.selectNextChildless (by
      simp [NinstIsChildless]) with
    ⟨guardBranchCursor, _testSlot, hiszero, _testOccurrence,
      htestGuardActions⟩
  rcases guardBranchCursor.selectBranchLeftWithBurn
      (not_run_call_revWith hsendError) with
    ⟨terminalCursor, hguardPopBy, hterminalActions⟩
  have hguardPop := Devm.PopBurn.of_popBurnBy hguardPopBy
  rcases sendEvidence.stack with ⟨gasWord, hcallStack⟩
  let accepted : AcceptedValueCall frame.sevm target
      (Sevm.argWord frame.sevm amountArg) callCursor.pre
        terminalCursor.pre :=
    ⟨gasWord, testCursor.pre, guardBranchCursor.pre, hcallStack,
      hcall, hiszero, hguardPop⟩
  have hwfCall : Mem.Wf callCursor.pre.memory := by
    rw [← sendEvidence.memory]
    exact hwfSend
  have hreadsCall : Mem.Reads callCursor.pre.memory
      (Bytes.writeAt img 0 (Sevm.argWord frame.sevm amountArg).toBytes) := by
    rw [← sendEvidence.memory]
    exact hreadsSend
  rcases exists_acceptedValueCallTrace_same_slot accepted
      hwfCall hreadsCall with
    ⟨trace, htraceSlot, hwfTerminal, hreadsTerminal⟩
  have hcommits :
      Blanc.Weth10.RetainedXlot.RawCommits trace.retained.retained :=
    ProcessMessageTrace.rawCommits_of_clean trace.retained trace.child_clean
  have traceStep : Ninst.StepRun trace.pc frame.sevm callCursor.pre
      Ninst.call trace.retained.slot (.ok trace.callPost) := by
    simpa only [htraceSlot] using trace.step
  have halign := Ninst.StepRun.unique_exec_of_filled
    trace.retained.retained.toFilled actualFilled traceStep actualStep
  have hslot : trace.retained.slot = actualSlot := halign.1
  have hpost : trace.callPost = testCursor.pre :=
    Except.ok.inj halign.2
  subst actualSlot
  have traceOccurrence : Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame Ninst.call
      callCursor.pre trace.callPost trace.retained.slot := by
    simpa only [← hpost] using actualOccurrence
  have hcallAt : Ninst.At frame.sevm.code callCursor.pc Ninst.call :=
    ninstAt_of_subcode_next callCursor.codeSlice
  have actualStepAt : Ninst.StepRun callCursor.pc frame.sevm
      callCursor.pre Ninst.call trace.retained.slot (.ok testCursor.pre) :=
    Ninst.stepRun_pc_irrel (pc' := callCursor.pc)
      (by simp [Ninst.pcFree]) actualStep
  have hselected : actualSelected =
      Blanc.Weth10.RetainedXlot.flowActions dp ca
        trace.retained.retained :=
    _actualEdge.selected_eq_retained_of_call hcallAt actualFilled
      actualStepAt trace.retained.retained hcommits
  have hstorAfterDebitCall : Devm.getStor afterDebitCursor.pre =
      Devm.getStor callCursor.pre :=
    hownerObs.storage.trans
      (heventStor.symm.trans sendEvidence.storage)
  have hlogsPreAfterDebit : cursor.pre.logs = afterDebitCursor.pre.logs :=
    hcheckObs.logs.trans
      (hbalancePop.logs.trans
        (debitLoadedBalance_logOutput_compiled hdebit).1)
  have hownerLogs : afterDebitCursor.pre.logs = eventCursor.pre.logs :=
    hownerObs.logs
  have houtputPreAfterDebit : cursor.pre.output =
      afterDebitCursor.pre.output :=
    hcheckObs.output.trans
      (hbalancePop.output.trans
        (debitLoadedBalance_logOutput_compiled hdebit).2)
  have hownerOutput : afterDebitCursor.pre.output = eventCursor.pre.output :=
    hownerObs.output
  have hbalPreCall : Devm.getBal cursor.pre =
      Devm.getBal callCursor.pre :=
    hcheckObs.balance.trans
      ((PopBurn.Inv.inv hbalancePop).trans
        ((Line.of_inv Devm.getBal (by line_inv) hdebit).trans
          (hownerObs.balance.trans
            (heventBal.symm.trans sendEvidence.balance))))
  have hcodePreCall : Devm.getCode cursor.pre =
      Devm.getCode callCursor.pre :=
    hcheckObs.code.trans
      ((funext (getCode_eq_of_state_eq hbalancePop.state)).trans
        ((Line.of_inv Devm.getCode (by line_inv) hdebit).trans
          (hownerObs.code.trans
            (heventCode.symm.trans sendEvidence.code))))
  have burn : BurnCallPrefix frame.sevm cursor.pre callCursor.pre
      terminalCursor.pre (source.word frame.sevm).toAdr
      (Sevm.argWord frame.sevm amountArg) target := by
    unfold BurnCallPrefix
    refine ⟨?_, ?_, ?_, ?_, hbalPreCall.symm, hcodePreCall.symm, ?_,
      accepted⟩
    · simpa only [toB256_toAdr (source.valid frame.sevm),
          ← congrFun hstorPreSuccess frame.sevm.currentTarget,
          congrFun hstorAfterDebitCall frame.sevm.currentTarget] using
        hdecrease
    · simpa only [toB256_toAdr (source.valid frame.sevm),
          ← congrFun hstorPreSuccess frame.sevm.currentTarget] using
        hcovered'
    · rw [← congrFun hstorAfterDebitCall frame.sevm.currentTarget,
          hflash,
          ← congrFun hstorPreSuccess frame.sevm.currentTarget]
    · rw [toB256_toAdr (source.valid frame.sevm),
          ← sendEvidence.logs, heventLogs, ← hownerLogs,
          ← hlogsPreAfterDebit]
    · exact sendEvidence.output.symm.trans
        (heventOutput.trans
          (hownerOutput.symm.trans houtputPreAfterDebit.symm))
  have hcallPrefixActions : callCursor.actions = cursor.actions :=
    hsendActions.trans (heventActions.trans
      (hownerActions.trans (hdebitActions.trans
        (hsuccessActions.trans hcheckActions))))
  have hsuccessActionsExact : terminalCursor.actions =
      cursor.actions ++ Blanc.Weth10.RetainedXlot.flowActions dp ca
        trace.retained.retained := by
    calc
      terminalCursor.actions = guardBranchCursor.actions := hterminalActions
      _ = testCursor.actions := htestGuardActions
      _ = callCursor.actions ++ actualSelected := htestActions
      _ = callCursor.actions ++
          Blanc.Weth10.RetainedXlot.flowActions dp ca
            trace.retained.retained := by rw [hselected]
      _ = cursor.actions ++
          Blanc.Weth10.RetainedXlot.flowActions dp ca
            trace.retained.retained := by
        rw [hcallPrefixActions]
  exact ⟨callCursor.pre, terminalCursor, trace, burn, htraceSlot,
    hcommits, traceOccurrence, hsuccessActionsExact,
    hwfTerminal, hreadsTerminal⟩

/-- Walk a successful value-redemption body on the original compiled
execution.  Both fixed reverter arms are excluded from that same cursor; the
selected external `CALL` is tied to the retained accepted-value trace before
a childless terminal suffix is closed. -/
theorem Exec.Frame.CompiledCursor.compiledValueRedemptionChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {source : RedemptionOwnerSource} {amountArg : B256}
    {sendPrefix successLine : Line} {successLast : Linst}
    {sendErrorSlot : Nat} {sendErrorReason : String}
    {target : B256} {img : Bytes}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (valueRedemptionBody source amountArg sendPrefix sendErrorSlot
        (successLine +++ Func.last successLast))
      frame.post)
    (hstack : [] <<+ cursor.pre.stack)
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img)
    (hsendChildless : ∀ n ∈ sendPrefix, NinstIsChildless n)
    (hsuccessChildless : ∀ n ∈ successLine, NinstIsChildless n)
    (hsuccessStor : Func.Inv Devm.getStor Devm.getStor
      (successLine +++ Func.last successLast))
    (hsuccessBal : Func.Inv Devm.getBal Devm.getBal
      (successLine +++ Func.last successLast))
    (hsuccessCode : Func.Inv Devm.getCode Devm.getCode
      (successLine +++ Func.last successLast))
    (hsuccessLogs : Func.Inv Devm.logs Devm.logs
      (successLine +++ Func.last successLast))
    (hsend : ∀ {pre callPre : Devm} {value : B256} {tail : Stack},
      value :: tail <<+ pre.stack →
      Line.Run frame.sevm pre sendPrefix callPre →
      ValueCallOperandPrefix frame.sevm pre callPre value target tail)
    (hburnError :
      (((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]? =
        some (Func.revWith "WETH: burn amount exceeds balance")))
    (hsendError :
      (((weth10 dp).main :: weth10Aux)[sendErrorSlot]? =
        some (Func.revWith sendErrorReason))) :
    Blanc.Weth10.Exec.Frame.CompiledValueRedemptionChronology dp ca frame cursor.pre
      (source.word frame.sevm).toAdr
      (Sevm.argWord frame.sevm amountArg) target
      cursor.actions := by
  rcases cursor.compiledValueRedemptionContinuation hstack hwf hreads
      hsendChildless hsend hburnError hsendError with
    ⟨callPre, successCursor, trace, burn, htraceSlot, hcommits,
      occurrence, hsuccessActions, _hwfSuccess, _hreadsSuccess⟩
  have hsuccessRun : Func.Run
      ((weth10 dp).main :: weth10Aux) frame.sevm successCursor.pre
      (successLine +++ Func.last successLast) frame.post :=
    Func.Run.of_runCompiled successCursor.run
  have hpostStor : Devm.getStor successCursor.pre =
      Devm.getStor frame.post := hsuccessStor hsuccessRun
  have hpostBal : Devm.getBal successCursor.pre =
      Devm.getBal frame.post := hsuccessBal hsuccessRun
  have hpostCode : Devm.getCode successCursor.pre =
      Devm.getCode frame.post := hsuccessCode hsuccessRun
  have hpostLogs : successCursor.pre.logs = frame.post.logs :=
    hsuccessLogs hsuccessRun
  have hdesc := successCursor.finishTerminalChildlessLine
    hsuccessChildless
  have hdescExact : Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame =
      cursor.actions ++ Blanc.Weth10.RetainedXlot.flowActions dp ca
        trace.retained.retained :=
    hdesc.trans hsuccessActions
  exact ⟨callPre, successCursor.pre, trace, burn, htraceSlot,
    hcommits, occurrence, hpostStor, hpostBal, hpostCode, hpostLogs,
    hdescExact⟩

/-- Enter the successful continuation of `transferZeroThen` on the original
compiled cursor.  The returned cursor is the literal post-guard boundary,
with the accepted value child's retained actions already appended and the
event-word memory image preserved for a following callback. -/
theorem Exec.Frame.CompiledCursor.enterTransferZeroThen
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {success : Func} {final : Devm} {img : Bytes}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (transferZeroThen success) final)
    (hstack : [] <<+ cursor.pre.stack)
    (hwf : Mem.Wf cursor.pre.memory)
    (hreads : Mem.Reads cursor.pre.memory img) :
    ∃ (callPre guardPost : Devm)
        (trace : AcceptedValueCallTrace frame.sevm
          frame.sevm.caller.toB256 (Sevm.argWord frame.sevm 1)
          callPre guardPost)
        (successCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux)) success final),
      BurnCallPrefix frame.sevm cursor.pre callPre guardPost
        frame.sevm.caller (Sevm.argWord frame.sevm 1)
        frame.sevm.caller.toB256 ∧
      trace.slot = trace.retained.slot ∧
      Blanc.Weth10.RetainedXlot.RawCommits trace.retained.retained ∧
      Blanc.Weth10.Exec.Frame.NinstOccurrence dp ca frame Ninst.call callPre trace.callPost
        trace.retained.slot ∧
      successCursor.pre = guardPost ∧
      successCursor.actions = cursor.actions ++
        Blanc.Weth10.RetainedXlot.flowActions dp ca
          trace.retained.retained ∧
      Mem.Wf successCursor.pre.memory ∧
      Mem.Reads successCursor.pre.memory
        (Bytes.writeAt img 0 (Sevm.argWord frame.sevm 1).toBytes) := by
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (valueRedemptionBody .caller 1 sendValueToCallerPrefix
      ethTransferErrorSlot success) final at cursor
  rcases cursor.compiledValueRedemptionContinuation
      (sendErrorReason := "WETH: ETH transfer failed")
      hstack hwf hreads
      (by simp [sendValueToCallerPrefix, pushList, NinstIsChildless,
        Ninst.pushB256])
      (by
        intro pre callPre value tail hp hrun
        exact sendValueToCallerPrefix_effect hp hrun)
      (by simp [weth10, weth10Aux, burnBalanceErrorSlot,
        burnBalanceError])
      (by simp [weth10, weth10Aux, ethTransferErrorSlot,
        ethTransferError]) with
    ⟨callPre, successCursor, trace, burn, htraceSlot, hcommits,
      occurrence, hactions, hwfSuccess, hreadsSuccess⟩
  refine ⟨callPre, successCursor.pre, trace, successCursor, ?_,
    htraceSlot, hcommits, occurrence, rfl, hactions,
    hwfSuccess, hreadsSuccess⟩
  simpa only [RedemptionOwnerSource.word, toAdr_toB256] using burn

/-- Exact original-execution redemption chronology for `withdraw(uint256)`.
The public entry/dispatch/nonpayable prefix is rebased only through its proved
observation equalities. -/
theorem Exec.Frame.compiledWithdrawChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.CompiledValueRedemptionChronology dp ca frame frame.pre
      frame.sevm.caller (Sevm.argWord frame.sevm 0)
      frame.sevm.caller.toB256 [] := by
  have hmem :
      (Sevm.selector frame.sevm, nonpayable withdraw) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [withdrawSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorSilent (frame := frame) context hnonempty hmem with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hbodyStack, hbodyActions, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (valueRedemptionBody .caller 0 sendValueToCallerPrefix
      ethTransferErrorSlot Func.stop) frame.post at bodyCursor
  have hwfBody : Mem.Wf bodyCursor.pre.memory := by
    rw [← hbodySilent.memory]
    exact context.memory_wf
  have hreadsBody : Mem.Reads bodyCursor.pre.memory [] := by
    rw [← hbodySilent.memory]
    exact context.memory_reads_empty
  have chronology := bodyCursor.compiledValueRedemptionChronology
    (successLine := []) (successLast := .stop)
    (sendErrorReason := "WETH: ETH transfer failed")
    hbodyStack hwfBody hreadsBody
    (by simp [sendValueToCallerPrefix, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by simp)
    (by func_inv)
    (by func_inv)
    stop_getCode_inv
    (by func_inv)
    (by
      intro pre callPre value tail hp hrun
      exact sendValueToCallerPrefix_effect hp hrun)
    (by simp [weth10, weth10Aux, burnBalanceErrorSlot,
      burnBalanceError])
    (by simp [weth10, weth10Aux, ethTransferErrorSlot,
      ethTransferError])
  have rebased := chronology.of_entry_eq
    (funext (getStor_eq_of_state_eq hbodySilent.state))
    (funext (getBal_eq_of_state_eq hbodySilent.state))
    (funext (getCode_eq_of_state_eq hbodySilent.state))
    hbodySilent.logs hbodySilent.output
  have hactions : bodyCursor.actions = [] :=
    hbodyActions.trans hwrapperActions
  simpa only [hactions, RedemptionOwnerSource.word, toAdr_toB256] using
    rebased

/-- Exact original-execution redemption chronology for
`withdrawTo(address,uint256)`, retaining the raw ABI target word used by the
actual value `CALL`. -/
theorem Exec.Frame.compiledWithdrawToChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.CompiledValueRedemptionChronology dp ca frame frame.pre
      frame.sevm.caller (Sevm.argWord frame.sevm 1)
      (Sevm.argWord frame.sevm 0) [] := by
  have hmem :
      (Sevm.selector frame.sevm, nonpayable withdrawTo) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [withdrawToSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorSilent (frame := frame) context hnonempty hmem with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, hbodyStack, hbodyActions, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (valueRedemptionBody .caller 1 (sendValueToArgPrefix 0)
      ethTransferErrorSlot Func.stop) frame.post at bodyCursor
  have hwfBody : Mem.Wf bodyCursor.pre.memory := by
    rw [← hbodySilent.memory]
    exact context.memory_wf
  have hreadsBody : Mem.Reads bodyCursor.pre.memory [] := by
    rw [← hbodySilent.memory]
    exact context.memory_reads_empty
  have chronology := bodyCursor.compiledValueRedemptionChronology
    (successLine := []) (successLast := .stop)
    (sendErrorReason := "WETH: ETH transfer failed")
    hbodyStack hwfBody hreadsBody
    (by simp [sendValueToArgPrefix, pushList, arg, cdl,
      NinstIsChildless, Ninst.pushB256])
    (by simp)
    (by func_inv)
    (by func_inv)
    stop_getCode_inv
    (by func_inv)
    (by
      intro pre callPre value tail hp hrun
      exact sendValueToArgPrefix_effect 0 hp hrun)
    (by simp [weth10, weth10Aux, burnBalanceErrorSlot,
      burnBalanceError])
    (by simp [weth10, weth10Aux, ethTransferErrorSlot,
      ethTransferError])
  have rebased := chronology.of_entry_eq
    (funext (getStor_eq_of_state_eq hbodySilent.state))
    (funext (getBal_eq_of_state_eq hbodySilent.state))
    (funext (getCode_eq_of_state_eq hbodySilent.state))
    hbodySilent.logs hbodySilent.output
  have hactions : bodyCursor.actions = [] :=
    hbodyActions.trans hwrapperActions
  simpa only [hactions, RedemptionOwnerSource.word, toAdr_toB256] using
    rebased

private def returnTruePrefixCompiled : Line :=
  [Ninst.pushB256 1] ++ mstoreAt 0 ++ pushList [32, 0]

private theorem returnTrue_eq_prefixCompiled :
    returnTrue = returnTruePrefixCompiled +++ Func.ret := by
  rfl

private theorem returnTrue_getCode_inv :
    Func.Inv Devm.getCode Devm.getCode
      (returnTruePrefixCompiled +++ Func.ret) := by
  intro fs e pre post run
  exact (of_returnTrue_exact nil_pref (by
    simpa only [returnTrue_eq_prefixCompiled] using run)).2

private def transferZeroSelectLine : Line := arg 0 ++ [Ninst.iszero]

/-- Exact selector-level chronology for `transfer(address,uint256)` when the
raw recipient word is zero.  The Boolean `RETURN` suffix is retained only
through the observations it actually preserves. -/
theorem Exec.Frame.compiledTransferZeroChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 0 = 0) :
    Blanc.Weth10.Exec.Frame.CompiledValueRedemptionChronology dp ca frame frame.pre
      frame.sevm.caller (Sevm.argWord frame.sevm 1)
      frame.sevm.caller.toB256 [] := by
  have hmem :
      (Sevm.selector frame.sevm, nonpayable transfer) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [transferSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorSilent (frame := frame) context hnonempty hmem with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨bodyCursor, _hbodyStack, hbodyActions, hnonpayableSilent⟩
  have hbodySilent : Devm.DispatchSilent frame.pre bodyCursor.pre :=
    hentrySilent.trans hnonpayableSilent
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferZeroSelectLine +++
      (transferZeroThen returnTrue <?> transferNonzeroThen returnTrue))
    frame.post at bodyCursor
  rcases bodyCursor.peelChildlessLine
      (by simp [transferZeroSelectLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine, htargetActions⟩
  have htargetPrefix :
      [Sevm.argWord frame.sevm 0 =? 0] <<+
        targetBranchCursor.pre.stack := by
    unfold transferZeroSelectLine at htargetLine
    rcases of_run_append (arg 0) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    exact prefix_of_iszero hzero (prefix_of_arg nil_pref harg)
  rw [hto] at htargetPrefix
  have hone : ((0 : B256) =? 0) = 1 := by simp [B256.eqCheck]
  rw [hone] at htargetPrefix
  rcases targetBranchCursor.selectBranchSuccSilent (flag := (1 : B256))
      (by decide) htargetPrefix with
    ⟨zeroCursor, _hzeroStack, hzeroActions, hbranchSilent⟩
  have hownStor : Devm.getStor frame.pre =
      Devm.getStor zeroCursor.pre :=
    (funext (getStor_eq_of_state_eq hbodySilent.state)).trans
      ((Line.of_inv Devm.getStor (by line_inv) htargetLine).trans
        (funext (getStor_eq_of_state_eq hbranchSilent.state)))
  have hownBal : Devm.getBal frame.pre = Devm.getBal zeroCursor.pre :=
    (funext (getBal_eq_of_state_eq hbodySilent.state)).trans
      ((Line.of_inv Devm.getBal (by line_inv) htargetLine).trans
        (funext (getBal_eq_of_state_eq hbranchSilent.state)))
  have hownCode : Devm.getCode frame.pre = Devm.getCode zeroCursor.pre :=
    (funext (getCode_eq_of_state_eq hbodySilent.state)).trans
      ((Line.of_inv Devm.getCode (by line_inv) htargetLine).trans
        (funext (getCode_eq_of_state_eq hbranchSilent.state)))
  have hownMemory : frame.pre.memory = zeroCursor.pre.memory :=
    hbodySilent.memory.trans
      ((Line.of_inv Devm.memory (by line_inv) htargetLine).trans
        hbranchSilent.memory)
  have hownLogs : frame.pre.logs = zeroCursor.pre.logs :=
    hbodySilent.logs.trans
      ((Line.of_inv Devm.logs (by line_inv) htargetLine).trans
        hbranchSilent.logs)
  have hownOutput : frame.pre.output = zeroCursor.pre.output :=
    hbodySilent.output.trans
      ((Line.of_inv Devm.output (by line_inv) htargetLine).trans
        hbranchSilent.output)
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (valueRedemptionBody .caller 1 sendValueToCallerPrefix
      ethTransferErrorSlot
      (returnTruePrefixCompiled +++ Func.ret)) frame.post at zeroCursor
  have hwfZero : Mem.Wf zeroCursor.pre.memory := by
    rw [← hownMemory]
    exact context.memory_wf
  have hreadsZero : Mem.Reads zeroCursor.pre.memory [] := by
    rw [← hownMemory]
    exact context.memory_reads_empty
  have chronology := zeroCursor.compiledValueRedemptionChronology
    (successLine := returnTruePrefixCompiled) (successLast := .ret)
    (sendErrorReason := "WETH: ETH transfer failed")
    nil_pref hwfZero hreadsZero
    (by simp [sendValueToCallerPrefix, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by simp [returnTruePrefixCompiled, mstoreAt, pushList,
      NinstIsChildless, Ninst.pushB256])
    (by unfold returnTruePrefixCompiled; func_inv)
    (by unfold returnTruePrefixCompiled; func_inv)
    returnTrue_getCode_inv
    (by unfold returnTruePrefixCompiled; func_inv)
    (by
      intro pre callPre value tail hp hrun
      exact sendValueToCallerPrefix_effect hp hrun)
    (by simp [weth10, weth10Aux, burnBalanceErrorSlot,
      burnBalanceError])
    (by simp [weth10, weth10Aux, ethTransferErrorSlot,
      ethTransferError])
  have rebased := chronology.of_entry_eq
    hownStor hownBal hownCode hownLogs hownOutput
  have hactions : zeroCursor.actions = [] :=
    hzeroActions.trans (htargetActions.trans
      (hbodyActions.trans hwrapperActions))
  simpa only [hactions, RedemptionOwnerSource.word, toAdr_toB256] using
    rebased

/-- The exact observations needed to connect an allowance wrapper's entry to
the internal balance core.  Approval logs and tagged allowance storage may
change, but booked balances, the flash slot, ETH balances, and code do not. -/
structure AllowancePrefixObservations (e : Sevm) (pre post : Devm) : Prop where
  storage : Stor.Weth10Silent
    (Devm.getStor pre e.currentTarget) (Devm.getStor post e.currentTarget)
  balance : Devm.getBal pre = Devm.getBal post
  code : Devm.getCode pre = Devm.getCode post
  memory : ∀ {img : Bytes},
    Mem.Wf pre.memory → Mem.Reads pre.memory img →
    Mem.Wf post.memory ∧ ∃ out, Mem.Reads post.memory out

private theorem AllowancePrefixObservations.of_dispatchSilent
    {e : Sevm} {pre post : Devm}
    (silent : Devm.DispatchSilent pre post) :
    AllowancePrefixObservations e pre post :=
  ⟨Stor.Weth10Silent.of_eq
      (congrArg (fun state : State => state.getStor e.currentTarget)
        silent.state),
    funext (getBal_eq_of_state_eq silent.state),
    funext (getCode_eq_of_state_eq silent.state), by
      intro img hwf hreads
      rw [← silent.memory]
      exact ⟨hwf, img, hreads⟩⟩

private theorem AllowancePrefixObservations.of_line
    {e : Sevm} {pre post : Devm} {line : Line}
    (hstor : Line.Inv Devm.getStor line)
    (hbal : Line.Inv Devm.getBal line)
    (hcode : Line.Inv Devm.getCode line)
    (hmemory : Line.Inv Devm.memory line)
    (run : Line.Run e pre line post) :
    AllowancePrefixObservations e pre post := by
  have stor := Line.of_inv Devm.getStor hstor run
  exact ⟨Stor.Weth10Silent.of_eq
      (congrFun stor e.currentTarget),
    Line.of_inv Devm.getBal hbal run,
    Line.of_inv Devm.getCode hcode run, by
      intro img hwf hreads
      rw [← Line.of_inv Devm.memory hmemory run]
      exact ⟨hwf, img, hreads⟩⟩

private theorem AllowancePrefixObservations.trans
    {e : Sevm} {pre mid post : Devm}
    (h₁ : AllowancePrefixObservations e pre mid)
    (h₂ : AllowancePrefixObservations e mid post) :
    AllowancePrefixObservations e pre post :=
  ⟨h₁.storage.trans h₂.storage,
    h₁.balance.trans h₂.balance,
    h₁.code.trans h₂.code, by
      intro img hwf hreads
      rcases h₁.memory hwf hreads with ⟨hwfMid, out, hreadsMid⟩
      exact h₂.memory hwfMid hreadsMid⟩

/-- Internal source calls are generated from push/jump/jumpdest only, hence
reaching the called body preserves the allowance-prefix observations. -/
private theorem Exec.Frame.CompiledCursor.enterCallSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
          (table 0 (f₀ :: aux)) body final,
        bodyCursor.actions = cursor.actions ∧
        Devm.DispatchSilent cursor.pre bodyCursor.pre := by
  cases hrun : cursor.run with
  | call hget hroom hburn hbody =>
      rcases subcode_compile_call cursor.codeSlice with
        ⟨loc, p, hgetTable, hloc, hpushAt, hjump⟩
      have hpf := (Prog.get?_table (m := 0)).symm.trans
        (congrArg (Prod.snd <$> ·) hgetTable)
      rw [hget] at hpf
      simp only [Option.map_eq_map, Option.map_some,
        Option.some.injEq] at hpf
      subst p
      rcases subcode_of_get?_eq_some hcode hgetTable with
        ⟨hjumpdest, hsub⟩
      have hjumpable := Prog.jumpable_of_get?_table hcode hgetTable
      rcases hpushAt with ⟨le, hpush⟩
      rcases Evm.call_steps (le := le) hpush hjump hjumpdest
          hjumpable.1 hloc hroom hburn with
        ⟨hstepPush, hstepJump, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) cursor.current cursor.parentPrefix
          hstepPush with
        ⟨afterPush, hprefixPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterPush hprefixPush hstepJump with
        ⟨afterJump, hprefixJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont (frame := frame) afterJump hprefixJump hstepJumpdest with
        ⟨bodyExec, hprefixBody⟩
      let bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
          (table 0 (f₀ :: aux)) _ final :=
        ⟨loc + 1, _, bodyExec, cursor.actions, hprefixBody,
          hbody, hsub, hjumpable.2⟩
      exact ⟨_, hget, bodyCursor, rfl,
        Devm.DispatchSilent.of_burnBy hburn⟩

private def spendOwnerEqLineCompiled : Line :=
  arg 0 ++ [Ninst.caller, Ninst.eq]

private def spendAllowanceLoadLineCompiled : Line :=
  arg 0 ++ mstoreAt 0 ++ [Ninst.caller] ++ mstoreAt 1 ++
    allowanceKeyFromMemory ++
    [Ninst.dup 0, Ninst.sload, Ninst.dup 0] ++ isMax

private def spendAllowanceCheckLineCompiled (amount : B256) : Line :=
  arg amount ++ [Ninst.swap 0] ++ balanceTooSmall

private def spendAllowanceBeforeStoreCompiled : Line :=
  [Ninst.sub, Ninst.dup 0, Ninst.swap 1]

private def spendAllowanceAfterStoreCompiled : Line :=
  arg 0 ++ [Ninst.swap 0, Ninst.caller] ++ emitApproval ++
    [Ninst.pop, Ninst.pop]

private theorem allowanceKeyPrefix_memory
    {e : Sevm} {pre post : Devm} {img : Bytes}
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory img)
    (run : Line.Run e pre
      (arg 0 ++ mstoreAt 0 ++ [Ninst.caller] ++ mstoreAt 1 ++
        allowanceKeyFromMemory) post) :
    Mem.Wf post.memory ∧ ∃ out, Mem.Reads post.memory out := by
  rcases of_run_append (arg 0) run with ⟨s₁, howner, run⟩
  have hp₁ : Sevm.argWord e 0 :: [] <<+ s₁.stack :=
    prefix_of_arg nil_pref howner
  rcases of_run_append (mstoreAt 0) run with ⟨s₂, hstoreOwner, run⟩
  rcases of_run_mstoreAt_val hstoreOwner hp₁ with ⟨hp₂, hmem₂⟩
  have hmem₂' : s₂.memory =
      s₁.memory.write 0 (Sevm.argWord e 0).toBytes := by
    simpa only [show (0 * 32 : B256).toNat = 0 by decide +kernel]
      using hmem₂
  have hmemOwner : pre.memory = s₁.memory :=
    Line.of_inv Devm.memory (by unfold arg cdl; line_inv) howner
  rcases Line.of_run_cons run with ⟨s₃, hcaller, run⟩
  have hcallerPush := of_run_caller hcaller
  have hp₃ : e.caller.toB256 :: [] <<+ s₃.stack :=
    prefix_of_push hcallerPush hp₂
  rcases of_run_append (mstoreAt 1) run with ⟨s₄, hstoreCaller, hkey⟩
  rcases of_run_mstoreAt_val hstoreCaller hp₃ with ⟨hp₄, hmem₄⟩
  have hmem₄' : s₄.memory =
      s₃.memory.write 32 e.caller.toB256.toBytes := by
    simpa only [show (1 * 32 : B256).toNat = 32 by decide +kernel]
      using hmem₄
  let img₁ := Bytes.writeAt img 0 (Sevm.argWord e 0).toBytes
  let img₂ := Bytes.writeAt img₁ 32 e.caller.toB256.toBytes
  have hwf₄ : Mem.Wf s₄.memory := by
    rw [hmem₄', ← hcallerPush.memory, hmem₂', ← hmemOwner]
    exact (hwf.write 0 (Sevm.argWord e 0).toBytes).write
      32 e.caller.toB256.toBytes
  have hreads₄ : Mem.Reads s₄.memory img₂ := by
    rw [hmem₄', ← hcallerPush.memory, hmem₂', ← hmemOwner]
    exact Mem.Reads.write
      (hwf.write 0 (Sevm.argWord e 0).toBytes)
      (Mem.Reads.write hwf hreads 0 (Sevm.argWord e 0).toBytes)
      32 e.caller.toB256.toBytes
  rcases prefix_of_allowanceKeyFromMemory_image hp₄ hwf₄ hreads₄ hkey with
    ⟨_hp, hwfPost, hreadsPost⟩
  exact ⟨hwfPost, img₂, hreadsPost⟩

private theorem spendAllowanceLoadLine_memory
    {e : Sevm} {pre post : Devm} {img : Bytes}
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory img)
    (run : Line.Run e pre spendAllowanceLoadLineCompiled post) :
    Mem.Wf post.memory ∧ ∃ out, Mem.Reads post.memory out := by
  let keyLine : Line :=
    arg 0 ++ mstoreAt 0 ++ [Ninst.caller] ++ mstoreAt 1 ++
      allowanceKeyFromMemory
  unfold spendAllowanceLoadLineCompiled at run
  rcases of_run_append keyLine run with ⟨afterKey, hkey, htail⟩
  obtain ⟨hwfKey, out, hreadsKey⟩ :=
    allowanceKeyPrefix_memory hwf hreads (by
      simpa only [keyLine] using hkey)
  have hmemory : afterKey.memory = post.memory :=
    Line.of_inv Devm.memory (by line_inv) htail
  rw [← hmemory]
  exact ⟨hwfKey, out, hreadsKey⟩

private theorem spendAllowanceAfterStoreLine_memory
    {e : Sevm} {pre post : Devm} {reduced : B256} {img : Bytes}
    (hp : reduced :: [] <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory img)
    (run : Line.Run e pre spendAllowanceAfterStoreCompiled post) :
    Mem.Wf post.memory ∧ ∃ out, Mem.Reads post.memory out := by
  unfold spendAllowanceAfterStoreCompiled at run
  rcases of_run_append (arg 0) run with ⟨s₁, howner, run⟩
  have hp₁ : Sevm.argWord e 0 :: reduced :: [] <<+ s₁.stack :=
    prefix_of_arg hp howner
  rcases Line.of_run_cons run with ⟨s₂, hswap, run⟩
  have hswapCore : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord e 0, reduced] [reduced, Sevm.argWord e 0] :=
    Stack.swapCore_zero
  have hp₂ : reduced :: Sevm.argWord e 0 :: [] <<+ s₂.stack :=
    Stack.prefix_of_swap hswapCore (of_run_swap hswap) hp₁
  rcases Line.of_run_cons run with ⟨s₃, hcaller, run⟩
  have hp₃ : e.caller.toB256 :: reduced :: Sevm.argWord e 0 :: [] <<+
      s₃.stack := prefix_of_push (of_run_caller hcaller) hp₂
  rcases of_run_append emitApproval run with ⟨s₄, hemit, run⟩
  have hmemory : pre.memory = s₃.memory :=
    (Line.of_inv Devm.memory (by line_inv) howner).trans
      ((Ninst.Hinv.inv (f := Devm.memory) hswap).trans
        (of_run_caller hcaller).memory)
  have hwf₃ : Mem.Wf s₃.memory := by
    rw [← hmemory]
    exact hwf
  have hreads₃ : Mem.Reads s₃.memory img := by
    rw [← hmemory]
    exact hreads
  obtain ⟨_hp, _hlogs, _hstor, _hbal, _hcode, _houtput,
      hwf₄, out, hreads₄⟩ :=
    emitApproval_effect hp₃ hwf₃ hreads₃ hemit
  rcases Line.of_run_cons run with ⟨s₅, hpop₁, run⟩
  rcases Line.of_run_cons run with ⟨s₆, hpop₂, hnil⟩
  cases hnil
  have hmemoryPost : s₄.memory = post.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) hpop₁).trans
      (Ninst.Hinv.inv (f := Devm.memory) hpop₂)
  rw [← hmemoryPost]
  exact ⟨hwf₄, out, hreads₄⟩

/-- Follow the actual successful allowance wrapper to its internal core.
Every source instruction in the wrapper is childless; the only alternate
internal call is the fixed allowance reverter, which cannot lead to the
committed final state. -/
theorem Exec.Frame.CompiledCursor.enterSpendCallerAllowanceThen
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {amount : B256} {nextSlot : Nat}
    {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
      (table 0 (f₀ :: aux))
      (spendCallerAllowanceThen amount nextSlot) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (hallowanceError :
      (f₀ :: aux)[allowanceErrorSlot]? = some allowanceError) :
    ∃ body,
      (f₀ :: aux)[nextSlot]? = some body ∧
      ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
          (table 0 (f₀ :: aux)) body final,
        bodyCursor.actions = cursor.actions := by
  unfold spendCallerAllowanceThen at cursor
  rcases cursor.peelChildlessLine
      (line := arg 0 ++ [Ninst.caller, Ninst.eq])
      (by simp [arg, cdl, NinstIsChildless, Ninst.pushB256]) with
    ⟨callerBranchCursor, _hcallerLine, hcallerActions⟩
  rcases callerBranchCursor.selectBranchWithActions with
      hallowance | hdirect
  · rcases hallowance with ⟨allowanceCursor, hallowanceActions⟩
    rcases allowanceCursor.peelChildlessLine
        (line := arg 0 ++ mstoreAt 0 ++ [Ninst.caller] ++ mstoreAt 1 ++
          allowanceKeyFromMemory ++
          [Ninst.dup 0, Ninst.sload, Ninst.dup 0] ++ isMax)
        (by simp [arg, cdl, mstoreAt, allowanceKeyFromMemory, pushList,
          isMax, NinstIsChildless, Ninst.pushB256]) with
      ⟨maxBranchCursor, _hloadLine, hloadActions⟩
    rcases maxBranchCursor.selectBranchWithActions with
        hfinite | hmax
    · rcases hfinite with ⟨finiteCursor, hfiniteActions⟩
      rcases finiteCursor.peelChildlessLine
          (line := arg amount ++ [Ninst.swap 0] ++ balanceTooSmall)
          (by simp [arg, cdl, balanceTooSmall, NinstIsChildless,
            Ninst.pushB256]) with
        ⟨spendBranchCursor, _hspendCheck, hspendCheckActions⟩
      rcases spendBranchCursor.selectBranchWithActions with
          hsuccess | herror
      · rcases hsuccess with ⟨successCursor, hsuccessActions⟩
        rcases successCursor.peelChildlessLine
            (line := [Ninst.sub, Ninst.dup 0, Ninst.swap 1,
                Ninst.sstore] ++
              arg 0 ++ [Ninst.swap 0, Ninst.caller] ++ emitApproval ++
              [Ninst.pop, Ninst.pop])
            (by simp [arg, cdl, emitApproval, mstoreAt,
              logWith, NinstIsChildless, Ninst.pushB256]) with
          ⟨coreCallCursor, _hwriteLine, hwriteActions⟩
        rcases coreCallCursor.enterCall hcode with
          ⟨body, hget, bodyCursor, hbodyActions⟩
        exact ⟨body, hget, bodyCursor, hbodyActions.trans
          (hwriteActions.trans (hsuccessActions.trans
            (hspendCheckActions.trans (hfiniteActions.trans
              (hloadActions.trans (hallowanceActions.trans
                (hcallerActions)))))))⟩
      · rcases herror with ⟨errorCursor, _herrorActions⟩
        rcases errorCursor.enterCall hcode with
          ⟨body, hget, bodyCursor, _hbodyActions⟩
        have hbody : body = allowanceError := by
          rw [hallowanceError] at hget
          exact Option.some.inj hget.symm
        subst body
        exact (Func.not_run_revWith
          (Func.Run.of_runCompiled bodyCursor.run)).elim
    · rcases hmax with ⟨maxCursor, hmaxActions⟩
      rcases maxCursor.peelChildlessLine
          (line := [Ninst.pop, Ninst.pop])
          (by simp [NinstIsChildless]) with
        ⟨coreCallCursor, _hpopLine, hpopActions⟩
      rcases coreCallCursor.enterCall hcode with
        ⟨body, hget, bodyCursor, hbodyActions⟩
      exact ⟨body, hget, bodyCursor, hbodyActions.trans
        (hpopActions.trans (hmaxActions.trans
          (hloadActions.trans (hallowanceActions.trans
            hcallerActions))))⟩
  · rcases hdirect with ⟨directCursor, hdirectActions⟩
    rcases directCursor.enterCall hcode with
      ⟨body, hget, bodyCursor, hbodyActions⟩
    exact ⟨body, hget, bodyCursor, hbodyActions.trans
      (hdirectActions.trans hcallerActions)⟩

/-- Follow the same exact allowance wrapper while also retaining the
balance/flash-slot, ETH-balance, and code observations needed to start a
delegated redemption at the reached core cursor. -/
theorem Exec.Frame.CompiledCursor.enterSpendCallerAllowanceThenWithObservations
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {amount : B256} {nextSlot : Nat}
    {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
      (table 0 (f₀ :: aux))
      (spendCallerAllowanceThen amount nextSlot) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (hallowanceError :
      (f₀ :: aux)[allowanceErrorSlot]? = some allowanceError) :
    ∃ body,
      (f₀ :: aux)[nextSlot]? = some body ∧
      ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame (f₀ :: aux)
          (table 0 (f₀ :: aux)) body final,
        bodyCursor.actions = cursor.actions ∧
        AllowancePrefixObservations frame.sevm cursor.pre
          bodyCursor.pre := by
  unfold spendCallerAllowanceThen at cursor
  rcases cursor.peelChildlessLine
      (line := spendOwnerEqLineCompiled)
      (by simp [spendOwnerEqLineCompiled, arg, cdl,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨callerBranchCursor, hcallerLine, hcallerActions⟩
  have hcallerPrefix :
      [frame.sevm.caller.toB256 =? Sevm.argWord frame.sevm 0] <<+
        callerBranchCursor.pre.stack := by
    unfold spendOwnerEqLineCompiled at hcallerLine
    rcases of_run_append (arg 0) hcallerLine with
      ⟨afterArg, harg, hcallerEq⟩
    rcases Line.of_run_cons hcallerEq with
      ⟨afterCaller, hcaller, heqLine⟩
    rcases Line.of_run_cons heqLine with ⟨afterEq, heq, hnil⟩
    cases hnil
    exact prefix_of_eq heq
      (prefix_of_push (of_run_caller hcaller)
        (prefix_of_arg nil_pref harg))
  have hcallerObs : AllowancePrefixObservations frame.sevm
      cursor.pre callerBranchCursor.pre :=
    AllowancePrefixObservations.of_line (by
      unfold spendOwnerEqLineCompiled
      line_inv) (by
      unfold spendOwnerEqLineCompiled
      line_inv) (by
      unfold spendOwnerEqLineCompiled
      line_inv) (by
      unfold spendOwnerEqLineCompiled
      line_inv) hcallerLine
  by_cases hselfFlag :
      (frame.sevm.caller.toB256 =? Sevm.argWord frame.sevm 0) = 0
  · rw [hselfFlag] at hcallerPrefix
    rcases callerBranchCursor.selectBranchZeroSilent hcallerPrefix with
      ⟨allowanceCursor, _hallowanceStack, hallowanceActions,
        hallowanceBranchSilent⟩
    rcases allowanceCursor.peelChildlessLine
        (line := spendAllowanceLoadLineCompiled)
        (by simp [spendAllowanceLoadLineCompiled, arg, cdl, mstoreAt,
          allowanceKeyFromMemory, pushList, isMax, NinstIsChildless,
          Ninst.pushB256]) with
      ⟨maxBranchCursor, hloadLine, hloadActions⟩
    rcases prefix_of_callerAllowanceIsMax 0 nil_pref hloadLine with
      ⟨hash, allowance, _hallowance, hloadPrefix⟩
    have hloadObs : AllowancePrefixObservations frame.sevm
        allowanceCursor.pre maxBranchCursor.pre :=
      ⟨Stor.Weth10Silent.of_eq (congrFun
          (Line.of_inv Devm.getStor (by
            unfold spendAllowanceLoadLineCompiled
            line_inv) hloadLine) frame.sevm.currentTarget),
        Line.of_inv Devm.getBal (by
          unfold spendAllowanceLoadLineCompiled
          line_inv) hloadLine,
        Line.of_inv Devm.getCode (by
          unfold spendAllowanceLoadLineCompiled
          line_inv) hloadLine, by
        intro img hwf hreads
        exact spendAllowanceLoadLine_memory hwf hreads hloadLine⟩
    by_cases hmaxFlag : ((~~~ allowance) =? 0) = 0
    · rw [hmaxFlag] at hloadPrefix
      rcases maxBranchCursor.selectBranchZeroSilent hloadPrefix with
        ⟨finiteCursor, hfinitePrefix, hfiniteActions,
          hfiniteBranchSilent⟩
      rcases finiteCursor.peelChildlessLine
          (line := spendAllowanceCheckLineCompiled amount)
          (by simp [spendAllowanceCheckLineCompiled, arg, cdl,
            balanceTooSmall, NinstIsChildless, Ninst.pushB256]) with
        ⟨spendBranchCursor, hcheckLine, hcheckActions⟩
      have hguardPrefix :
          (allowance <? Sevm.argWord frame.sevm amount) :: allowance ::
            Sevm.argWord frame.sevm amount ::
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: []
              <<+ spendBranchCursor.pre.stack := by
        unfold spendAllowanceCheckLineCompiled at hcheckLine
        rcases of_run_append (arg amount) hcheckLine with
          ⟨afterAmount, hamount, hafterAmount⟩
        rcases Line.of_run_cons hafterAmount with
          ⟨afterSwap, hswap, hguard⟩
        have hpAmount : Sevm.argWord frame.sevm amount :: allowance ::
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: []
              <<+ afterAmount.stack :=
          prefix_of_arg hfinitePrefix hamount
        have hswapCore : Stack.Swap (0 : Fin 16).val
            (Sevm.argWord frame.sevm amount :: allowance ::
              (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [])
            (allowance :: Sevm.argWord frame.sevm amount ::
              (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: []) :=
          Stack.swapCore_zero
        exact prefix_of_balanceTooSmall
          (Stack.prefix_of_swap hswapCore (of_run_swap hswap) hpAmount)
          hguard
      rcases spendBranchCursor.selectBranchLeftWithBurn
          (not_run_call_revWith (by
            simpa only [allowanceError] using hallowanceError)) with
        ⟨successCursor, hsuccessPopBy, hsuccessActions⟩
      have hsuccessPrefix : allowance ::
          Sevm.argWord frame.sevm amount ::
          (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: []
            <<+ successCursor.pre.stack :=
        prefix_of_pop
          ⟨0, Devm.PopBurn.of_popBurnBy hsuccessPopBy⟩ hguardPrefix
      rcases successCursor.peelChildlessLine
          (line := spendAllowanceBeforeStoreCompiled)
          (by simp [spendAllowanceBeforeStoreCompiled,
            NinstIsChildless]) with
        ⟨storeCursor, hbeforeStore, hbeforeActions⟩
      rcases Line.of_run_cons hbeforeStore with
        ⟨afterSub, hsub, hbeforeStore⟩
      rcases Line.of_run_cons hbeforeStore with
        ⟨afterDup, hdup, hbeforeStore⟩
      rcases Line.of_run_cons hbeforeStore with
        ⟨afterSwap, hswap, hnil⟩
      cases hnil
      have hsubPrefix :
          (allowance - Sevm.argWord frame.sevm amount) ::
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: []
              <<+ afterSub.stack := prefix_of_sub hsub hsuccessPrefix
      have hdupPrefix :
          (allowance - Sevm.argWord frame.sevm amount) ::
            (allowance - Sevm.argWord frame.sevm amount) ::
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: []
              <<+ afterDup.stack :=
        prefix_of_dup_val hdup (by show_nth) hsubPrefix
      have hstoreSwap : Stack.Swap (1 : Fin 16).val
          ((allowance - Sevm.argWord frame.sevm amount) ::
            (allowance - Sevm.argWord frame.sevm amount) ::
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [])
          ((allowanceTagWord ||| (allowancePayloadMask &&& hash)) ::
            (allowance - Sevm.argWord frame.sevm amount) ::
            (allowance - Sevm.argWord frame.sevm amount) :: []) :=
        Stack.swapCore_succ Stack.swapCore_zero
      have hstorePrefix :
          (allowanceTagWord ||| (allowancePayloadMask &&& hash)) ::
            (allowance - Sevm.argWord frame.sevm amount) ::
            (allowance - Sevm.argWord frame.sevm amount) :: []
              <<+ storeCursor.pre.stack :=
        Stack.prefix_of_swap hstoreSwap (of_run_swap hswap) hdupPrefix
      rcases storeCursor.selectNextChildless (by
          simp [NinstIsChildless]) with
        ⟨afterStoreCursor, _storeSlot, hstore, _storeOccurrence,
          hstoreActions⟩
      rcases afterStoreCursor.peelChildlessLine
          (line := spendAllowanceAfterStoreCompiled)
          (by simp [spendAllowanceAfterStoreCompiled, arg, cdl,
            emitApproval, mstoreAt, logWith, NinstIsChildless,
            Ninst.pushB256]) with
        ⟨coreCallCursor, hafterStore, hafterActions⟩
      have hset : Devm.getStor afterStoreCursor.pre
          frame.sevm.currentTarget =
          (Devm.getStor storeCursor.pre frame.sevm.currentTarget).set
            (allowanceTagWord ||| (allowancePayloadMask &&& hash))
            (allowance - Sevm.argWord frame.sevm amount) :=
        sstore_getStor_set hstore hstorePrefix
      have hstoreSilent : Stor.Weth10Silent
          (Devm.getStor storeCursor.pre frame.sevm.currentTarget)
          (Devm.getStor afterStoreCursor.pre frame.sevm.currentTarget) := by
        rw [hset]
        exact Stor.Weth10Silent.set
          (runtimeAllowanceKey_not_valid hash)
          (runtimeAllowanceKey_ne_flash hash)
      have hmutationObs : AllowancePrefixObservations frame.sevm
          successCursor.pre coreCallCursor.pre := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact (Stor.Weth10Silent.of_eq (congrFun
              (Line.of_inv Devm.getStor (by
                line_inv) (Line.Run.cons hsub
                  (Line.Run.cons hdup
                    (Line.Run.cons hswap Line.Run.nil))))
              frame.sevm.currentTarget)).trans
            (hstoreSilent.trans
              (Stor.Weth10Silent.of_eq (congrFun
                (Line.of_inv Devm.getStor (by
                  unfold spendAllowanceAfterStoreCompiled
                  line_inv) hafterStore)
                frame.sevm.currentTarget)))
        · exact (Line.of_inv Devm.getBal (by
              line_inv) (Line.Run.cons hsub
                (Line.Run.cons hdup (Line.Run.cons hswap Line.Run.nil)))).trans
            ((Ninst.Hinv.inv (f := Devm.getBal) hstore).trans
              (Line.of_inv Devm.getBal (by
                unfold spendAllowanceAfterStoreCompiled
                line_inv) hafterStore))
        · exact (Line.of_inv Devm.getCode (by
              line_inv) (Line.Run.cons hsub
                (Line.Run.cons hdup (Line.Run.cons hswap Line.Run.nil)))).trans
            ((Ninst.Hinv.inv (f := Devm.getCode) hstore).trans
              (Line.of_inv Devm.getCode (by
                unfold spendAllowanceAfterStoreCompiled
                line_inv) hafterStore))
        · intro img hwf hreads
          have hbeforeMemory : successCursor.pre.memory =
              storeCursor.pre.memory :=
            Line.of_inv Devm.memory (by line_inv)
              (Line.Run.cons hsub
                (Line.Run.cons hdup (Line.Run.cons hswap Line.Run.nil)))
          have hstoreMemory : storeCursor.pre.memory =
              afterStoreCursor.pre.memory :=
            Ninst.Hinv.inv (f := Devm.memory) hstore
          have hafterPrefix :
              (allowance - Sevm.argWord frame.sevm amount) :: [] <<+
                afterStoreCursor.pre.stack :=
            prefix_of_sstore hstore hstorePrefix
          have hwfAfter : Mem.Wf afterStoreCursor.pre.memory := by
            rw [← hstoreMemory, ← hbeforeMemory]
            exact hwf
          have hreadsAfter : Mem.Reads afterStoreCursor.pre.memory img := by
            rw [← hstoreMemory, ← hbeforeMemory]
            exact hreads
          exact spendAllowanceAfterStoreLine_memory hafterPrefix
            hwfAfter hreadsAfter hafterStore
      rcases coreCallCursor.enterCallSilent hcode with
        ⟨body, hget, bodyCursor, hbodyActions, hcallSilent⟩
      have hp₁ := hcallerObs.trans
        (AllowancePrefixObservations.of_dispatchSilent
          hallowanceBranchSilent)
      have hp₂ := hp₁.trans hloadObs
      have hp₃ := hp₂.trans
        (AllowancePrefixObservations.of_dispatchSilent
          hfiniteBranchSilent)
      have hp₄ := hp₃.trans
        (AllowancePrefixObservations.of_line (by
          unfold spendAllowanceCheckLineCompiled
          line_inv) (by
          unfold spendAllowanceCheckLineCompiled
          line_inv) (by
          unfold spendAllowanceCheckLineCompiled
          line_inv) (by
          unfold spendAllowanceCheckLineCompiled
          line_inv) hcheckLine)
      have hp₅ := hp₄.trans
        (AllowancePrefixObservations.of_dispatchSilent
          (Devm.DispatchSilent.of_popBurnBy hsuccessPopBy))
      have hp₆ := hp₅.trans hmutationObs
      have hp := hp₆.trans
        (AllowancePrefixObservations.of_dispatchSilent hcallSilent)
      exact ⟨body, hget, bodyCursor,
        hbodyActions.trans (hafterActions.trans
          (hstoreActions.trans (hbeforeActions.trans
            (hsuccessActions.trans (hcheckActions.trans
              (hfiniteActions.trans (hloadActions.trans
                (hallowanceActions.trans hcallerActions)))))))), hp⟩
    · rcases maxBranchCursor.selectBranchSuccSilent hmaxFlag
          hloadPrefix with
        ⟨maxCursor, _hmaxStack, hmaxActions, hmaxBranchSilent⟩
      rcases maxCursor.peelChildlessLine
          (line := [Ninst.pop, Ninst.pop])
          (by simp [NinstIsChildless]) with
        ⟨coreCallCursor, hpopLine, hpopActions⟩
      rcases coreCallCursor.enterCallSilent hcode with
        ⟨body, hget, bodyCursor, hbodyActions, hcallSilent⟩
      have hp₁ := hcallerObs.trans
        (AllowancePrefixObservations.of_dispatchSilent
          hallowanceBranchSilent)
      have hp₂ := hp₁.trans hloadObs
      have hp₃ := hp₂.trans
        (AllowancePrefixObservations.of_dispatchSilent hmaxBranchSilent)
      have hp₄ := hp₃.trans
        (AllowancePrefixObservations.of_line (by line_inv)
          (by line_inv) (by line_inv) (by line_inv) hpopLine)
      have hp := hp₄.trans
        (AllowancePrefixObservations.of_dispatchSilent hcallSilent)
      exact ⟨body, hget, bodyCursor,
        hbodyActions.trans (hpopActions.trans
          (hmaxActions.trans (hloadActions.trans
            (hallowanceActions.trans hcallerActions)))), hp⟩
  · rcases callerBranchCursor.selectBranchSuccSilent hselfFlag
        hcallerPrefix with
      ⟨directCursor, _hdirectStack, hdirectActions, hdirectBranchSilent⟩
    rcases directCursor.enterCallSilent hcode with
      ⟨body, hget, bodyCursor, hbodyActions, hcallSilent⟩
    exact ⟨body, hget, bodyCursor,
      hbodyActions.trans (hdirectActions.trans hcallerActions),
      hcallerObs.trans
        ((AllowancePrefixObservations.of_dispatchSilent
          hdirectBranchSilent).trans
          (AllowancePrefixObservations.of_dispatchSilent hcallSilent))⟩

private def transferFromSelectLine : Line := arg 1 ++ [Ninst.iszero]

/-- Exact selector-level chronology for delegated `transferFrom` when the raw
recipient word is zero.  The allowance prefix retains its literal reached
owner cursor, including a possible finite allowance write and `Approval` log;
the redemption chronology therefore starts at that cursor rather than being
rebased across the allowance mutation. -/
theorem Exec.Frame.compiledTransferFromZeroChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 1 = 0) :
    ∃ ownPre,
      AllowancePrefixObservations frame.sevm frame.pre ownPre ∧
      Blanc.Weth10.Exec.Frame.CompiledValueRedemptionChronology dp ca frame ownPre
        (normalizedAddressArg frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 2) frame.sevm.caller.toB256 [] := by
  have hmem :
      (Sevm.selector frame.sevm, nonpayable transferFrom) ∈
        weth10Funcs dp := by
    rw [hselector]
    simp [transferFromSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorSilent (frame := frame) context hnonempty hmem with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨transferCursor, _htransferStack, htransferActions,
      hnonpayableSilent⟩
  have hentryObs : AllowancePrefixObservations frame.sevm frame.pre
      transferCursor.pre :=
    AllowancePrefixObservations.of_dispatchSilent
      (hentrySilent.trans hnonpayableSilent)
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (spendCallerAllowanceThen 2 transferFromCoreSlot) frame.post at transferCursor
  rcases transferCursor.enterSpendCallerAllowanceThenWithObservations
      context.invocation.2.2.2 (by
        simp [weth10, weth10Aux, allowanceErrorSlot]) with
    ⟨body, hget, coreCursor, hcoreActions, hallowanceObs⟩
  have hbody : body = transferFromCore := by
    simpa [weth10, weth10Aux, transferFromCoreSlot] using hget.symm
  subst body
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferFromSelectLine +++
      (transferFromZero <?> transferFromNonzero)) frame.post at coreCursor
  rcases coreCursor.peelChildlessLine
      (by simp [transferFromSelectLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine, htargetActions⟩
  have htargetPrefix :
      [Sevm.argWord frame.sevm 1 =? 0] <<+
        targetBranchCursor.pre.stack := by
    unfold transferFromSelectLine at htargetLine
    rcases of_run_append (arg 1) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    exact prefix_of_iszero hzero (prefix_of_arg nil_pref harg)
  rw [hto] at htargetPrefix
  have hone : ((0 : B256) =? 0) = 1 := by simp [B256.eqCheck]
  rw [hone] at htargetPrefix
  rcases targetBranchCursor.selectBranchSuccSilent (flag := (1 : B256))
      (by decide) htargetPrefix with
    ⟨zeroCursor, _hzeroStack, hzeroActions, hbranchSilent⟩
  have hselectObs : AllowancePrefixObservations frame.sevm
      coreCursor.pre zeroCursor.pre :=
    (AllowancePrefixObservations.of_line (by line_inv) (by line_inv)
      (by line_inv) (by line_inv) htargetLine).trans
      (AllowancePrefixObservations.of_dispatchSilent hbranchSilent)
  have hownObs : AllowancePrefixObservations frame.sevm frame.pre
      zeroCursor.pre :=
    hentryObs.trans (hallowanceObs.trans hselectObs)
  obtain ⟨hwfZero, img, hreadsZero⟩ :=
    hownObs.memory context.memory_wf context.memory_reads_empty
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (valueRedemptionBody (.arg 0) 2 sendValueToCallerPrefix
      ethTransferErrorSlot
      (returnTruePrefixCompiled +++ Func.ret)) frame.post at zeroCursor
  have chronology := zeroCursor.compiledValueRedemptionChronology
    (successLine := returnTruePrefixCompiled) (successLast := .ret)
    (sendErrorReason := "WETH: ETH transfer failed")
    nil_pref hwfZero hreadsZero
    (by simp [sendValueToCallerPrefix, pushList, NinstIsChildless,
      Ninst.pushB256])
    (by simp [returnTruePrefixCompiled, mstoreAt, pushList,
      NinstIsChildless, Ninst.pushB256])
    (by unfold returnTruePrefixCompiled; func_inv)
    (by unfold returnTruePrefixCompiled; func_inv)
    returnTrue_getCode_inv
    (by unfold returnTruePrefixCompiled; func_inv)
    (by
      intro pre callPre value tail hp hrun
      exact sendValueToCallerPrefix_effect hp hrun)
    (by simp [weth10, weth10Aux, burnBalanceErrorSlot,
      burnBalanceError])
    (by simp [weth10, weth10Aux, ethTransferErrorSlot,
      ethTransferError])
  have hactions : zeroCursor.actions = [] :=
    hzeroActions.trans (htargetActions.trans
      (hcoreActions.trans (htransferActions.trans hwrapperActions)))
  refine ⟨zeroCursor.pre, hownObs, ?_⟩
  simpa only [hactions, RedemptionOwnerSource.word] using chronology

/-- Exact selector-level chronology for `withdrawFrom`.  The returned
allowance observations connect frame entry to the literal post-allowance
owner cursor, while the accepted value child and descendant ledger remain
owned by the redemption chronology starting there. -/
theorem Exec.Frame.compiledWithdrawFromChronology
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ ownPre,
      AllowancePrefixObservations frame.sevm frame.pre ownPre ∧
      Blanc.Weth10.Exec.Frame.CompiledValueRedemptionChronology dp ca frame ownPre
        (normalizedAddressArg frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 2) (Sevm.argWord frame.sevm 1) [] := by
  have hmem :
      (Sevm.selector frame.sevm, nonpayable withdrawFrom) ∈
        weth10Funcs dp := by
    rw [hselector]
    simp [withdrawFromSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorSilent (frame := frame) context hnonempty hmem with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions, hentrySilent⟩
  rcases wrapperCursor.enterNonpayableSilent with
    ⟨withdrawCursor, _hwithdrawStack, hwithdrawActions,
      hnonpayableSilent⟩
  have hentryObs : AllowancePrefixObservations frame.sevm frame.pre
      withdrawCursor.pre :=
    AllowancePrefixObservations.of_dispatchSilent
      (hentrySilent.trans hnonpayableSilent)
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (spendCallerAllowanceThen 2 withdrawFromCoreSlot) frame.post at withdrawCursor
  rcases withdrawCursor.enterSpendCallerAllowanceThenWithObservations
      context.invocation.2.2.2 (by
        simp [weth10, weth10Aux, allowanceErrorSlot]) with
    ⟨body, hget, ownCursor, hownActions, hallowanceObs⟩
  have hbody : body = withdrawFromCore := by
    simpa [weth10, weth10Aux, withdrawFromCoreSlot] using hget.symm
  subst body
  have hownObs : AllowancePrefixObservations frame.sevm frame.pre
      ownCursor.pre := hentryObs.trans hallowanceObs
  obtain ⟨hwfOwn, img, hreadsOwn⟩ :=
    hownObs.memory context.memory_wf context.memory_reads_empty
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (valueRedemptionBody (.arg 0) 2 (sendValueToArgPrefix 1)
      etherTransferErrorSlot Func.stop) frame.post at ownCursor
  have chronology := ownCursor.compiledValueRedemptionChronology
    (successLine := []) (successLast := .stop)
    (sendErrorReason := "WETH: Ether transfer failed")
    nil_pref hwfOwn hreadsOwn
    (by simp [sendValueToArgPrefix, pushList, arg, cdl,
      NinstIsChildless, Ninst.pushB256])
    (by simp)
    (by func_inv)
    (by func_inv)
    stop_getCode_inv
    (by func_inv)
    (by
      intro pre callPre value tail hp hrun
      exact sendValueToArgPrefix_effect 1 hp hrun)
    (by simp [weth10, weth10Aux, burnBalanceErrorSlot,
      burnBalanceError])
    (by simp [weth10, weth10Aux, etherTransferErrorSlot,
      etherTransferError])
  have hactions : ownCursor.actions = [] :=
    hownActions.trans (hwithdrawActions.trans hwrapperActions)
  refine ⟨ownCursor.pre, hownObs, ?_⟩
  simpa only [hactions, RedemptionOwnerSource.word] using chronology

private def transferFromBalanceCheckLine : Line :=
  loadArgBalanceAmount 0 2 ++ balanceTooSmall

private def transferFromNonzeroSuccessLine : Line :=
  debitLoadedBalance ++
  addressArg 1 ++ [Ninst.dup 0, Ninst.sload] ++ arg 2 ++
  [Ninst.add, Ninst.swap 0, Ninst.sstore] ++
  addressArg 0 ++ arg 2 ++ addressArg 1 ++ emitTransfer ++
  [Ninst.pushB256 1] ++ mstoreAt 0 ++ pushList [32, 0]

/-- A successful `transferFrom` to a nonzero recipient has no proper child
execution.  The allowance wrapper, finite allowance update, transfer writes,
log, and Boolean return are all childless; the fixed reverter alternatives
cannot be the retained frame's committed continuation. -/
theorem Exec.Frame.descendantFlowActions_eq_nil_of_transferFromNonzero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 1 ≠ 0) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = [] := by
  have hmem :
      (Sevm.selector frame.sevm, nonpayable transferFrom) ∈
        weth10Funcs dp := by
    rw [hselector]
    simp [transferFromSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursor (frame := frame) context hnonempty hmem with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions⟩
  rcases wrapperCursor.enterNonpayable with
    ⟨transferCursor, _htransferStack, htransferActions⟩
  rcases transferCursor.enterSpendCallerAllowanceThen
      context.invocation.2.2.2 (by
        simp [weth10, weth10Aux, allowanceErrorSlot]) with
    ⟨body, hget, coreCursor, hcoreActions⟩
  have hbody : body = transferFromCore := by
    simpa [weth10, weth10Aux, transferFromCoreSlot] using hget.symm
  subst body
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferFromSelectLine +++
      (transferFromZero <?> transferFromNonzero)) frame.post at coreCursor
  rcases coreCursor.peelChildlessLine
      (by simp [transferFromSelectLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine, htargetActions⟩
  have htargetPrefix :
      [Sevm.argWord frame.sevm 1 =? 0] <<+
        targetBranchCursor.pre.stack := by
    unfold transferFromSelectLine at htargetLine
    rcases of_run_append (arg 1) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    exact prefix_of_iszero hzero (prefix_of_arg nil_pref harg)
  have htargetCheck : (Sevm.argWord frame.sevm 1 =? 0) = 0 := by
    simp [B256.eqCheck, hto]
  rw [htargetCheck] at htargetPrefix
  rcases targetBranchCursor.selectBranchZero htargetPrefix with
    ⟨nonzeroCursor, _hnonzeroStack, hnonzeroActions⟩
  change Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferFromBalanceCheckLine +++
      ((.call transferBalanceErrorSlot) <?>
        (transferFromNonzeroSuccessLine +++ Func.ret)))
    frame.post at nonzeroCursor
  rcases nonzeroCursor.peelChildlessLine
      (by simp [transferFromBalanceCheckLine, loadArgBalanceAmount,
        balanceTooSmall, addressArg, arg, cdl, normalizeAddress,
        pushAddressMask, NinstIsChildless, Ninst.pushB256]) with
    ⟨balanceBranchCursor, _hbalanceLine, hbalanceActions⟩
  rcases balanceBranchCursor.selectBranchWithActions with
      hsuccess | herror
  · rcases hsuccess with ⟨successCursor, hsuccessActions⟩
    have hdesc := successCursor.finishTerminalChildlessLine (by
      simp [transferFromNonzeroSuccessLine, debitLoadedBalance,
        addressArg, arg, cdl, normalizeAddress, pushAddressMask,
        emitTransfer, Blanc.transferFromLog, mstoreAt, logWith, pushList,
        NinstIsChildless, Ninst.pushB256])
    exact hdesc.trans (hsuccessActions.trans
      (hbalanceActions.trans (hnonzeroActions.trans
        (htargetActions.trans (hcoreActions.trans
          (htransferActions.trans hwrapperActions))))))
  · rcases herror with ⟨errorCursor, _herrorActions⟩
    rcases errorCursor.enterCall context.invocation.2.2.2 with
      ⟨errorBody, herrorGet, errorBodyCursor, _herrorBodyActions⟩
    have herrorBody : errorBody = transferBalanceError := by
      simpa [weth10Aux, transferBalanceErrorSlot] using herrorGet.symm
    subst errorBody
    exact (Func.not_run_revWith
      (Func.Run.of_runCompiled errorBodyCursor.run)).elim

/-- The debit stored in a classified action is either absent, mechanically
direct, or is the exact allowance branch accepted by the executed WETH10
program. -/
inductive FlowAction.AcceptedDebit (dp : DeployParams)
    (action : FlowAction) (e : Sevm) (pre post : Devm) : Prop
  | none (hdebit : action.debit = none)
  | direct (rawSource : B256) (source : Adr)
      (hdebit : action.debit = some
        { actualCaller := e.caller
          rawSource
          source
          branch := .direct })
  | delegated (rawSource : B256) (source : Adr) (corePre : Devm)
      (branch : AllowanceBranch)
      (hdebit : action.debit = some
        { actualCaller := e.caller
          rawSource
          source
          branch := .delegated branch })
      (accepted : CallerAllowanceAccepted e pre corePre 2 branch)
  | flash (rawReceiver : B256) (receiver : Adr)
      (settle burn : Devm) (branch : AllowanceBranch)
      (hdebit : action.debit = some
        { actualCaller := e.caller
          rawSource := rawReceiver
          source := receiver
          branch := .flash branch })
      (accepted : FlashAllowanceAccepted e settle burn branch)
      (burnRun : Func.Run ((weth10 dp).main :: weth10Aux) e burn
        flashBurn post)

/-- Accepted debit provenance plus the exact installed-code and executable
classification witnesses that produced the stored action. -/
structure Exec.Frame.HasAcceptedDebit (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) (action : FlowAction) : Prop where
  authentic : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame
  classified : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action
  accepted : action.AcceptedDebit dp frame.sevm frame.pre frame.post

/-- Exact WETH-emitter evidence for a successful compiled frame.  The direct
mint cases expose their final log equality.  Transfer and burn cases retain
their functional branch predicates, whose `ordinaryTransferLog` equality is
at the pre-callback/pre-CALL local boundary.  The ERC677 and flash cases keep
their raw boundaries; in particular the flash case retains both the
`flashMintTransferLog` prefix and the `flashBurnTransferLog` suffix. -/
inductive GenuineWethEmitterEffect (dp : DeployParams) (e : Sevm)
    (pre post : Devm) : Prop
  | receive
      (empty : e.data.length.toB256 = 0)
      (logs : post.logs = pre.logs ++ [mintCallerTransferLog e])
  | deposit
      (selected : Sevm.selector e = depositSelector)
      (logs : post.logs = pre.logs ++ [mintCallerTransferLog e])
  | depositTo
      (selected : Sevm.selector e = depositToSelector)
      (logs : post.logs = pre.logs ++ [mintToTransferLog e])
  | depositToAndCall
      (selected : Sevm.selector e = depositToAndCallSelector)
      (effect : DepositToAndCallRawSuccessEffect dp e pre post)
  | transfer
      (selected : Sevm.selector e = transferSelector)
      (effect : TransferSuccessEffect e pre post)
  | transferAndCall
      (selected : Sevm.selector e = transferAndCallSelector)
      (effect : TransferAndCallRawSuccessEffect dp e pre post)
  | transferFrom
      (selected : Sevm.selector e = transferFromSelector)
      (effect : TransferFromSuccessEffect e pre post)
  | withdraw
      (selected : Sevm.selector e = withdrawSelector)
      (effect : BurnStopEffect e pre post e.caller
        (Sevm.argWord e 0) e.caller.toB256)
  | withdrawTo
      (selected : Sevm.selector e = withdrawToSelector)
      (effect : BurnStopEffect e pre post e.caller
        (Sevm.argWord e 1) (Sevm.argWord e 0))
  | withdrawFrom
      (selected : Sevm.selector e = withdrawFromSelector)
      (effect : WithdrawFromSuccessEffect e pre post)
  | flashLoan
      (selected : Sevm.selector e = flashLoanSelector)
      (effect : RawFlashLoanSuccessEffect dp e pre post
        (Sevm.argWord e 0) (Sevm.argWord e 1) (Sevm.argWord e 2))

/-- Exact emitter evidence paired with the authentic executable
classification that selected the same frame action. -/
structure Exec.Frame.HasGenuineWethEmitterEffect (dp : DeployParams)
    (ca : Adr) (frame : Exec.Frame) (action : FlowAction) : Prop where
  authentic : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame
  classified : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action
  effect : GenuineWethEmitterEffect dp frame.sevm frame.pre frame.post

/-- Exact absence of an own WETH balance write for the non-flow public
leaves.  Read endpoints and `approve` are silent through their public result.
`approveAndCall` records only the pre-callback approval prefix: its child may
reenter WETH and therefore the enclosing frame endpoint is intentionally not
claimed silent. -/
inductive NoWethBalanceOwnEffect (dp : DeployParams) (e : Sevm)
    (pre post : Devm) : Prop
  | name
      (selected : Sevm.selector e = selector "name" [])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | approve
      (selected : Sevm.selector e =
        selector "approve" [.address, .uint256])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | totalSupply
      (selected : Sevm.selector e = selector "totalSupply" [])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | permitTypehash
      (selected : Sevm.selector e = selector "PERMIT_TYPEHASH" [])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | decimals
      (selected : Sevm.selector e = selector "decimals" [])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | domainSeparator
      (selected : Sevm.selector e = selector "DOMAIN_SEPARATOR" [])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | maxFlashLoan
      (selected : Sevm.selector e = selector "maxFlashLoan" [.address])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | balanceOf
      (selected : Sevm.selector e = selector "balanceOf" [.address])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | nonces
      (selected : Sevm.selector e = selector "nonces" [.address])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | callbackSuccess
      (selected : Sevm.selector e = selector "CALLBACK_SUCCESS" [])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | flashMinted
      (selected : Sevm.selector e = selector "flashMinted" [])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | symbol
      (selected : Sevm.selector e = selector "symbol" [])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | approveAndCall
      (selected : Sevm.selector e = approveAndCallSelector)
      (callbackPre : Devm)
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor callbackPre e.currentTarget))
      (continuation : Func.Run ((weth10 dp).main :: weth10Aux) e
        callbackPre
        (callBoolCallback onTokenApprovalSelector 0 2 (arg 1)) post)
  | deploymentChainId
      (selected : Sevm.selector e = selector "deploymentChainId" [])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | permit
      (selected : Sevm.selector e = permitSelector)
      (ownSilent : PermitBalanceOwnSilent e pre post)
  | flashFee
      (selected : Sevm.selector e =
        selector "flashFee" [.address, .uint256])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))
  | allowance
      (selected : Sevm.selector e =
        selector "allowance" [.address, .address])
      (silent : Stor.Weth10Silent
        (Devm.getStor pre e.currentTarget)
        (Devm.getStor post e.currentTarget))

/-- Authentic unclassified-frame wrapper for a genuine silent own segment. -/
structure Exec.Frame.HasNoWethBalanceOwnEffect (dp : DeployParams)
    (ca : Adr) (frame : Exec.Frame) : Prop where
  authentic : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame
  unclassified : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = none
  effect : NoWethBalanceOwnEffect dp frame.sevm frame.pre frame.post

/-- Exhaustive own-storage classification of a successful authentic compiled
WETH10 frame.  The flow arm carries the exact action and rich operational
effect; the non-flow arm carries the selector-specific proof that the frame's
own code did not write a WETH balance slot. -/
inductive Exec.Frame.HasCompiledBalanceOwnEffect (dp : DeployParams)
    (ca : Adr) (frame : Exec.Frame) : Prop
  | flow (action : FlowAction)
      (effect : Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action)
  | noFlow (effect : Blanc.Weth10.Exec.Frame.HasNoWethBalanceOwnEffect dp ca frame)

private theorem publicReadResult_weth10Silent
    {P : Devm → Prop} {e : Sevm} {pre post : Devm}
    (h : PublicReadResult P e pre post) :
    Stor.Weth10Silent
      (Devm.getStor pre e.currentTarget)
      (Devm.getStor post e.currentTarget) :=
  Stor.Weth10Silent.of_eq (congrFun h.2.2.1 e.currentTarget).symm

/-- A successful binary-dispatch run cannot disappear into an unlisted leaf.
The only alternative at a leaf is the supplied fallback, which is required to
have no successful run.  Unlike forward reachability, this direction needs no
sortedness: it reports membership in the concrete tree that actually ran. -/
private theorem recognized_of_run_dispatchWith
    {c : List Func} {k : Nat} {fallback : Func}
    {e : Sevm} {s r : Devm} {tree : DispatchTree}
    {sig : B256} {ws : Stack}
    (hk : c[k]? = some fallback)
    (hfallback : ∀ {s' r'}, ¬ Func.Run c e s' fallback r')
    (hpfx : sig :: ws <<+ s.stack)
    (run : Func.Run c e s (dispatchWith k tree) r) :
    ∃ body, (sig, body) ∈ tree := by
  induction tree generalizing s ws with
  | fork left right ihLeft ihRight =>
      refine run_prepend_elim _
        [Ninst.dup 0, Ninst.pushB256 (leftmostFsig right), Ninst.gt] ?_ run
      intro s₁ h₁ hbranch
      have hpfx' :
          (leftmostFsig right >? sig) :: sig :: ws <<+ s₁.stack := by
        generalize_line_prefix
      rcases of_run_branch hbranch with
          ⟨s₂, hpop, hright⟩ |
          ⟨w, s₂, s₃, hnz, hpop, hburn, hleft⟩
      · rcases ihRight (popBurn_pref hpop hpfx').2 hright with
          ⟨body, hmem⟩
        exact ⟨body, Or.inr hmem⟩
      · have hpfx'' : sig :: ws <<+ s₃.stack := by
          rw [← hburn.stack]
          exact (popBurn_pref hpop hpfx').2
        rcases ihLeft hpfx'' hleft with ⟨body, hmem⟩
        exact ⟨body, Or.inl hmem⟩
  | leaf w body =>
      refine run_prepend_elim _ [Ninst.pushB256 w, Ninst.eq] ?_ run
      intro s₁ h₁ hbranch
      have hpfx' : (w =? sig) :: ws <<+ s₁.stack := by
        generalize_line_prefix
      rcases of_run_branch hbranch with
          ⟨s₂, hpop, hcall⟩ |
          ⟨v, s₂, s₃, hnz, hpop, hburn, hbody⟩
      · cases hcall with
        | call heq hburn hrun =>
            have hsame := hk.symm.trans heq
            injection hsame with hfb
            subst hfb
            exact (hfallback hrun).elim
      · have hflag : v = (w =? sig) := (popBurn_pref hpop hpfx').1
        have heq : w = sig := by
          by_contra hne
          have hz : (w =? sig) = 0 := by simp [B256.eqCheck, hne]
          exact hnz (hflag.trans hz)
        subst w
        exact ⟨body, rfl⟩

/-- Reverse compiled dispatch: every successful authentic WETH10 frame with
nonempty calldata entered one of the 27 listed public selector bodies.  This is
proved from the retained `Exec`, not assumed from the selector word. -/
theorem Exec.Frame.recognizedSelector_of_nonempty
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ body, (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hrun : Prog.Run e pre (weth10 dp) post :=
        correct e pre (weth10 dp) post run context.invocation.2.2.2
      dsimp only [Prog.Run] at hrun
      cases hrun
      rename (_ = _) => hentry
      rename (Func.Run _ _ _ _ _) => hmain
      rename (Devm.Burn _ _) => hburn
      rename Devm => entry
      cases hentry
      have hmain' : Func.Run ((weth10 dp).main :: weth10Aux) e entry
          (Ninst.calldatasize ::: Ninst.iszero :::
            (receiveEther <?>
              (fsig +++ dispatchWith fallbackSlot (weth10Tree dp)))) post := by
        simpa only [weth10, weth10Main] using hmain
      refine run_prepend_elim _ [Ninst.calldatasize, Ninst.iszero] ?_ hmain'
      intro flagPost hflag hbranch
      rcases Line.of_run_cons hflag with ⟨sizePost, hsize, hzeroRun⟩
      rcases Line.of_run_cons hzeroRun with ⟨zeroPost, hzero, hnil⟩
      cases hnil
      have hsizePfx : [e.data.length.toB256] <<+ sizePost.stack :=
        prefix_of_push (of_run_calldatasize hsize) nil_pref
      have hflagPfx : [e.data.length.toB256 =? 0] <<+ flagPost.stack :=
        prefix_of_iszero hzero hsizePfx
      rcases of_run_branch hbranch with
          ⟨dispatchPre, hpop, hdispatch⟩ |
          ⟨w, popPost, receivePre, hnz, hpop, hreceiveBurn, hreceive⟩
      · refine run_prepend_elim _ fsig ?_ hdispatch
        intro dispatchPost hfsig htreeRun
        have hselectorPfx : Sevm.selector e :: [] <<+ dispatchPost.stack :=
          prefix_of_fsig nil_pref hfsig
        rcases recognized_of_run_dispatchWith
            (c := (weth10 dp).main :: weth10Aux)
            (k := fallbackSlot) (fallback := Func.rev)
            (tree := weth10Tree dp)
            (by simp [fallbackSlot, weth10, weth10Aux])
            (fun {_ _} => not_run_rev)
            hselectorPfx htreeRun with ⟨body, hmem⟩
        exact ⟨body, DispatchTree.mem_of_mem_ofSorted
          (by simp [weth10Funcs]) hmem⟩
      · have hpop' := hpop.stack
        simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpop'
        rw [hpop'] at hflagPfx
        have hw : (e.data.length.toB256 =? 0) = w :=
          pref_head_unique hflagPfx (pref_append [w] popPost.stack)
        have hflagNonzero : (e.data.length.toB256 =? 0) ≠ 0 := by
          rw [hw]
          exact hnz
        have hflagZero : (e.data.length.toB256 =? 0) = 0 := by
          simp [B256.eqCheck, hnonempty]
        exact (hflagNonzero hflagZero).elim

private theorem action_eq_of_flowAction_eq
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {atom : FlowAtom} {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hatom : primaryFlowAtom frame.sevm = some atom)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    action =
      { atom
        credit := atom.creditOccurrence frame.pre ca
        debit := primaryDebitProvenance frame.sevm frame.pre frame.post
        actualCaller := frame.sevm.caller
        currentTarget := frame.sevm.currentTarget
        codeAddress := frame.sevm.codeAddress
        depth := frame.sevm.depth } := by
  simp only [Blanc.Weth10.Exec.Frame.flowAction?, if_pos context.invocation, hatom,
    Option.map_some, Option.some.injEq] at haction
  exact haction.symm

private theorem debit_eq_of_flowAction_eq
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    action.debit =
      primaryDebitProvenance frame.sevm frame.pre frame.post := by
  unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
  rw [if_pos context.invocation] at haction
  cases hatom : primaryFlowAtom frame.sevm with
  | none => simp [hatom] at haction
  | some atom =>
      simp only [hatom, Option.map_some, Option.some.injEq] at haction
      subst action
      rfl

private theorem normalizedAddressArg_eq_toAdr_toB256
    (e : Sevm) (k : B256) :
    normalizedAddressArg e k = (Sevm.argWord e k).toAdr.toB256 := by
  have lowMask (x : UInt64) :
      (0x00000000ffffffff : UInt64) &&& x =
        x.toUInt32.toUInt64 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_and, UInt64.toNat_toUInt32,
      UInt32.toNat_toUInt64]
    rw [Nat.and_comm]
    change x.toNat &&& 2 ^ 32 - 1 = x.toNat % 2 ^ 32
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have andMax (x : UInt64) : UInt64.max &&& x = x := by
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_and]
    have hmax : UInt64.max.toBitVec = BitVec.allOnes 64 := by rfl
    rw [hmax]
    exact BitVec.allOnes_and
  have b128AndMax (x : B128) : B128.max &&& x = x := by
    apply Prod.ext <;> apply andMax
  have hmask : (~~~ addressMask) =
      (⟨⟨0, 0x00000000ffffffff⟩, B128.max⟩ : B256) := by
    decide +kernel
  unfold normalizedAddressArg
  rw [hmask]
  rcases Sevm.argWord e k with ⟨⟨high, middle⟩, low⟩
  simp only [B256.toAdr, Adr.toB256, B256.and_eq_and_prod_and,
    B128.and_eq_and_prod_and, UInt64.zero_and]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact lowMask middle
  · exact b128AndMax low

private theorem rest_set_callerAllowanceRuntimeKey
    (e : Sevm) (s : Stor) (v : B256) :
    Stor.rest (s.set (callerAllowanceRuntimeKey e) v) = Stor.rest s := by
  funext a
  unfold Stor.rest Function.comp
  rw [Stor.get_set_ne]
  intro heq
  apply runtimeAllowanceKey_not_valid
    (Bytes.keccak
      ((Sevm.argWord e 0).toBytes ++ e.caller.toB256.toBytes))
  exact ⟨a, heq.symm⟩

private theorem callerAllowanceOutcome_rest_eq
    {e : Sevm} {pre corePre : Devm} {amountArg : B256}
    (h : CallerAllowanceOutcome e pre corePre amountArg) :
    Stor.rest (Devm.getStor corePre e.currentTarget) =
      Stor.rest (Devm.getStor pre e.currentTarget) := by
  rcases h.1 with hself | ⟨hnotself, hspend⟩
  · exact congrArg Stor.rest hself.2.1
  · rcases hspend with hmax | hfinite
    · exact congrArg Stor.rest hmax.2.1
    · rcases hfinite with
        ⟨allowance, hnotmax, hle, hget, hstor, hlogs⟩
      rw [hstor, rest_set_callerAllowanceRuntimeKey]

private theorem callerAllowanceOutcome_weth10Silent
    {e : Sevm} {pre corePre : Devm} {amountArg : B256}
    (h : CallerAllowanceOutcome e pre corePre amountArg) :
    Stor.Weth10Silent (Devm.getStor pre e.currentTarget)
      (Devm.getStor corePre e.currentTarget) := by
  refine ⟨(callerAllowanceOutcome_rest_eq h).symm, ?_⟩
  rcases h.1 with hself | ⟨hnotself, hspend⟩
  · rw [hself.2.1]
  · rcases hspend with hmax | hfinite
    · rw [hmax.2.1]
    · rcases hfinite with
        ⟨allowance, hnotmax, hle, hget, hstor, hlogs⟩
      rw [hstor, Stor.get_set_ne]
      exact runtimeAllowanceKey_ne_flash
        (Bytes.keccak
          ((Sevm.argWord e 0).toBytes ++ e.caller.toB256.toBytes))

private theorem flashAllowanceOutcome_weth10Silent
    {e : Sevm} {settle burn : Devm}
    (h : FlashAllowanceOutcome e settle burn) :
    Stor.Weth10Silent (Devm.getStor settle e.currentTarget)
      (Devm.getStor burn e.currentTarget) := by
  rcases h.1 with hmax | hfinite
  · exact Stor.Weth10Silent.of_eq hmax.2.1.symm
  · rcases hfinite with
      ⟨allowance, hnotmax, hle, hget, hstor, hlogs⟩
    rw [hstor]
    exact Stor.Weth10Silent.set
      (runtimeAllowanceKey_not_valid _)
      (runtimeAllowanceKey_ne_flash _)

private theorem callerAllowanceBranch_accepted
    {e : Sevm} {pre corePre : Devm} {amountArg : B256}
    (h : CallerAllowanceOutcome e pre corePre amountArg) :
    CallerAllowanceAccepted e pre corePre amountArg
      (callerAllowanceBranch e pre amountArg) := by
  unfold callerAllowanceBranch
  rcases h.1 with hself | ⟨hnotself, hspend⟩
  · simp [hself.1, CallerAllowanceAccepted, CallerAllowanceTag, h]
  · simp only [hnotself, ↓reduceIte]
    rcases hspend with hmax | hfinite
    · simp [hmax.1, CallerAllowanceAccepted, CallerAllowanceTag, h,
        hnotself]
    · rcases hfinite with
        ⟨allowance, hnotmax, hle, hget, hstor, hlogs⟩
      simp [hget, hnotmax, CallerAllowanceAccepted, CallerAllowanceTag,
        h, hnotself, hle]

/-- Post-state reconstruction of the flash repayment visit.  The burn
continuation never touches the tagged repayment cell, so the word the
committed post state holds there is exactly the word settlement wrote, and it
alone decides the fork: `B256.max` is the infinite-allowance arm, which wrote
nothing, and any other word `after` is the finite arm reducing an entry
allowance of exactly `after + amount`. -/
theorem flashSettlement_reconstruction
    {dp : DeployParams} {e : Sevm} {settlePre burnPre post : Devm}
    (houtcome : FlashAllowanceOutcome e settlePre burnPre)
    (hburn : Func.Run ((weth10 dp).main :: weth10Aux) e burnPre
      flashBurn post) :
    FlashAllowanceAccepted e settlePre burnPre
      (flashAllowanceBranchFromPost e post) := by
  have hkey := flashBurn_storage_at_allowanceKey dp hburn
  unfold flashAllowanceBranchFromPost
  rcases houtcome.1 with hmax | hfinite
  · have hpostmax : (Devm.getStor post e.currentTarget).get
        (flashAllowanceRuntimeKey e) = B256.max := by
      rw [hkey, hmax.2.1, hmax.1]
    rw [if_pos hpostmax]
    exact ⟨houtcome, rfl, hmax.1⟩
  · rcases hfinite with
      ⟨allowance, hnotmax, hle, hread, hwrite, _hlogs⟩
    have hpostafter : (Devm.getStor post e.currentTarget).get
        (flashAllowanceRuntimeKey e) =
          allowance - Sevm.argWord e 2 := by
      rw [hkey, hwrite, Stor.get_set_self]
    have hsuble : allowance - Sevm.argWord e 2 ≤ allowance := by
      apply B256.le_of_toNat_le_toNat
      rw [B256.toNat_sub_eq_of_le _ _ hle]
      omega
    have hallowlemax : allowance ≤ B256.max := B256.le_max allowance
    have hafternotmax :
        allowance - Sevm.argWord e 2 ≠ B256.max := by
      intro heq
      have hmaxle : B256.max ≤ allowance := by
        simpa only [heq] using hsuble
      exact hnotmax (le_antisymm hallowlemax hmaxle)
    have hpostnotmax : (Devm.getStor post e.currentTarget).get
        (flashAllowanceRuntimeKey e) ≠ B256.max := by
      rw [hpostafter]
      exact hafternotmax
    rw [if_neg hpostnotmax]
    have hbefore : (Devm.getStor post e.currentTarget).get
          (flashAllowanceRuntimeKey e) + Sevm.argWord e 2 = allowance := by
      rw [hpostafter]
      exact B256.sub_add_cancel
    refine ⟨houtcome, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hbefore]
      exact hread
    · rw [hbefore]
      exact hnotmax
    · rw [hbefore]
      exact hle
    · rw [hbefore, hpostafter]

private theorem localSegment_ordinaryMint
    {action : FlowAction} {pre post : HolderBalances}
    {rawRecipient : B256} {recipient : Adr} {amountWord : B256}
    (hatom : action.atom =
      .ordinaryMint rawRecipient recipient amountWord.toNat)
    (hcredit : action.ExactCredit recipient (pre recipient) amountWord)
    (hdebit : action.debit = none)
    (hincrease : Increase recipient amountWord pre post) :
    LocalActionSegment .ordinaryMint action pre post :=
  .ordinaryMint rawRecipient recipient amountWord hatom hcredit hdebit
    hincrease

private theorem localSegment_ordinaryTransfer
    {action : FlowAction} {pre post : HolderBalances}
    {rawSource rawRecipient : B256} {source recipient : Adr}
    {amountWord : B256}
    (hatom : action.atom = .transfer rawSource rawRecipient source recipient
      amountWord.toNat)
    (hcredit : action.ExactCredit recipient
      (if source = recipient then pre source - amountWord
        else pre recipient) amountWord)
    (hdebit : action.HasDebitSource rawSource source)
    (htransfer : Transfer pre source amountWord recipient post) :
    LocalActionSegment .ordinaryTransfer action pre post := by
  rcases htransfer with ⟨hle, intermediate, hdecrease, hincrease⟩
  have hbefore : intermediate recipient =
      (if source = recipient then pre source - amountWord
        else pre recipient) := by
    by_cases hself : source = recipient
    · subst recipient
      simpa using ((hdecrease source).1 rfl).symm
    · simpa [hself] using ((hdecrease recipient).2 hself).symm
  apply LocalActionSegment.ordinaryTransfer rawSource rawRecipient source
    recipient amountWord hatom
    { amount_le := hle
      intermediate := intermediate
      decrease := hdecrease
      increase := hincrease }
  · simpa only [FlowAction.ExactCredit, hbefore] using hcredit
  · exact hdebit

private theorem localSegment_redemption
    {action : FlowAction} {pre post : HolderBalances}
    {rawSource : B256} {source ethRecipient : Adr} {amountWord : B256}
    (hatom : action.atom =
      .redemption rawSource source ethRecipient amountWord.toNat)
    (hcredit : action.credit = none)
    (hdebit : action.HasDebitSource rawSource source)
    (hle : amountWord ≤ pre source)
    (hdecrease : Decrease source amountWord pre post) :
    LocalActionSegment .redemption action pre post :=
  .redemption rawSource source ethRecipient amountWord hatom hcredit hdebit
    hle hdecrease

private theorem localSegments_flashPair
    {action : FlowAction} {pre minted settle post : HolderBalances}
    {rawReceiver : B256} {receiver : Adr} {amountWord : B256}
    (hatom : action.atom =
      .flashPair rawReceiver receiver amountWord.toNat)
    (hcredit : action.ExactCredit receiver (pre receiver) amountWord)
    (hdebit : action.HasFlashDebitSource rawReceiver receiver)
    (hincrease : Increase receiver amountWord pre minted)
    (hle : amountWord ≤ settle receiver)
    (hdecrease : Decrease receiver amountWord settle post) :
    LocalActionSegment .flashCredit action pre minted ∧
      LocalActionSegment .flashRepayment action settle post :=
  ⟨.flashCredit rawReceiver receiver amountWord hatom hcredit hdebit
      hincrease,
    .flashRepayment rawReceiver receiver amountWord (pre receiver)
      hatom hcredit hdebit hle hdecrease⟩

private theorem localOwnEffect_ordinaryMint
    {action : FlowAction} {pre post : HolderBalances}
    {rawRecipient : B256} {recipient : Adr} {amountWord : B256}
    (hatom : action.atom =
      .ordinaryMint rawRecipient recipient amountWord.toNat)
    (hcredit : action.ExactCredit recipient (pre recipient) amountWord)
    (hdebit : action.debit = none)
    (hincrease : Increase recipient amountWord pre post) :
    LocalOwnEffect action pre post :=
  .ordinaryMint (.ordinaryMint rawRecipient recipient amountWord
    hatom hcredit hdebit hincrease)

private theorem localOwnEffect_ordinaryTransfer
    {action : FlowAction} {pre post : HolderBalances}
    {rawSource rawRecipient : B256} {source recipient : Adr}
    {amountWord : B256}
    (hatom : action.atom = .transfer rawSource rawRecipient source recipient
      amountWord.toNat)
    (hcredit : action.ExactCredit recipient
      (if source = recipient then pre source - amountWord
        else pre recipient) amountWord)
    (hdebit : action.HasDebitSource rawSource source)
    (htransfer : Transfer pre source amountWord recipient post) :
    LocalOwnEffect action pre post := by
  rcases htransfer with ⟨hle, intermediate, hdecrease, hincrease⟩
  have hbefore : intermediate recipient =
      (if source = recipient then pre source - amountWord
        else pre recipient) := by
    by_cases hself : source = recipient
    · subst recipient
      simpa using ((hdecrease source).1 rfl).symm
    · simpa [hself] using ((hdecrease recipient).2 hself).symm
  apply LocalOwnEffect.ordinaryTransfer
  apply LocalActionSegment.ordinaryTransfer rawSource rawRecipient source
    recipient amountWord hatom
    { amount_le := hle
      intermediate := intermediate
      decrease := hdecrease
      increase := hincrease }
  · simpa only [FlowAction.ExactCredit, hbefore] using hcredit
  · exact hdebit

private theorem localOwnEffect_redemption
    {action : FlowAction} {pre post : HolderBalances}
    {rawSource : B256} {source ethRecipient : Adr} {amountWord : B256}
    (hatom : action.atom =
      .redemption rawSource source ethRecipient amountWord.toNat)
    (hcredit : action.credit = none)
    (hdebit : action.HasDebitSource rawSource source)
    (hle : amountWord ≤ pre source)
    (hdecrease : Decrease source amountWord pre post) :
    LocalOwnEffect action pre post :=
  .redemption (.redemption rawSource source ethRecipient amountWord
    hatom hcredit hdebit hle hdecrease)

private theorem localOwnEffect_flashPair
    {action : FlowAction} {pre minted settle post : HolderBalances}
    {rawReceiver : B256} {receiver : Adr} {amountWord : B256}
    (hatom : action.atom =
      .flashPair rawReceiver receiver amountWord.toNat)
    (hcredit : action.ExactCredit receiver (pre receiver) amountWord)
    (hdebit : action.HasFlashDebitSource rawReceiver receiver)
    (hincrease : Increase receiver amountWord pre minted)
    (hle : amountWord ≤ settle receiver)
    (hdecrease : Decrease receiver amountWord settle post) :
    LocalOwnEffect action pre post :=
  .flashPair
    (.flashCredit rawReceiver receiver amountWord hatom hcredit hdebit
      hincrease)
    (.flashRepayment rawReceiver receiver amountWord (pre receiver)
      hatom hcredit hdebit hle hdecrease)

theorem Exec.Frame.hasLocalOwnEffect_of_receive
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hempty : frame.sevm.data.length.toB256 = 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasLocalOwnEffect ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := receive_exec_effect dp context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2 hempty
      have hinc := heffect.1
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rw [htarget] at hinc
      have haction' := haction
      simp [Blanc.Weth10.Exec.Frame.flowAction?, context.invocation, primaryFlowAtom,
        primaryDebitProvenance, hempty] at haction'
      symm at haction'
      subst action
      unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
      refine ⟨Stor.rest (Devm.getStor post ca), ?_⟩
      apply localOwnEffect_ordinaryMint
      · rfl
      · unfold FlowAction.ExactCredit
        simp only [FlowAtom.creditOccurrence]
        rw [toB256_toNat]
      · rfl
      · exact hinc

theorem Exec.Frame.hasLocalOwnEffect_of_deposit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = depositSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasLocalOwnEffect ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := deposit_exec_effect dp context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        (by simpa only [depositSelector] using hselector) hnonempty
      have hinc := heffect.1
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rw [htarget] at hinc
      have haction' := haction
      simp [Blanc.Weth10.Exec.Frame.flowAction?, context.invocation, primaryFlowAtom,
        primaryDebitProvenance, hnonempty, hselector,
        depositSelector_ne_transferSelector,
        depositSelector_ne_transferAndCallSelector,
        depositSelector_ne_withdrawSelector,
        depositSelector_ne_withdrawToSelector,
        depositSelector_ne_transferFromSelector,
        depositSelector_ne_withdrawFromSelector,
        depositSelector_ne_flashLoanSelector] at haction'
      symm at haction'
      subst action
      unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
      refine ⟨Stor.rest (Devm.getStor post ca), ?_⟩
      apply localOwnEffect_ordinaryMint
      · rfl
      · unfold FlowAction.ExactCredit
        simp only [FlowAtom.creditOccurrence]
        rw [toB256_toNat]
      · rfl
      · exact hinc

theorem Exec.Frame.hasLocalOwnEffect_of_transfer
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasLocalOwnEffect ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := (weth10_transfer_successEffect dp
        context.memory_wf context.memory_reads_empty run
        context.invocation.2.2.2
        (by simpa only [transferSelector] using hselector) hnonempty).2
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rcases heffect with hzero | hnonzero
      · rcases hzero with ⟨hraw, callPre, guardPost, hprefix, _⟩
        unfold BurnCallPrefix at hprefix
        rw [htarget] at hprefix
        have hatom : primaryFlowAtom e = some
            (.redemption e.caller.toB256 e.caller e.caller
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector,
            transferSelector_ne_depositSelector,
            transferSelector_ne_depositToSelector,
            transferSelector_ne_depositToAndCallSelector, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
        refine ⟨Stor.rest (Devm.getStor callPre ca), ?_⟩
        apply localOwnEffect_redemption
        · rfl
        · rfl
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector]
        · exact hprefix.2.1
        · exact hprefix.1
      · rcases hnonzero with
          ⟨hraw, recipient, hrecipient, htransfer, _⟩
        rw [htarget] at htransfer
        have hrecipient' : recipient = (Sevm.argWord e 0).toAdr := by
          apply Adr.toB256_inj
          rw [hrecipient]
          exact normalizedAddressArg_eq_toAdr_toB256 e 0
        subst recipient
        have hatom : primaryFlowAtom e = some
            (.transfer e.caller.toB256 (Sevm.argWord e 0) e.caller
              (Sevm.argWord e 0).toAdr
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector,
            transferSelector_ne_depositSelector,
            transferSelector_ne_depositToSelector,
            transferSelector_ne_depositToAndCallSelector, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
        refine ⟨Stor.rest (Devm.getStor post ca), ?_⟩
        apply localOwnEffect_ordinaryTransfer
        · rfl
        · unfold FlowAction.ExactCredit
          simp only [FlowAtom.creditOccurrence]
          rw [toB256_toNat]
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector]
        · exact htransfer

theorem Exec.Frame.hasLocalOwnEffect_of_depositTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = depositToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasLocalOwnEffect ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := depositTo_exec_effect dp context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        (by simpa only [depositToSelector] using hselector) hnonempty
      have hstor := heffect.1
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rw [htarget, normalizedAddressArg_eq_toAdr_toB256] at hstor
      have hincrease : Increase (Sevm.argWord e 0).toAdr e.value
          (Stor.rest (Devm.getStor pre ca))
          (Stor.rest (Devm.getStor post ca)) := by
        rw [hstor]
        exact Stor.increase_set _ _ _
      have hatom : primaryFlowAtom e = some
          (.ordinaryMint (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            e.value.toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          depositToSelector_ne_depositSelector]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
      refine ⟨Stor.rest (Devm.getStor post ca), ?_⟩
      apply localOwnEffect_ordinaryMint
      · rfl
      · unfold FlowAction.ExactCredit
        simp only [FlowAtom.creditOccurrence]
        rw [toB256_toNat]
      · simp [primaryDebitProvenance, hnonempty, hselector,
        depositToSelector_ne_transferSelector,
          depositToSelector_ne_transferAndCallSelector,
          depositToSelector_ne_transferFromSelector,
          depositToSelector_ne_withdrawSelector,
          depositToSelector_ne_withdrawToSelector,
          depositToSelector_ne_withdrawFromSelector,
          depositToSelector_ne_flashLoanSelector]
      · exact hincrease

theorem Exec.Frame.hasLocalOwnEffect_of_depositToAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector :
      Sevm.selector frame.sevm = depositToAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasLocalOwnEffect ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := weth10_depositToAndCall_rawSuccessEffect dp
        context.invocation.2.2.2 hselector hnonempty context.memory_wf
        context.memory_reads_empty run
      unfold DepositToAndCallRawSuccessEffect at heffect
      rcases heffect with
        ⟨callbackPre, inputSize, input, hstor, hlogs, hbal, hcode,
          houtput, hboundary⟩
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rw [htarget, normalizedAddressArg_eq_toAdr_toB256] at hstor
      have hincrease : Increase (Sevm.argWord e 0).toAdr e.value
          (Stor.rest (Devm.getStor pre ca))
          (Stor.rest (Devm.getStor callbackPre ca)) := by
        rw [hstor]
        exact Stor.increase_set _ _ _
      have hatom : primaryFlowAtom e = some
          (.ordinaryMint (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            e.value.toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          depositToAndCallSelector_ne_depositSelector]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
      refine ⟨Stor.rest (Devm.getStor callbackPre ca), ?_⟩
      apply localOwnEffect_ordinaryMint
      · rfl
      · unfold FlowAction.ExactCredit
        simp only [FlowAtom.creditOccurrence]
        rw [toB256_toNat]
      · simp [primaryDebitProvenance, hnonempty, hselector,
        depositToAndCallSelector_ne_transferSelector,
          depositToAndCallSelector_ne_transferAndCallSelector,
          depositToAndCallSelector_ne_transferFromSelector,
          depositToAndCallSelector_ne_withdrawSelector,
          depositToAndCallSelector_ne_withdrawToSelector,
          depositToAndCallSelector_ne_withdrawFromSelector,
          depositToAndCallSelector_ne_flashLoanSelector]
      · exact hincrease

theorem Exec.Frame.hasLocalOwnEffect_of_transferAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasLocalOwnEffect ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := (weth10_transferAndCall_rawSuccessEffect dp
        context.invocation.2.2.2 hselector hnonempty context.memory_wf
        context.memory_reads_empty run).2
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rcases heffect with hzero | hnonzero
      · rcases hzero with
          ⟨hraw, callPre, callbackPre, inputSize, input, hprefix,
            hboundary⟩
        unfold BurnCallPrefix at hprefix
        rw [htarget] at hprefix
        have hatom : primaryFlowAtom e = some
            (.redemption e.caller.toB256 e.caller e.caller
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector,
            transferAndCallSelector_ne_depositSelector,
            transferAndCallSelector_ne_depositToSelector,
            transferAndCallSelector_ne_depositToAndCallSelector, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
        refine ⟨Stor.rest (Devm.getStor callPre ca), ?_⟩
        apply localOwnEffect_redemption
        · rfl
        · rfl
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector]
        · exact hprefix.2.1
        · exact hprefix.1
      · rcases hnonzero with
          ⟨hraw, recipient, callbackPre, inputSize, input, hrecipient,
            htransfer, hflash, hlogs, hbal, hcode, houtput, hboundary⟩
        rw [htarget] at htransfer
        have hrecipient' : recipient = (Sevm.argWord e 0).toAdr := by
          apply Adr.toB256_inj
          rw [hrecipient]
          exact normalizedAddressArg_eq_toAdr_toB256 e 0
        subst recipient
        have hatom : primaryFlowAtom e = some
            (.transfer e.caller.toB256 (Sevm.argWord e 0) e.caller
              (Sevm.argWord e 0).toAdr
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector,
            transferAndCallSelector_ne_depositSelector,
            transferAndCallSelector_ne_depositToSelector,
            transferAndCallSelector_ne_depositToAndCallSelector, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
        refine ⟨Stor.rest (Devm.getStor callbackPre ca), ?_⟩
        apply localOwnEffect_ordinaryTransfer
        · rfl
        · unfold FlowAction.ExactCredit
          simp only [FlowAtom.creditOccurrence]
          rw [toB256_toNat]
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector]
        · exact htransfer

theorem Exec.Frame.hasLocalOwnEffect_of_transferFrom
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasLocalOwnEffect ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := (weth10_transferFrom_successEffect dp
        context.memory_wf context.memory_reads_empty run
        context.invocation.2.2.2
        (by simpa only [transferFromSelector] using hselector)
        hnonempty).2
      rcases heffect with ⟨corePre, hallowance, hcore⟩
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hrest := callerAllowanceOutcome_rest_eq hallowance
      rw [htarget] at hrest
      have hsource : (normalizedAddressArg e 0).toAdr =
          (Sevm.argWord e 0).toAdr := by
        rw [normalizedAddressArg_eq_toAdr_toB256, toAdr_toB256]
      rcases hcore with hzero | hnonzero
      · rcases hzero with ⟨hraw, hburn⟩
        unfold BurnReturnTrueEffect at hburn
        rcases hburn with
          ⟨callPre, guardPost, hprefix, hstorGuard, hbalGuard,
            hcodeGuard, hlogsGuard, htrue⟩
        unfold BurnCallPrefix at hprefix
        rw [htarget, hrest, hsource] at hprefix
        have hatom : primaryFlowAtom e = some
            (.redemption (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
              e.caller (Sevm.argWord e 2).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector,
            transferFromSelector_ne_depositSelector,
            transferFromSelector_ne_depositToSelector,
            transferFromSelector_ne_depositToAndCallSelector,
            transferFromSelector_ne_transferSelector,
            transferFromSelector_ne_transferAndCallSelector, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
        refine ⟨Stor.rest (Devm.getStor callPre ca), ?_⟩
        apply localOwnEffect_redemption
        · rfl
        · rfl
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector,
            transferFromSelector_ne_transferSelector,
            transferFromSelector_ne_transferAndCallSelector,
            transferFromSelector_ne_withdrawSelector,
            transferFromSelector_ne_withdrawToSelector]
        · exact hprefix.2.1
        · exact hprefix.1
      · rcases hnonzero with
          ⟨hraw, recipient, hrecipient, htransfer, hflash, hlogs,
            htrue, hbal, hcode⟩
        rw [htarget, hrest, hsource] at htransfer
        have hrecipient' : recipient = (Sevm.argWord e 1).toAdr := by
          apply Adr.toB256_inj
          rw [hrecipient]
          exact normalizedAddressArg_eq_toAdr_toB256 e 1
        subst recipient
        have hatom : primaryFlowAtom e = some
            (.transfer (Sevm.argWord e 0) (Sevm.argWord e 1)
              (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toAdr
              (Sevm.argWord e 2).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector,
            transferFromSelector_ne_depositSelector,
            transferFromSelector_ne_depositToSelector,
            transferFromSelector_ne_depositToAndCallSelector,
            transferFromSelector_ne_transferSelector,
            transferFromSelector_ne_transferAndCallSelector, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
        refine ⟨Stor.rest (Devm.getStor post ca), ?_⟩
        apply localOwnEffect_ordinaryTransfer
        · rfl
        · unfold FlowAction.ExactCredit
          simp only [FlowAtom.creditOccurrence]
          rw [toB256_toNat]
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector,
            transferFromSelector_ne_transferSelector,
            transferFromSelector_ne_transferAndCallSelector,
            transferFromSelector_ne_withdrawSelector,
            transferFromSelector_ne_withdrawToSelector]
        · exact htransfer

theorem Exec.Frame.hasLocalOwnEffect_of_withdraw
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasLocalOwnEffect ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := (weth10_withdraw_successEffect dp
        context.memory_wf context.memory_reads_empty run
        context.invocation.2.2.2
        (by simpa only [withdrawSelector] using hselector) hnonempty).2
      rcases heffect with ⟨callPre, hprefix⟩
      unfold BurnCallPrefix at hprefix
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rw [htarget] at hprefix
      have hatom : primaryFlowAtom e = some
          (.redemption e.caller.toB256 e.caller e.caller
            (Sevm.argWord e 0).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          withdrawSelector_ne_depositSelector,
          withdrawSelector_ne_depositToSelector,
          withdrawSelector_ne_depositToAndCallSelector,
          withdrawSelector_ne_transferSelector,
          withdrawSelector_ne_transferAndCallSelector,
          withdrawSelector_ne_transferFromSelector]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
      refine ⟨Stor.rest (Devm.getStor callPre ca), ?_⟩
      apply localOwnEffect_redemption
      · rfl
      · rfl
      · unfold FlowAction.HasDebitSource
        simp [primaryDebitProvenance, hnonempty, hselector]
      · exact hprefix.2.1
      · exact hprefix.1

theorem Exec.Frame.hasLocalOwnEffect_of_withdrawTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasLocalOwnEffect ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := (weth10_withdrawTo_successEffect dp
        context.memory_wf context.memory_reads_empty run
        context.invocation.2.2.2
        (by simpa only [withdrawToSelector] using hselector) hnonempty).2
      rcases heffect with ⟨callPre, hprefix⟩
      unfold BurnCallPrefix at hprefix
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rw [htarget] at hprefix
      have hatom : primaryFlowAtom e = some
          (.redemption e.caller.toB256 e.caller
            (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          withdrawToSelector_ne_depositSelector,
          withdrawToSelector_ne_depositToSelector,
          withdrawToSelector_ne_depositToAndCallSelector,
          withdrawToSelector_ne_transferSelector,
          withdrawToSelector_ne_transferAndCallSelector,
          withdrawToSelector_ne_transferFromSelector,
          withdrawToSelector_ne_withdrawSelector]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
      refine ⟨Stor.rest (Devm.getStor callPre ca), ?_⟩
      apply localOwnEffect_redemption
      · rfl
      · rfl
      · unfold FlowAction.HasDebitSource
        simp [primaryDebitProvenance, hnonempty, hselector]
      · exact hprefix.2.1
      · exact hprefix.1

theorem Exec.Frame.hasLocalOwnEffect_of_withdrawFrom
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasLocalOwnEffect ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := (weth10_withdrawFrom_successEffect dp
        context.memory_wf context.memory_reads_empty run
        context.invocation.2.2.2
        (by simpa only [withdrawFromSelector] using hselector)
        hnonempty).2
      rcases heffect with ⟨corePre, hallowance, callPre, hprefix⟩
      unfold BurnCallPrefix at hprefix
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hrest := callerAllowanceOutcome_rest_eq hallowance
      rw [htarget] at hrest
      have hsource : (normalizedAddressArg e 0).toAdr =
          (Sevm.argWord e 0).toAdr := by
        rw [normalizedAddressArg_eq_toAdr_toB256, toAdr_toB256]
      rw [htarget, hrest, hsource] at hprefix
      have hatom : primaryFlowAtom e = some
          (.redemption (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            (Sevm.argWord e 1).toAdr (Sevm.argWord e 2).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          withdrawFromSelector_ne_depositSelector,
          withdrawFromSelector_ne_depositToSelector,
          withdrawFromSelector_ne_depositToAndCallSelector,
          withdrawFromSelector_ne_transferSelector,
          withdrawFromSelector_ne_transferAndCallSelector,
          withdrawFromSelector_ne_transferFromSelector,
          withdrawFromSelector_ne_withdrawSelector,
          withdrawFromSelector_ne_withdrawToSelector]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
      refine ⟨Stor.rest (Devm.getStor callPre ca), ?_⟩
      apply localOwnEffect_redemption
      · rfl
      · rfl
      · unfold FlowAction.HasDebitSource
        simp [primaryDebitProvenance, hnonempty, hselector,
          withdrawFromSelector_ne_transferSelector,
          withdrawFromSelector_ne_transferAndCallSelector,
          withdrawFromSelector_ne_transferFromSelector,
          withdrawFromSelector_ne_withdrawSelector,
          withdrawFromSelector_ne_withdrawToSelector]
      · exact hprefix.2.1
      · exact hprefix.1

theorem Exec.Frame.hasLocalOwnEffect_of_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasLocalOwnEffect ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hstateCode : pre.getCode e.currentTarget = e.code := by
        rw [htarget]
        exact context.stateCode_eq
      have heffect := (weth10_flashLoan_rawSuccessEffect dp
        context.invocation.2.2.2 hstateCode hselector hnonempty
        context.memory_wf context.memory_reads_empty run).2
      unfold RawFlashLoanSuccessEffect at heffect
      rcases heffect with
        ⟨h0, h1, h2, htoken, recipient, sc, mid, settle, burn,
          callbackLogs, base, hrecipient, hbase, hamount, htotal,
          hincrease, hcounterSc, hcodeSc, hbalSc, hmemory, hmintLogs,
          houtputSc, hcontinuation, hcallback, hcallbackLogs, hstorMid,
          hbalMid, hcodeMid, hsettleLogs, hsettleOutput, hsettleRun,
          hburnRun, hallowance, hdecrease, hle, hcounterPost, hlogFork,
          htrue, hbalPost, hcodePost⟩
      rw [htarget] at hincrease hdecrease hle
      have hrecipient' : recipient = (Sevm.argWord e 0).toAdr := by
        apply Adr.toB256_inj
        rw [hrecipient]
        exact normalizedAddressArg_eq_toAdr_toB256 e 0
      subst recipient
      have hatom : primaryFlowAtom e = some
          (.flashPair (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            (Sevm.argWord e 2).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          flashLoanSelector_ne_depositSelector,
          flashLoanSelector_ne_depositToSelector,
          flashLoanSelector_ne_depositToAndCallSelector,
          flashLoanSelector_ne_transferSelector,
          flashLoanSelector_ne_transferAndCallSelector,
          flashLoanSelector_ne_transferFromSelector,
          flashLoanSelector_ne_withdrawSelector,
          flashLoanSelector_ne_withdrawToSelector,
          flashLoanSelector_ne_withdrawFromSelector]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      unfold Blanc.Weth10.Exec.Frame.HasLocalOwnEffect
      refine ⟨Stor.rest (Devm.getStor post ca), ?_⟩
      apply localOwnEffect_flashPair
      · rfl
      · unfold FlowAction.ExactCredit
        simp only [FlowAtom.creditOccurrence]
        rw [toB256_toNat]
      · unfold FlowAction.HasFlashDebitSource
        simp [primaryDebitProvenance, hnonempty, hselector,
          flashLoanSelector_ne_transferSelector,
          flashLoanSelector_ne_transferAndCallSelector,
          flashLoanSelector_ne_transferFromSelector,
          flashLoanSelector_ne_withdrawSelector,
          flashLoanSelector_ne_withdrawToSelector,
          flashLoanSelector_ne_withdrawFromSelector]
      · exact hincrease
      · exact hle
      · exact hdecrease

/-- Every classified frame retains the exact accepted debit arm used by the
compiled program.  Direct debits are pinned to the caller, delegated debits
carry `CallerAllowanceAccepted`, and flash repayment carries
`FlashAllowanceAccepted` for the same branch stored in the action. -/
theorem Exec.Frame.hasAcceptedDebit_of_flowAction?_eq_some
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasAcceptedDebit dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hdebit := debit_eq_of_flowAction_eq context haction
      refine ⟨context, haction, ?_⟩
      by_cases hempty : e.data.length.toB256 = 0
      · apply FlowAction.AcceptedDebit.none
        rw [hdebit]
        simp [primaryDebitProvenance, hempty]
      have hnonempty : e.data.length.toB256 ≠ 0 := hempty
      by_cases htransfer : Sevm.selector e = transferSelector
      · apply FlowAction.AcceptedDebit.direct e.caller.toB256 e.caller
        rw [hdebit]
        simp [primaryDebitProvenance, hnonempty, htransfer]
      by_cases htransferCall :
          Sevm.selector e = transferAndCallSelector
      · apply FlowAction.AcceptedDebit.direct e.caller.toB256 e.caller
        rw [hdebit]
        simp [primaryDebitProvenance, hnonempty, htransferCall]
      by_cases hwithdraw : Sevm.selector e = withdrawSelector
      · apply FlowAction.AcceptedDebit.direct e.caller.toB256 e.caller
        rw [hdebit]
        simp [primaryDebitProvenance, hnonempty, hwithdraw]
      by_cases hwithdrawTo : Sevm.selector e = withdrawToSelector
      · apply FlowAction.AcceptedDebit.direct e.caller.toB256 e.caller
        rw [hdebit]
        simp [primaryDebitProvenance, hnonempty, hwithdrawTo]
      by_cases htransferFrom : Sevm.selector e = transferFromSelector
      · have heffect := (weth10_transferFrom_successEffect dp
          context.memory_wf context.memory_reads_empty run
          context.invocation.2.2.2
          (by simpa only [transferFromSelector] using htransferFrom)
          hnonempty).2
        rcases heffect with ⟨corePre, hallowance, hcore⟩
        apply FlowAction.AcceptedDebit.delegated
          (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr corePre
          (callerAllowanceBranch e pre 2)
        · rw [hdebit]
          simp [primaryDebitProvenance, hnonempty, htransferFrom,
            transferFromSelector_ne_transferSelector,
            transferFromSelector_ne_transferAndCallSelector,
            transferFromSelector_ne_withdrawSelector,
            transferFromSelector_ne_withdrawToSelector]
        · exact callerAllowanceBranch_accepted hallowance
      by_cases hwithdrawFrom : Sevm.selector e = withdrawFromSelector
      · have heffect := (weth10_withdrawFrom_successEffect dp
          context.memory_wf context.memory_reads_empty run
          context.invocation.2.2.2
          (by simpa only [withdrawFromSelector] using hwithdrawFrom)
          hnonempty).2
        rcases heffect with ⟨corePre, hallowance, hcore⟩
        apply FlowAction.AcceptedDebit.delegated
          (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr corePre
          (callerAllowanceBranch e pre 2)
        · rw [hdebit]
          simp [primaryDebitProvenance, hnonempty, hwithdrawFrom,
            withdrawFromSelector_ne_transferSelector,
            withdrawFromSelector_ne_transferAndCallSelector,
            withdrawFromSelector_ne_withdrawSelector,
            withdrawFromSelector_ne_withdrawToSelector,
            withdrawFromSelector_ne_transferFromSelector]
        · exact callerAllowanceBranch_accepted hallowance
      by_cases hflash : Sevm.selector e = flashLoanSelector
      · have htarget : e.currentTarget = ca := context.invocation.2.1
        have hstateCode : pre.getCode e.currentTarget = e.code := by
          rw [htarget]
          exact context.stateCode_eq
        have heffect := (weth10_flashLoan_rawSuccessEffect dp
          context.invocation.2.2.2 hstateCode hflash hnonempty
          context.memory_wf context.memory_reads_empty run).2
        unfold RawFlashLoanSuccessEffect at heffect
        rcases heffect with
          ⟨h0, h1, h2, htoken, recipient, sc, mid, settle, burn,
            callbackLogs, base, hrecipient, hbase, hamount, htotal,
            hincrease, hcounterSc, hcodeSc, hbalSc, hmemory, hmintLogs,
            houtputSc, hcontinuation, hcallback, hcallbackLogs, hstorMid,
            hbalMid, hcodeMid, hsettleLogs, hsettleOutput, hsettleRun,
            hburnRun, hallowance, hdecrease, hle, hcounterPost,
            hlogFork, htrue, hbalPost, hcodePost⟩
        apply FlowAction.AcceptedDebit.flash
          (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr settle burn
          (flashAllowanceBranchFromPost e post)
        · rw [hdebit]
          simp [primaryDebitProvenance, hnonempty, hflash,
            flashLoanSelector_ne_transferSelector,
            flashLoanSelector_ne_transferAndCallSelector,
            flashLoanSelector_ne_withdrawSelector,
            flashLoanSelector_ne_withdrawToSelector,
            flashLoanSelector_ne_transferFromSelector,
            flashLoanSelector_ne_withdrawFromSelector,
            Exec.Frame.post, Execution.committedPost]
        · exact flashSettlement_reconstruction hallowance hburnRun
        · simpa [Exec.Frame.post, Execution.committedPost] using hburnRun
      · apply FlowAction.AcceptedDebit.none
        rw [hdebit]
        simp [primaryDebitProvenance, hnonempty, htransfer,
          htransferCall, hwithdraw, hwithdrawTo, htransferFrom,
          hwithdrawFrom, hflash]

/-- Every executable flow classification is paired with the exact emitter
effect established by the corresponding compiled functional theorem.  Raw
ERC677 and flash effects deliberately retain the concrete callback boundary
and its arbitrary child-log segment. -/
theorem Exec.Frame.hasGenuineWethEmitterEffect_of_flowAction?_eq_some
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasGenuineWethEmitterEffect dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      refine ⟨context, haction, ?_⟩
      by_cases hempty : e.data.length.toB256 = 0
      · apply GenuineWethEmitterEffect.receive hempty
        have heffect := receive_exec_effect dp context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          heffect.2.2.1
      have hnonempty : e.data.length.toB256 ≠ 0 := hempty
      by_cases hdeposit : Sevm.selector e = depositSelector
      · apply GenuineWethEmitterEffect.deposit hdeposit
        have heffect := deposit_exec_effect dp context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2
          (by simpa only [depositSelector] using hdeposit) hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          heffect.2.2.1
      by_cases hdepositTo : Sevm.selector e = depositToSelector
      · apply GenuineWethEmitterEffect.depositTo hdepositTo
        have heffect := depositTo_exec_effect dp context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2
          (by simpa only [depositToSelector] using hdepositTo) hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          heffect.2.1
      by_cases hdepositCall :
          Sevm.selector e = depositToAndCallSelector
      · apply GenuineWethEmitterEffect.depositToAndCall hdepositCall
        have heffect := weth10_depositToAndCall_rawSuccessEffect dp
          context.invocation.2.2.2 hdepositCall hnonempty
          context.memory_wf context.memory_reads_empty run
        simpa only [Exec.Frame.post, Execution.committedPost] using heffect
      by_cases htransfer : Sevm.selector e = transferSelector
      · apply GenuineWethEmitterEffect.transfer htransfer
        have heffect := (weth10_transfer_successEffect dp
          context.memory_wf context.memory_reads_empty run
          context.invocation.2.2.2
          (by simpa only [transferSelector] using htransfer) hnonempty).2
        simpa only [Exec.Frame.post, Execution.committedPost] using heffect
      by_cases htransferCall :
          Sevm.selector e = transferAndCallSelector
      · apply GenuineWethEmitterEffect.transferAndCall htransferCall
        have heffect := (weth10_transferAndCall_rawSuccessEffect dp
          context.invocation.2.2.2 htransferCall hnonempty
          context.memory_wf context.memory_reads_empty run).2
        simpa only [Exec.Frame.post, Execution.committedPost] using heffect
      by_cases htransferFrom : Sevm.selector e = transferFromSelector
      · apply GenuineWethEmitterEffect.transferFrom htransferFrom
        have heffect := (weth10_transferFrom_successEffect dp
          context.memory_wf context.memory_reads_empty run
          context.invocation.2.2.2
          (by simpa only [transferFromSelector] using htransferFrom)
          hnonempty).2
        simpa only [Exec.Frame.post, Execution.committedPost] using heffect
      by_cases hwithdraw : Sevm.selector e = withdrawSelector
      · apply GenuineWethEmitterEffect.withdraw hwithdraw
        have heffect := (weth10_withdraw_successEffect dp
          context.memory_wf context.memory_reads_empty run
          context.invocation.2.2.2
          (by simpa only [withdrawSelector] using hwithdraw) hnonempty).2
        simpa only [Exec.Frame.post, Execution.committedPost] using heffect
      by_cases hwithdrawTo : Sevm.selector e = withdrawToSelector
      · apply GenuineWethEmitterEffect.withdrawTo hwithdrawTo
        have heffect := (weth10_withdrawTo_successEffect dp
          context.memory_wf context.memory_reads_empty run
          context.invocation.2.2.2
          (by simpa only [withdrawToSelector] using hwithdrawTo)
          hnonempty).2
        simpa only [Exec.Frame.post, Execution.committedPost] using heffect
      by_cases hwithdrawFrom : Sevm.selector e = withdrawFromSelector
      · apply GenuineWethEmitterEffect.withdrawFrom hwithdrawFrom
        have heffect := (weth10_withdrawFrom_successEffect dp
          context.memory_wf context.memory_reads_empty run
          context.invocation.2.2.2
          (by simpa only [withdrawFromSelector] using hwithdrawFrom)
          hnonempty).2
        simpa only [Exec.Frame.post, Execution.committedPost] using heffect
      by_cases hflash : Sevm.selector e = flashLoanSelector
      · apply GenuineWethEmitterEffect.flashLoan hflash
        have htarget : e.currentTarget = ca := context.invocation.2.1
        have hstateCode : pre.getCode e.currentTarget = e.code := by
          rw [htarget]
          exact context.stateCode_eq
        have heffect := (weth10_flashLoan_rawSuccessEffect dp
          context.invocation.2.2.2 hstateCode hflash hnonempty
          context.memory_wf context.memory_reads_empty run).2
        simpa only [Exec.Frame.post, Execution.committedPost] using heffect
      have hprimary : primaryFlowAtom e = none := by
        simp [primaryFlowAtom, hnonempty, hdeposit, hdepositTo,
          hdepositCall, htransfer, htransferCall, htransferFrom,
          hwithdraw, hwithdrawTo, hwithdrawFrom, hflash]
      simp [Blanc.Weth10.Exec.Frame.flowAction?, context.invocation, hprimary] at haction

/-- Reverse leaf classification for every recognized non-flow selector.
The recognized-leaf premise is deliberately explicit: deriving it from an
arbitrary successful `Exec` is supplied by the compiled dispatch bridge below.

All fourteen read leaves and `approve` are silent at the public endpoint.
`approveAndCall` and `permit` retain their exact recursive machine boundaries,
with every own balance-region prefix and suffix proved silent. -/
theorem Exec.Frame.hasNoWethBalanceOwnEffect_of_recognized
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hnone : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = none)
    (hrecognized : ∃ body,
      (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp) :
    Blanc.Weth10.Exec.Frame.HasNoWethBalanceOwnEffect dp ca frame := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      refine ⟨context, hnone, ?_⟩
      by_cases hempty : e.data.length.toB256 = 0
      · have hprimary : primaryFlowAtom e ≠ none := by
          simp [primaryFlowAtom, hempty]
        unfold Blanc.Weth10.Exec.Frame.flowAction? at hnone
        rw [if_pos context.invocation] at hnone
        cases h : primaryFlowAtom e with
        | none => exact (hprimary h).elim
        | some atom => simp [h] at hnone
      have hnonempty : e.data.length.toB256 ≠ 0 := hempty
      have hprimary : primaryFlowAtom e = none := by
        unfold Blanc.Weth10.Exec.Frame.flowAction? at hnone
        rw [if_pos context.invocation] at hnone
        cases h : primaryFlowAtom e with
        | none => rfl
        | some atom => simp [h] at hnone
      have hnotDeposit : Sevm.selector e ≠ depositSelector := by
        intro h
        simp [primaryFlowAtom, hnonempty, h] at hprimary
      have hnotDepositTo : Sevm.selector e ≠ depositToSelector := by
        intro h
        simp [primaryFlowAtom, hnonempty, h,
          depositToSelector_ne_depositSelector] at hprimary
      have hnotDepositCall :
          Sevm.selector e ≠ depositToAndCallSelector := by
        intro h
        simp [primaryFlowAtom, hnonempty, h,
          depositToAndCallSelector_ne_depositSelector] at hprimary
      have hnotTransfer : Sevm.selector e ≠ transferSelector := by
        intro h
        simp [primaryFlowAtom, hnonempty, h,
          transferSelector_ne_depositSelector,
          transferSelector_ne_depositToSelector,
          transferSelector_ne_depositToAndCallSelector] at hprimary
        split at hprimary <;> simp_all
      have hnotTransferCall :
          Sevm.selector e ≠ transferAndCallSelector := by
        intro h
        simp [primaryFlowAtom, hnonempty, h,
          transferAndCallSelector_ne_depositSelector,
          transferAndCallSelector_ne_depositToSelector,
          transferAndCallSelector_ne_depositToAndCallSelector] at hprimary
        split at hprimary <;> simp_all
      have hnotTransferFrom :
          Sevm.selector e ≠ transferFromSelector := by
        intro h
        simp [primaryFlowAtom, hnonempty, h,
          transferFromSelector_ne_depositSelector,
          transferFromSelector_ne_depositToSelector,
          transferFromSelector_ne_depositToAndCallSelector,
          transferFromSelector_ne_transferSelector,
          transferFromSelector_ne_transferAndCallSelector] at hprimary
        split at hprimary <;> simp_all
      have hnotWithdraw : Sevm.selector e ≠ withdrawSelector := by
        intro h
        simp [primaryFlowAtom, hnonempty, h,
          withdrawSelector_ne_depositSelector,
          withdrawSelector_ne_depositToSelector,
          withdrawSelector_ne_depositToAndCallSelector,
          withdrawSelector_ne_transferSelector,
          withdrawSelector_ne_transferAndCallSelector,
          withdrawSelector_ne_transferFromSelector]
          at hprimary
      have hnotWithdrawTo : Sevm.selector e ≠ withdrawToSelector := by
        intro h
        simp [primaryFlowAtom, hnonempty, h,
          withdrawToSelector_ne_depositSelector,
          withdrawToSelector_ne_depositToSelector,
          withdrawToSelector_ne_depositToAndCallSelector,
          withdrawToSelector_ne_transferSelector,
          withdrawToSelector_ne_transferAndCallSelector,
          withdrawToSelector_ne_transferFromSelector,
          withdrawToSelector_ne_withdrawSelector] at hprimary
      have hnotWithdrawFrom :
          Sevm.selector e ≠ withdrawFromSelector := by
        intro h
        simp [primaryFlowAtom, hnonempty, h,
          withdrawFromSelector_ne_depositSelector,
          withdrawFromSelector_ne_depositToSelector,
          withdrawFromSelector_ne_depositToAndCallSelector,
          withdrawFromSelector_ne_transferSelector,
          withdrawFromSelector_ne_transferAndCallSelector,
          withdrawFromSelector_ne_transferFromSelector,
          withdrawFromSelector_ne_withdrawSelector,
          withdrawFromSelector_ne_withdrawToSelector] at hprimary
      have hnotFlash : Sevm.selector e ≠ flashLoanSelector := by
        intro h
        simp [primaryFlowAtom, hnonempty, h,
          flashLoanSelector_ne_depositSelector,
          flashLoanSelector_ne_depositToSelector,
          flashLoanSelector_ne_depositToAndCallSelector,
          flashLoanSelector_ne_transferSelector,
          flashLoanSelector_ne_transferAndCallSelector,
          flashLoanSelector_ne_transferFromSelector,
          flashLoanSelector_ne_withdrawSelector,
          flashLoanSelector_ne_withdrawToSelector,
          flashLoanSelector_ne_withdrawFromSelector] at hprimary
      rcases hrecognized with ⟨body, hbody⟩
      have hselmem : Sevm.selector e ∈
          (weth10Funcs dp).map Prod.fst := by
        exact List.mem_map.mpr ⟨(Sevm.selector e, body), hbody, rfl⟩
      simp only [weth10Funcs, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hselmem
      rcases hselmem with
          hname | happrove | htotalSupply | hwithdrawTo |
          htransferFrom | hwithdraw | hpermitTypehash | hdecimals |
          hdomainSeparator | htransferCall | hflash | hdepositCall |
          hmaxFlashLoan | hbalanceOf | hnonces | hcallbackSuccess |
          hflashMinted | hwithdrawFrom | hsymbol | htransfer |
          hdepositTo | happroveCall | hdeploymentChainId | hdeposit |
          hpermit | hflashFee | hallowance
      · apply NoWethBalanceOwnEffect.name hname
        have heffect := name_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hname
          hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · apply NoWethBalanceOwnEffect.approve happrove
        have heffect := approve_exec_effect dp context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 happrove
          hnonempty
        rw [Exec.Frame.post, Execution.committedPost, heffect.2.1]
        unfold approveRuntimeKey
        exact Stor.Weth10Silent.set
          (runtimeAllowanceKey_not_valid _)
          (runtimeAllowanceKey_ne_flash _)
      · apply NoWethBalanceOwnEffect.totalSupply htotalSupply
        have heffect := totalSupply_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2
          htotalSupply hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · exact (hnotWithdrawTo (by
          simpa only [withdrawToSelector] using hwithdrawTo)).elim
      · exact (hnotTransferFrom (by
          simpa only [transferFromSelector] using htransferFrom)).elim
      · exact (hnotWithdraw (by
          simpa only [withdrawSelector] using hwithdraw)).elim
      · apply NoWethBalanceOwnEffect.permitTypehash hpermitTypehash
        have heffect := permitTypehash_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2
          hpermitTypehash hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · apply NoWethBalanceOwnEffect.decimals hdecimals
        have heffect := decimals_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hdecimals
          hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · apply NoWethBalanceOwnEffect.domainSeparator hdomainSeparator
        have heffect := domainSeparator_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2
          hdomainSeparator hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · exact (hnotTransferCall (by
          simpa only [transferAndCallSelector] using htransferCall)).elim
      · exact (hnotFlash (by
          simpa only [flashLoanSelector] using hflash)).elim
      · exact (hnotDepositCall (by
          simpa only [depositToAndCallSelector] using hdepositCall)).elim
      · apply NoWethBalanceOwnEffect.maxFlashLoan hmaxFlashLoan
        have heffect := maxFlashLoan_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2
          hmaxFlashLoan hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · apply NoWethBalanceOwnEffect.balanceOf hbalanceOf
        have heffect := balanceOf_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hbalanceOf
          hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · apply NoWethBalanceOwnEffect.nonces hnonces
        have heffect := nonces_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hnonces
          hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · apply NoWethBalanceOwnEffect.callbackSuccess hcallbackSuccess
        have heffect := callbackSuccess_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2
          hcallbackSuccess hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · apply NoWethBalanceOwnEffect.flashMinted hflashMinted
        have heffect := flashMinted_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2
          hflashMinted hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · exact (hnotWithdrawFrom (by
          simpa only [withdrawFromSelector] using hwithdrawFrom)).elim
      · apply NoWethBalanceOwnEffect.symbol hsymbol
        have heffect := symbol_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hsymbol
          hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · exact (hnotTransfer (by
          simpa only [transferSelector] using htransfer)).elim
      · exact (hnotDepositTo (by
          simpa only [depositToSelector] using hdepositTo)).elim
      · have happroveCall' : Sevm.selector e = approveAndCallSelector := by
          simpa only [approveAndCallSelector] using happroveCall
        rcases exec_enters_weth10Nonpayable_logs (body := approveAndCall) run
            context.invocation.2.2.2 happroveCall' hnonempty
            (by simp [weth10Funcs, approveAndCallSelector]) with
          ⟨bodyPre, hvalue, hstor, hbal, hcode, hmemory, hlogs,
            houtput, hbodyRun⟩
        simp only [approveAndCall] at hbodyRun
        rcases of_run_prepend approvePrefix _ hbodyRun with
          ⟨callbackPre, hprefix, hcontinuation⟩
        apply NoWethBalanceOwnEffect.approveAndCall happroveCall'
          callbackPre
        · exact (Stor.Weth10Silent.of_eq
            (congrFun hstor e.currentTarget).symm).trans
              (approvePrefix_storage_silent hprefix)
        · simpa only [Exec.Frame.post, Execution.committedPost] using
            hcontinuation
      · apply NoWethBalanceOwnEffect.deploymentChainId hdeploymentChainId
        have heffect := deploymentChainId_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2
          hdeploymentChainId hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · exact (hnotDeposit (by
          simpa only [depositSelector] using hdeposit)).elim
      · have hpermit' : Sevm.selector e = permitSelector := by
          simpa only [permitSelector] using hpermit
        rcases exec_enters_weth10Selector_logs run
            context.invocation.2.2.2 hpermit' hnonempty
            (permit_mem_weth10Funcs dp) with
          ⟨permitPre, hstor, hbal, hcode, hmemory, hlogs, houtput,
            hpermitRun⟩
        apply NoWethBalanceOwnEffect.permit hpermit'
        exact (permit_balanceSilent dp hpermitRun).prepend
          (Stor.Weth10Silent.of_eq
            (congrFun hstor e.currentTarget).symm)
      · apply NoWethBalanceOwnEffect.flashFee hflashFee
        have heffect := flashFee_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hflashFee
          hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect
      · apply NoWethBalanceOwnEffect.allowance hallowance
        have heffect := allowance_exec_output context.memory_wf
          context.memory_reads_empty run context.invocation.2.2.2 hallowance
          hnonempty
        simpa only [Exec.Frame.post, Execution.committedPost] using
          publicReadResult_weth10Silent heffect

/-- Rich receive classification with the mint segment ending at the committed
frame endpoint. -/
theorem Exec.Frame.hasRichLocalStorageEffect_of_receive
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hempty : frame.sevm.data.length.toB256 = 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := receive_exec_effect dp context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2 hempty
      have hinc := heffect.1
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rw [htarget] at hinc
      have haction' := haction
      simp [Blanc.Weth10.Exec.Frame.flowAction?, context.invocation, primaryFlowAtom,
        primaryDebitProvenance, hempty] at haction'
      symm at haction'
      subst action
      refine ⟨context, haction, .ordinaryMint ?_⟩
      apply localSegment_ordinaryMint
      · rfl
      · unfold FlowAction.ExactCredit
        simp only [FlowAtom.creditOccurrence]
        rw [toB256_toNat]
      · rfl
      · exact hinc

theorem Exec.Frame.hasRichLocalStorageEffect_of_deposit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = depositSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := deposit_exec_effect dp context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        (by simpa only [depositSelector] using hselector) hnonempty
      have hinc := heffect.1
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rw [htarget] at hinc
      have haction' := haction
      simp [Blanc.Weth10.Exec.Frame.flowAction?, context.invocation, primaryFlowAtom,
        primaryDebitProvenance, hnonempty, hselector,
        depositSelector_ne_transferSelector,
        depositSelector_ne_transferAndCallSelector,
        depositSelector_ne_withdrawSelector,
        depositSelector_ne_withdrawToSelector,
        depositSelector_ne_transferFromSelector,
        depositSelector_ne_withdrawFromSelector,
        depositSelector_ne_flashLoanSelector] at haction'
      symm at haction'
      subst action
      refine ⟨context, haction, .ordinaryMint ?_⟩
      apply localSegment_ordinaryMint
      · rfl
      · unfold FlowAction.ExactCredit
        simp only [FlowAtom.creditOccurrence]
        rw [toB256_toNat]
      · rfl
      · exact hinc

theorem Exec.Frame.hasRichLocalStorageEffect_of_depositTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = depositToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := depositTo_exec_effect dp context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        (by simpa only [depositToSelector] using hselector) hnonempty
      have hstor := heffect.1
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rw [htarget, normalizedAddressArg_eq_toAdr_toB256] at hstor
      have hincrease : Increase (Sevm.argWord e 0).toAdr e.value
          (Stor.rest (Devm.getStor pre ca))
          (Stor.rest (Devm.getStor post ca)) := by
        rw [hstor]
        exact Stor.increase_set _ _ _
      have hatom : primaryFlowAtom e = some
          (.ordinaryMint (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            e.value.toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          depositToSelector_ne_depositSelector]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      refine ⟨context, haction, .ordinaryMint ?_⟩
      apply localSegment_ordinaryMint
      · rfl
      · unfold FlowAction.ExactCredit
        simp only [FlowAtom.creditOccurrence]
        rw [toB256_toNat]
      · simp [primaryDebitProvenance, hnonempty, hselector,
        depositToSelector_ne_transferSelector,
          depositToSelector_ne_transferAndCallSelector,
          depositToSelector_ne_transferFromSelector,
          depositToSelector_ne_withdrawSelector,
          depositToSelector_ne_withdrawToSelector,
          depositToSelector_ne_withdrawFromSelector,
          depositToSelector_ne_flashLoanSelector]
      · exact hincrease

theorem Exec.Frame.hasRichLocalStorageEffect_of_depositToAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = depositToAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := weth10_depositToAndCall_rawStepSuccessEffect dp
        context.invocation.2.2.2 hselector hnonempty context.memory_wf
        context.memory_reads_empty run
      rcases heffect with
        ⟨callbackPre, inputSize, input, hstor, hlogs, hbal, hcode,
          houtput, hboundary⟩
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rw [htarget, normalizedAddressArg_eq_toAdr_toB256] at hstor
      have hincrease : Increase (Sevm.argWord e 0).toAdr e.value
          (Stor.rest (Devm.getStor pre ca))
          (Stor.rest (Devm.getStor callbackPre ca)) := by
        rw [hstor]
        exact Stor.increase_set _ _ _
      have hatom : primaryFlowAtom e = some
          (.ordinaryMint (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            e.value.toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          depositToAndCallSelector_ne_depositSelector]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      refine ⟨context, haction, ?_⟩
      apply RichLocalStorageEffect.tokenCallback .ordinaryMint callbackPre
        (Sevm.argWord e 0).toAdr (Sevm.argWord e 0)
        onTokenTransferSelector e.value (Sevm.tailLen e 1) inputSize
        (Sevm.tailBytes e 1) input
      · apply localSegment_ordinaryMint
        · rfl
        · unfold FlowAction.ExactCredit
          simp only [FlowAtom.creditOccurrence]
          rw [toB256_toNat]
        · simp [primaryDebitProvenance, hnonempty, hselector,
          depositToAndCallSelector_ne_transferSelector,
            depositToAndCallSelector_ne_transferAndCallSelector,
            depositToAndCallSelector_ne_transferFromSelector,
            depositToAndCallSelector_ne_withdrawSelector,
            depositToAndCallSelector_ne_withdrawToSelector,
            depositToAndCallSelector_ne_withdrawFromSelector,
            depositToAndCallSelector_ne_flashLoanSelector]
        · exact hincrease
      · exact congrFun hcode ca
      · exact hboundary

theorem Exec.Frame.hasRichLocalStorageEffect_of_transfer
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := (weth10_transfer_successEffect dp
        context.memory_wf context.memory_reads_empty run
        context.invocation.2.2.2
        (by simpa only [transferSelector] using hselector) hnonempty).2
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rcases heffect with hzero | hnonzero
      · rcases hzero with
          ⟨hraw, callPre, guardPost, hprefix, hstorGuard, hbalGuard,
            hcodeGuard, hlogsGuard, htrue⟩
        have htrace := exists_burnCallPrefixTrace hprefix
        have hprefix' := hprefix
        unfold BurnCallPrefix at hprefix'
        rw [htarget] at hprefix'
        have hatom : primaryFlowAtom e = some
            (.redemption e.caller.toB256 e.caller e.caller
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector,
            transferSelector_ne_depositSelector,
            transferSelector_ne_depositToSelector,
            transferSelector_ne_depositToAndCallSelector, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        refine ⟨context, haction, ?_⟩
        apply RichLocalStorageEffect.redemption pre callPre guardPost
          e.caller (Sevm.argWord e 1) e.caller.toB256
        · exact Stor.Weth10Silent.rfl
        · rfl
        · apply localSegment_redemption
          · rfl
          · rfl
          · unfold FlowAction.HasDebitSource
            simp [primaryDebitProvenance, hnonempty, hselector]
          · exact hprefix'.2.1
          · exact hprefix'.1
        · exact hprefix
        · exact htrace
        · exact Stor.Weth10Silent.of_eq (congrFun hstorGuard ca)
      · rcases hnonzero with
          ⟨hraw, recipient, hrecipient, htransfer, _⟩
        rw [htarget] at htransfer
        have hrecipient' : recipient = (Sevm.argWord e 0).toAdr := by
          apply Adr.toB256_inj
          rw [hrecipient]
          exact normalizedAddressArg_eq_toAdr_toB256 e 0
        subst recipient
        have hatom : primaryFlowAtom e = some
            (.transfer e.caller.toB256 (Sevm.argWord e 0) e.caller
              (Sevm.argWord e 0).toAdr
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector,
            transferSelector_ne_depositSelector,
            transferSelector_ne_depositToSelector,
            transferSelector_ne_depositToAndCallSelector, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        refine ⟨context, haction, .ordinaryTransfer ?_⟩
        apply localSegment_ordinaryTransfer
        · rfl
        · unfold FlowAction.ExactCredit
          simp only [FlowAtom.creditOccurrence]
          rw [toB256_toNat]
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector]
        · exact htransfer

theorem Exec.Frame.hasRichLocalStorageEffect_of_transferAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := (weth10_transferAndCall_rawStepSuccessEffect dp
        context.invocation.2.2.2 hselector hnonempty context.memory_wf
        context.memory_reads_empty run).2
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rcases heffect with hzero | hnonzero
      · rcases hzero with
          ⟨hraw, callPre, callbackPre, inputSize, input, hprefix,
            hboundary⟩
        have htrace := exists_burnCallPrefixTrace hprefix
        have hprefix' := hprefix
        unfold BurnCallPrefix at hprefix'
        rw [htarget] at hprefix'
        have hatom : primaryFlowAtom e = some
            (.redemption e.caller.toB256 e.caller e.caller
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector,
            transferAndCallSelector_ne_depositSelector,
            transferAndCallSelector_ne_depositToSelector,
            transferAndCallSelector_ne_depositToAndCallSelector, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        refine ⟨context, haction, ?_⟩
        apply RichLocalStorageEffect.redemptionThenTokenCallback
          callPre callbackPre e.caller (Sevm.argWord e 1)
          e.caller.toB256 (Sevm.argWord e 0).toAdr
          (Sevm.argWord e 0) onTokenTransferSelector
          (Sevm.argWord e 1) (Sevm.tailLen e 2) inputSize
          (Sevm.tailBytes e 2) input
        · apply localSegment_redemption
          · rfl
          · rfl
          · unfold FlowAction.HasDebitSource
            simp [primaryDebitProvenance, hnonempty, hselector]
          · exact hprefix'.2.1
          · exact hprefix'.1
        · exact hprefix
        · exact htrace
        · exact hboundary
      · rcases hnonzero with
          ⟨hraw, recipient, callbackPre, inputSize, input, hrecipient,
            htransfer, hflash, hlogs, hbal, hcode, houtput, hboundary⟩
        rw [htarget] at htransfer
        have hrecipient' : recipient = (Sevm.argWord e 0).toAdr := by
          apply Adr.toB256_inj
          rw [hrecipient]
          exact normalizedAddressArg_eq_toAdr_toB256 e 0
        subst recipient
        have hatom : primaryFlowAtom e = some
            (.transfer e.caller.toB256 (Sevm.argWord e 0) e.caller
              (Sevm.argWord e 0).toAdr
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector,
            transferAndCallSelector_ne_depositSelector,
            transferAndCallSelector_ne_depositToSelector,
            transferAndCallSelector_ne_depositToAndCallSelector, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        refine ⟨context, haction, ?_⟩
        apply RichLocalStorageEffect.tokenCallback .ordinaryTransfer
          callbackPre (Sevm.argWord e 0).toAdr (Sevm.argWord e 0)
          onTokenTransferSelector (Sevm.argWord e 1)
          (Sevm.tailLen e 2) inputSize (Sevm.tailBytes e 2) input
        · apply localSegment_ordinaryTransfer
          · rfl
          · unfold FlowAction.ExactCredit
            simp only [FlowAtom.creditOccurrence]
            rw [toB256_toNat]
          · unfold FlowAction.HasDebitSource
            simp [primaryDebitProvenance, hnonempty, hselector]
          · exact htransfer
        · exact congrFun hcode ca
        · exact hboundary

theorem Exec.Frame.hasRichLocalStorageEffect_of_transferFrom
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := (weth10_transferFrom_successEffect dp
        context.memory_wf context.memory_reads_empty run
        context.invocation.2.2.2
        (by simpa only [transferFromSelector] using hselector)
        hnonempty).2
      rcases heffect with ⟨corePre, hallowance, hcore⟩
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hrest := callerAllowanceOutcome_rest_eq hallowance
      have hsilent := callerAllowanceOutcome_weth10Silent hallowance
      rw [htarget] at hrest hsilent
      have hsource : (normalizedAddressArg e 0).toAdr =
          (Sevm.argWord e 0).toAdr := by
        rw [normalizedAddressArg_eq_toAdr_toB256, toAdr_toB256]
      rcases hcore with hzero | hnonzero
      · rcases hzero with ⟨hraw, hburn⟩
        rcases hburn with
          ⟨callPre, guardPost, hprefix, hstorGuard, hbalGuard,
            hcodeGuard, hlogsGuard, htrue⟩
        have htrace := exists_burnCallPrefixTrace hprefix
        have hprefix' := hprefix
        unfold BurnCallPrefix at hprefix'
        rw [htarget, hrest, hsource] at hprefix'
        have hatom : primaryFlowAtom e = some
            (.redemption (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
              e.caller (Sevm.argWord e 2).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector,
            transferFromSelector_ne_depositSelector,
            transferFromSelector_ne_depositToSelector,
            transferFromSelector_ne_depositToAndCallSelector,
            transferFromSelector_ne_transferSelector,
            transferFromSelector_ne_transferAndCallSelector, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        refine ⟨context, haction, ?_⟩
        apply RichLocalStorageEffect.redemption corePre callPre guardPost
          (Sevm.argWord e 0).toAdr (Sevm.argWord e 2) e.caller.toB256
        · exact hsilent
        · exact congrFun hallowance.2.2.2 ca
        · apply localSegment_redemption
          · rfl
          · rfl
          · unfold FlowAction.HasDebitSource
            simp [primaryDebitProvenance, hnonempty, hselector,
              transferFromSelector_ne_transferSelector,
              transferFromSelector_ne_transferAndCallSelector,
              transferFromSelector_ne_withdrawSelector,
              transferFromSelector_ne_withdrawToSelector]
          · exact hprefix'.2.1
          · exact hprefix'.1
        · simpa only [hsource] using hprefix
        · simpa only [hsource] using htrace
        · exact Stor.Weth10Silent.of_eq (congrFun hstorGuard ca)
      · rcases hnonzero with
          ⟨hraw, recipient, hrecipient, htransfer, hflash, hlogs,
            htrue, hbal, hcode⟩
        rw [htarget, hrest, hsource] at htransfer
        have hrecipient' : recipient = (Sevm.argWord e 1).toAdr := by
          apply Adr.toB256_inj
          rw [hrecipient]
          exact normalizedAddressArg_eq_toAdr_toB256 e 1
        subst recipient
        have hatom : primaryFlowAtom e = some
            (.transfer (Sevm.argWord e 0) (Sevm.argWord e 1)
              (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toAdr
              (Sevm.argWord e 2).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector,
            transferFromSelector_ne_depositSelector,
            transferFromSelector_ne_depositToSelector,
            transferFromSelector_ne_depositToAndCallSelector,
            transferFromSelector_ne_transferSelector,
            transferFromSelector_ne_transferAndCallSelector, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        refine ⟨context, haction, .ordinaryTransfer ?_⟩
        apply localSegment_ordinaryTransfer
        · rfl
        · unfold FlowAction.ExactCredit
          simp only [FlowAtom.creditOccurrence]
          rw [toB256_toNat]
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector,
            transferFromSelector_ne_transferSelector,
            transferFromSelector_ne_transferAndCallSelector,
            transferFromSelector_ne_withdrawSelector,
            transferFromSelector_ne_withdrawToSelector]
        · exact htransfer

theorem Exec.Frame.hasRichLocalStorageEffect_of_withdraw
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := (weth10_withdraw_successEffect dp
        context.memory_wf context.memory_reads_empty run
        context.invocation.2.2.2
        (by simpa only [withdrawSelector] using hselector) hnonempty).2
      rcases heffect with ⟨callPre, hprefix⟩
      have htrace := exists_burnCallPrefixTrace hprefix
      have hprefix' := hprefix
      unfold BurnCallPrefix at hprefix'
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rw [htarget] at hprefix'
      have hatom : primaryFlowAtom e = some
          (.redemption e.caller.toB256 e.caller e.caller
            (Sevm.argWord e 0).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          withdrawSelector_ne_depositSelector,
          withdrawSelector_ne_depositToSelector,
          withdrawSelector_ne_depositToAndCallSelector,
          withdrawSelector_ne_transferSelector,
          withdrawSelector_ne_transferAndCallSelector,
          withdrawSelector_ne_transferFromSelector]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      refine ⟨context, haction, ?_⟩
      apply RichLocalStorageEffect.redemption pre callPre post e.caller
        (Sevm.argWord e 0) e.caller.toB256
      · exact Stor.Weth10Silent.rfl
      · rfl
      · apply localSegment_redemption
        · rfl
        · rfl
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector]
        · exact hprefix'.2.1
        · exact hprefix'.1
      · exact hprefix
      · exact htrace
      · exact Stor.Weth10Silent.rfl

theorem Exec.Frame.hasRichLocalStorageEffect_of_withdrawTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := (weth10_withdrawTo_successEffect dp
        context.memory_wf context.memory_reads_empty run
        context.invocation.2.2.2
        (by simpa only [withdrawToSelector] using hselector)
        hnonempty).2
      rcases heffect with ⟨callPre, hprefix⟩
      have htrace := exists_burnCallPrefixTrace hprefix
      have hprefix' := hprefix
      unfold BurnCallPrefix at hprefix'
      have htarget : e.currentTarget = ca := context.invocation.2.1
      rw [htarget] at hprefix'
      have hatom : primaryFlowAtom e = some
          (.redemption e.caller.toB256 e.caller
            (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          withdrawToSelector_ne_depositSelector,
          withdrawToSelector_ne_depositToSelector,
          withdrawToSelector_ne_depositToAndCallSelector,
          withdrawToSelector_ne_transferSelector,
          withdrawToSelector_ne_transferAndCallSelector,
          withdrawToSelector_ne_transferFromSelector,
          withdrawToSelector_ne_withdrawSelector]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      refine ⟨context, haction, ?_⟩
      apply RichLocalStorageEffect.redemption pre callPre post e.caller
        (Sevm.argWord e 1) (Sevm.argWord e 0)
      · exact Stor.Weth10Silent.rfl
      · rfl
      · apply localSegment_redemption
        · rfl
        · rfl
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector]
        · exact hprefix'.2.1
        · exact hprefix'.1
      · exact hprefix
      · exact htrace
      · exact Stor.Weth10Silent.rfl

theorem Exec.Frame.hasRichLocalStorageEffect_of_withdrawFrom
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := (weth10_withdrawFrom_successEffect dp
        context.memory_wf context.memory_reads_empty run
        context.invocation.2.2.2
        (by simpa only [withdrawFromSelector] using hselector)
        hnonempty).2
      rcases heffect with ⟨corePre, hallowance, callPre, hprefix⟩
      have htrace := exists_burnCallPrefixTrace hprefix
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hrest := callerAllowanceOutcome_rest_eq hallowance
      have hsilent := callerAllowanceOutcome_weth10Silent hallowance
      rw [htarget] at hrest hsilent
      have hsource : (normalizedAddressArg e 0).toAdr =
          (Sevm.argWord e 0).toAdr := by
        rw [normalizedAddressArg_eq_toAdr_toB256, toAdr_toB256]
      have hprefix' := hprefix
      unfold BurnCallPrefix at hprefix'
      rw [htarget, hrest, hsource] at hprefix'
      have hatom : primaryFlowAtom e = some
          (.redemption (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            (Sevm.argWord e 1).toAdr (Sevm.argWord e 2).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          withdrawFromSelector_ne_depositSelector,
          withdrawFromSelector_ne_depositToSelector,
          withdrawFromSelector_ne_depositToAndCallSelector,
          withdrawFromSelector_ne_transferSelector,
          withdrawFromSelector_ne_transferAndCallSelector,
          withdrawFromSelector_ne_transferFromSelector,
          withdrawFromSelector_ne_withdrawSelector,
          withdrawFromSelector_ne_withdrawToSelector]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      refine ⟨context, haction, ?_⟩
      apply RichLocalStorageEffect.redemption corePre callPre post
        (Sevm.argWord e 0).toAdr (Sevm.argWord e 2)
        (Sevm.argWord e 1)
      · exact hsilent
      · exact congrFun hallowance.2.2.2 ca
      · apply localSegment_redemption
        · rfl
        · rfl
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector,
            withdrawFromSelector_ne_transferSelector,
            withdrawFromSelector_ne_transferAndCallSelector,
            withdrawFromSelector_ne_transferFromSelector,
            withdrawFromSelector_ne_withdrawSelector,
            withdrawFromSelector_ne_withdrawToSelector]
        · exact hprefix'.2.1
        · exact hprefix'.1
      · simpa only [hsource] using hprefix
      · simpa only [hsource] using htrace
      · exact Stor.Weth10Silent.rfl

theorem Exec.Frame.hasRichLocalStorageEffect_of_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hmem :
          (flashLoanSelector, nonpayable flashLoan) ∈ weth10Funcs dp := by
        simp [flashLoanSelector, weth10Funcs]
      rcases exec_enters_weth10Nonpayable_logs run
          context.invocation.2.2.2 hselector hnonempty hmem with
        ⟨bodyPre, hvalue, hstorEntry, hbalEntry, hcodeEntry, hmemoryEntry,
          hlogsEntry, houtputEntry, hbody⟩
      have hwfBody : Mem.Wf bodyPre.memory := by
        rw [hmemoryEntry]
        exact context.memory_wf
      have hreadsBody : Mem.Reads bodyPre.memory [] := by
        rw [hmemoryEntry]
        exact context.memory_reads_empty
      obtain ⟨recipient, sc, gasWord, inputSize, base,
          hbase, hrecipient, htoken, hamount, htotal, hincrease,
          hcounterSc, hcodeSc, hbalSc, hinputSize, hstack, hmemory,
          hmintLogs, hsetupOutput, htail⟩ :=
        of_flashLoan_toCall_frame dp hbody
      have hinputSize' : inputSize = flashCallbackRuntimeSize e := by
        simpa only [flashCallbackRuntimeSize] using hinputSize
      have hstack' := hstack
      rw [hinputSize'] at hstack'
      obtain ⟨hwfSc, hreadsSc⟩ := hmemory [] hwfBody hreadsBody
      have hreadsRuntime :
          Mem.Reads sc.memory (flashCallbackRuntimeImage e []) := by
        simpa only [flashCallbackRuntimeImage] using hreadsSc
      have htail' : Func.Run ((weth10 dp).main :: weth10Aux) e sc
          flashLoanSuccessTail post := by
        simpa only [flashLoanSuccessTail, flashLoanFromCall] using htail
      obtain ⟨mid, settle, hcallback, hstorMid, hbalMid, hcodeMid,
          hsettleLogs, hsettleOutput, hwfSettle, hreadsSettleEx,
          hsettle⟩ :=
        of_rawFlashLoanSuccessTail_step dp hstack' hwfSc hreadsRuntime
          (by rfl) htail'
      obtain ⟨settleImg, hreadsSettle⟩ := hreadsSettleEx
      obtain ⟨burn, hburn, hallowance, hwfBurn, burnImg,
          hreadsBurn⟩ :=
        of_flashSettle_allowance dp hwfSettle hreadsSettle hsettle
      obtain ⟨hdecrease, hcover, hflashBurn, hburnLogs, htrue,
          hbalBurn, hcodeBurn⟩ :=
        flashBurn_effect dp hwfBurn hreadsBurn hburn
      have htarget : e.currentTarget = ca := context.invocation.2.1
      have hrecipient' : recipient = (Sevm.argWord e 0).toAdr := by
        apply Adr.toB256_inj
        rw [hrecipient]
        exact normalizedAddressArg_eq_toAdr_toB256 e 0
      subst recipient
      have hreceiverNorm : (normalizedAddressArg e 0).toAdr =
          (Sevm.argWord e 0).toAdr := by
        rw [normalizedAddressArg_eq_toAdr_toB256, toAdr_toB256]
      rw [htarget] at hincrease
      rw [congrFun hstorEntry ca] at hincrease
      rw [htarget, hreceiverNorm] at hdecrease hcover
      have hsilentAllowance := flashAllowanceOutcome_weth10Silent hallowance
      rw [htarget] at hsilentAllowance
      have hatom : primaryFlowAtom e = some
          (.flashPair (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            (Sevm.argWord e 2).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          flashLoanSelector_ne_depositSelector,
          flashLoanSelector_ne_depositToSelector,
          flashLoanSelector_ne_depositToAndCallSelector,
          flashLoanSelector_ne_transferSelector,
          flashLoanSelector_ne_transferAndCallSelector,
          flashLoanSelector_ne_transferFromSelector,
          flashLoanSelector_ne_withdrawSelector,
          flashLoanSelector_ne_withdrawToSelector,
          flashLoanSelector_ne_withdrawFromSelector]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      have hsegments := localSegments_flashPair
        (action :=
          { atom := .flashPair (Sevm.argWord e 0)
              (Sevm.argWord e 0).toAdr (Sevm.argWord e 2).toNat
            credit :=
              (FlowAtom.flashPair (Sevm.argWord e 0)
                (Sevm.argWord e 0).toAdr
                (Sevm.argWord e 2).toNat).creditOccurrence pre ca
            debit := primaryDebitProvenance e pre post
            actualCaller := e.caller
            currentTarget := e.currentTarget
            codeAddress := e.codeAddress
            depth := e.depth })
        (pre := Stor.rest (Devm.getStor pre ca))
        (minted := Stor.rest (Devm.getStor sc ca))
        (settle := Stor.rest (Devm.getStor burn ca))
        (post := Stor.rest (Devm.getStor post ca))
        (rawReceiver := Sevm.argWord e 0)
        (receiver := (Sevm.argWord e 0).toAdr)
        (amountWord := Sevm.argWord e 2)
        (by rfl)
        (by
          unfold FlowAction.ExactCredit
          simp only [FlowAtom.creditOccurrence]
          rw [toB256_toNat])
        (by
          unfold FlowAction.HasFlashDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector,
            flashLoanSelector_ne_transferSelector,
            flashLoanSelector_ne_transferAndCallSelector,
            flashLoanSelector_ne_transferFromSelector,
            flashLoanSelector_ne_withdrawSelector,
            flashLoanSelector_ne_withdrawToSelector,
            flashLoanSelector_ne_withdrawFromSelector])
        hincrease hcover hdecrease
      refine ⟨context, haction, ?_⟩
      apply RichLocalStorageEffect.flash sc mid settle burn
        (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
        (Sevm.argWord e 2)
      · exact hsegments.1
      · exact (congrFun hcodeSc ca).symm.trans (congrFun hcodeEntry ca)
      · exact hcallback
      · exact hstorMid
      · exact hsettle
      · exact hsilentAllowance
      · exact hsegments.2
      · exact hburn

/-- Exhaustive operational classifier for every retained WETH10 frame whose
primary flow action is defined.  In addition to the frame's exact own balance
segment, callback-bearing constructors retain the concrete CALL instruction
slot and child execution supplied by the compiled program proof. -/
theorem Exec.Frame.hasRichLocalStorageEffect_of_flowAction?_eq_some
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action := by
  by_cases hempty : frame.sevm.data.length.toB256 = 0
  · exact Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_receive (frame := frame) context hempty haction
  have hnonempty : frame.sevm.data.length.toB256 ≠ 0 := hempty
  by_cases hdeposit : Sevm.selector frame.sevm = depositSelector
  · exact Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_deposit (frame := frame) context hdeposit
      hnonempty haction
  by_cases hdepositTo : Sevm.selector frame.sevm = depositToSelector
  · exact Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_depositTo (frame := frame) context hdepositTo
      hnonempty haction
  by_cases hdepositCall :
      Sevm.selector frame.sevm = depositToAndCallSelector
  · exact Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_depositToAndCall (frame := frame) context
      hdepositCall hnonempty haction
  by_cases htransfer : Sevm.selector frame.sevm = transferSelector
  · exact Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_transfer (frame := frame) context htransfer
      hnonempty haction
  by_cases htransferCall :
      Sevm.selector frame.sevm = transferAndCallSelector
  · exact Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_transferAndCall (frame := frame) context
      htransferCall hnonempty haction
  by_cases htransferFrom :
      Sevm.selector frame.sevm = transferFromSelector
  · exact Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_transferFrom (frame := frame) context
      htransferFrom hnonempty haction
  by_cases hwithdraw : Sevm.selector frame.sevm = withdrawSelector
  · exact Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_withdraw (frame := frame) context hwithdraw
      hnonempty haction
  by_cases hwithdrawTo : Sevm.selector frame.sevm = withdrawToSelector
  · exact Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_withdrawTo (frame := frame) context hwithdrawTo
      hnonempty haction
  by_cases hwithdrawFrom :
      Sevm.selector frame.sevm = withdrawFromSelector
  · exact Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_withdrawFrom (frame := frame) context
      hwithdrawFrom hnonempty haction
  by_cases hflash : Sevm.selector frame.sevm = flashLoanSelector
  · exact Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_flashLoan (frame := frame) context hflash
      hnonempty haction
  have hprimary : primaryFlowAtom frame.sevm = none := by
    simp [primaryFlowAtom, hnonempty, hdeposit, hdepositTo,
      hdepositCall, htransfer, htransferCall, htransferFrom, hwithdraw,
      hwithdrawTo, hwithdrawFrom, hflash]
  simp [Blanc.Weth10.Exec.Frame.flowAction?, context.invocation, hprimary] at haction

/-- Exhaustive compiled-program classifier for receive plus all 27 selector
leaves.  Nonempty successful calldata is first proved to have entered an
actual listed dispatch leaf; therefore the non-flow arm is not conditional on
an externally supplied recognition assumption. -/
theorem Exec.Frame.hasCompiledBalanceOwnEffect
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame) :
    Blanc.Weth10.Exec.Frame.HasCompiledBalanceOwnEffect dp ca frame := by
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | some action =>
      exact .flow action
        (Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_flowAction?_eq_some (frame := frame)
          context haction)
  | none =>
      by_cases hempty : frame.sevm.data.length.toB256 = 0
      · have hprimary : primaryFlowAtom frame.sevm ≠ none := by
          simp [primaryFlowAtom, hempty]
        unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation] at haction
        cases hatom : primaryFlowAtom frame.sevm with
        | none => exact (hprimary hatom).elim
        | some atom => simp [hatom] at haction
      · exact .noFlow
          (Blanc.Weth10.Exec.Frame.hasNoWethBalanceOwnEffect_of_recognized (frame := frame) context haction
            (Blanc.Weth10.Exec.Frame.recognizedSelector_of_nonempty (frame := frame) context hempty))

/-- Identifier-safe alias for tooling that cannot parse `?` in declaration
names. -/
theorem Exec.Frame.hasRichLocalStorageEffect_of_classified
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action :=
  Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_flowAction?_eq_some (frame := frame) context haction

/-- A classified authentic frame contributes its own action first, followed
by exactly the labels computed from the original proof-indexed proper
descendant traversal. -/
theorem Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.ClassifiedActionLedger dp ca frame action := by
  refine ⟨Blanc.Weth10.Exec.Frame.hasRichLocalStorageEffect_of_classified (frame := frame) context haction, ?_⟩
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  have hroot : Blanc.Weth10.Exec.Frame.flowAction? dp ca
      (Exec.Frame.ofRun run committed) = some action := by
    exact haction
  simp [Exec.flowActions, Exec.committedFrames,
    Blanc.Weth10.Exec.Frame.descendantFlowActions, committed, hroot]

/-- Every executable flow classification of an authentic committed WETH10
frame is backed by the exact local balance segment executed by that frame.
Callback and ETH-send children are excluded from the existential endpoint;
their effects remain available through the raw functional boundaries used by
the selector-specific proofs above. -/
theorem Exec.Frame.hasLocalOwnEffect_of_flowAction?_eq_some
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasLocalOwnEffect ca frame action := by
  by_cases hempty : frame.sevm.data.length.toB256 = 0
  · exact Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_receive (frame := frame) context hempty haction
  have hnonempty : frame.sevm.data.length.toB256 ≠ 0 := hempty
  by_cases hdeposit : Sevm.selector frame.sevm = depositSelector
  · exact Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_deposit (frame := frame) context hdeposit hnonempty
      haction
  by_cases hdepositTo : Sevm.selector frame.sevm = depositToSelector
  · exact Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_depositTo (frame := frame) context hdepositTo
      hnonempty haction
  by_cases hdepositCall :
      Sevm.selector frame.sevm = depositToAndCallSelector
  · exact Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_depositToAndCall (frame := frame) context hdepositCall
      hnonempty haction
  by_cases htransfer : Sevm.selector frame.sevm = transferSelector
  · exact Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_transfer (frame := frame) context htransfer hnonempty
      haction
  by_cases htransferCall :
      Sevm.selector frame.sevm = transferAndCallSelector
  · exact Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_transferAndCall (frame := frame) context htransferCall
      hnonempty haction
  by_cases htransferFrom :
      Sevm.selector frame.sevm = transferFromSelector
  · exact Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_transferFrom (frame := frame) context htransferFrom
      hnonempty haction
  by_cases hwithdraw : Sevm.selector frame.sevm = withdrawSelector
  · exact Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_withdraw (frame := frame) context hwithdraw hnonempty
      haction
  by_cases hwithdrawTo : Sevm.selector frame.sevm = withdrawToSelector
  · exact Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_withdrawTo (frame := frame) context hwithdrawTo
      hnonempty haction
  by_cases hwithdrawFrom :
      Sevm.selector frame.sevm = withdrawFromSelector
  · exact Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_withdrawFrom (frame := frame) context hwithdrawFrom
      hnonempty haction
  by_cases hflash : Sevm.selector frame.sevm = flashLoanSelector
  · exact Blanc.Weth10.Exec.Frame.hasLocalOwnEffect_of_flashLoan (frame := frame) context hflash hnonempty
      haction
  have hprimary : primaryFlowAtom frame.sevm = none := by
    simp [primaryFlowAtom, hnonempty, hdeposit, hdepositTo,
      hdepositCall, htransfer, htransferCall, htransferFrom, hwithdraw,
      hwithdrawTo, hwithdrawFrom, hflash]
  simp [Blanc.Weth10.Exec.Frame.flowAction?, context.invocation, hprimary] at haction

/-! ## Literal generated-program SSTORE inventory

`sourceSstoreSiteCount` counts `SSTORE` nodes in the `Func` syntax that the
compiler emits.  Calls are counted at their single auxiliary definition rather
than again at each jump site.  Branches count both emitted arms.  Consequently
the program total below is a literal inventory of the generated runtime, not a
statement merely about successful endpoints.

In the 27-entry leaf vector (the order of `weth10Funcs`), the nonzero entries
are: approve 1; withdrawTo 1; transferFrom wrapper 1; withdraw 1;
transferAndCall 3; flashLoan 2; depositToAndCall 1; withdrawFrom wrapper 1;
transfer 3; depositTo 1; approveAndCall 1; deposit 1; permit 1.  Receive adds
one.  In `weth10Aux`, flashSettle contributes 1, transferFromCore 3,
withdrawFromCore 1, flashBurn 2, and permitRecover 1.

The key regions represented by those 27 emitted sites are exactly 18 balance
sites, 6 allowance-tag sites, 1 nonce-tag site, and 2 flash-minted sites.  The
semantic functional theorems used above establish the key class of each named
group; what is still not encoded here is an occurrence relation connecting an
arbitrary `SSTORE` step in a proof-indexed `Exec` back to its syntax node. -/

def sourceSstoreSiteCount : Func → Nat
  | .last _ => 0
  | .next (.reg .sstore) rest => 1 + sourceSstoreSiteCount rest
  | .next _ rest => sourceSstoreSiteCount rest
  | .branch left right =>
      sourceSstoreSiteCount left + sourceSstoreSiteCount right
  | .call _ => 0

def progSourceSstoreSiteCount (program : Prog) : Nat :=
  sourceSstoreSiteCount program.main +
    (program.aux.map sourceSstoreSiteCount).sum

private def ninstSourceSstoreSiteCount : Ninst → Nat
  | .reg .sstore => 1
  | _ => 0

private theorem sourceSstoreSiteCount_next (n : Ninst) (rest : Func) :
    sourceSstoreSiteCount (.next n rest) =
      ninstSourceSstoreSiteCount n + sourceSstoreSiteCount rest := by
  cases n with
  | reg r => cases r <;>
      simp [sourceSstoreSiteCount, ninstSourceSstoreSiteCount]
  | exec x => simp [sourceSstoreSiteCount, ninstSourceSstoreSiteCount]
  | push bs h => simp [sourceSstoreSiteCount, ninstSourceSstoreSiteCount]

private def lineSourceSstoreSiteCount (line : Line) : Nat :=
  (line.map ninstSourceSstoreSiteCount).sum

private theorem sourceSstoreSiteCount_prepend (line : Line) (rest : Func) :
    sourceSstoreSiteCount (line +++ rest) =
      lineSourceSstoreSiteCount line + sourceSstoreSiteCount rest := by
  induction line with
  | nil => simp [prepend, lineSourceSstoreSiteCount]
  | cons n line ih =>
      simp [prepend, sourceSstoreSiteCount_next,
        lineSourceSstoreSiteCount, ih, Nat.add_assoc]

private def dispatchTreeSourceSstoreSiteCount : DispatchTree → Nat
  | .leaf _ body => sourceSstoreSiteCount body
  | .fork left right =>
      dispatchTreeSourceSstoreSiteCount left +
        dispatchTreeSourceSstoreSiteCount right

private theorem dispatchWith_sourceSstoreSiteCount
    (k : Nat) (tree : DispatchTree) :
    sourceSstoreSiteCount (dispatchWith k tree) =
      dispatchTreeSourceSstoreSiteCount tree := by
  induction tree with
  | leaf selector body =>
      simp only [dispatchWith, sourceSstoreSiteCount_next,
        Ninst.pushB256, ninstSourceSstoreSiteCount, sourceSstoreSiteCount,
        dispatchTreeSourceSstoreSiteCount]
      omega
  | fork left right ihLeft ihRight =>
      simp only [dispatchWith, sourceSstoreSiteCount_next,
        Ninst.pushB256, ninstSourceSstoreSiteCount, sourceSstoreSiteCount,
        dispatchTreeSourceSstoreSiteCount, ihLeft, ihRight]
      omega

private theorem dispatchTreeSourceSstoreSiteCount_build :
    ∀ (n : Nat) (entries : List (B256 × Func)),
      entries ≠ [] → entries.length ≤ n + 1 →
      dispatchTreeSourceSstoreSiteCount (DispatchTree.build n entries) =
        (entries.map fun entry => sourceSstoreSiteCount entry.2).sum := by
  intro n
  induction n with
  | zero =>
      intro entries hne hlen
      rcases entries with _ | ⟨head, tail⟩
      · exact absurd rfl hne
      · rcases tail with _ | ⟨second, rest⟩
        · rfl
        · simp only [List.length_cons] at hlen
          omega
  | succ n ih =>
      intro entries hne hlen
      rcases entries with _ | ⟨head, tail⟩
      · exact absurd rfl hne
      · rcases tail with _ | ⟨second, rest⟩
        · rfl
        · let entries := head :: second :: rest
          let split := (entries.length + 1) / 2
          simp only [List.length_cons] at hlen
          have htakeLen : (entries.take split).length ≤ n + 1 := by
            simp only [List.length_take, entries, split, List.length_cons]
            omega
          have hdropLen : (entries.drop split).length ≤ n + 1 := by
            simp only [List.length_drop, entries, split, List.length_cons]
            omega
          have htakeNe : entries.take split ≠ [] := by
            intro h
            have hl := congrArg List.length h
            simp only [List.length_take, entries, split, List.length_cons,
              List.length_nil] at hl
            omega
          have hdropNe : entries.drop split ≠ [] := by
            intro h
            have hl := congrArg List.length h
            simp only [List.length_drop, entries, split, List.length_cons,
              List.length_nil] at hl
            omega
          simp only [DispatchTree.build,
            dispatchTreeSourceSstoreSiteCount]
          rw [ih _ htakeNe htakeLen, ih _ hdropNe hdropLen]
          rw [← List.sum_append, ← List.map_append,
            List.take_append_drop]

private theorem weth10Tree_sourceSstoreSiteCount (dp : DeployParams) :
    dispatchTreeSourceSstoreSiteCount (weth10Tree dp) =
      ((weth10Funcs dp).map
        (fun entry => sourceSstoreSiteCount entry.2)).sum := by
  unfold weth10Tree DispatchTree.ofSorted
  apply dispatchTreeSourceSstoreSiteCount_build
  · simp [weth10Funcs]
  · omega

/-! Named leaf facts keep the literal inventory local to each generated body.
The vector proofs below only rewrite an explicit list shape and compose these
facts; they never ask the kernel to normalize the closed dispatcher program. -/

private theorem name_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable name) = 0 := by rfl
private theorem approve_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable approve) = 1 := by rfl
private theorem totalSupply_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable totalSupply) = 0 := by rfl
private theorem withdrawTo_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable withdrawTo) = 1 := by rfl
private theorem transferFrom_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable transferFrom) = 1 := by rfl
private theorem withdraw_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable withdraw) = 1 := by rfl
private theorem permitTypehash_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable permitTypehash) = 0 := by rfl
private theorem decimals_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable decimals) = 0 := by rfl
private theorem domainSeparator_public_sourceSstoreSiteCount
    (dp : DeployParams) :
    sourceSstoreSiteCount (nonpayable (domainSeparator dp)) = 0 := by rfl
private theorem transferAndCall_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable transferAndCall) = 3 := by rfl
private theorem flashLoan_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable flashLoan) = 2 := by rfl
private theorem depositToAndCall_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount depositToAndCall = 1 := by rfl
private theorem maxFlashLoan_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable maxFlashLoan) = 0 := by rfl
private theorem balanceOf_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable balanceOfEndpoint) = 0 := by rfl
private theorem nonces_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable nonces) = 0 := by rfl
private theorem callbackSuccess_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable callbackSuccess) = 0 := by rfl
private theorem flashMinted_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable flashMinted) = 0 := by rfl
private theorem withdrawFrom_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable withdrawFrom) = 1 := by rfl
private theorem symbol_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable symbol) = 0 := by rfl
private theorem transfer_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable transfer) = 3 := by rfl
private theorem depositTo_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount depositTo = 1 := by rfl
private theorem approveAndCall_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable approveAndCall) = 1 := by rfl
private theorem deploymentChainId_public_sourceSstoreSiteCount
    (dp : DeployParams) :
    sourceSstoreSiteCount (nonpayable (deploymentChainId dp)) = 0 := by rfl
private theorem deposit_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount deposit = 1 := by rfl
private theorem permit_public_sourceSstoreSiteCount (dp : DeployParams) :
    sourceSstoreSiteCount (nonpayable (permit dp)) = 1 := by rfl
private theorem flashFee_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable flashFee) = 0 := by rfl
private theorem allowance_public_sourceSstoreSiteCount :
    sourceSstoreSiteCount (nonpayable allowance) = 0 := by rfl

private theorem prependStore_sourceSstoreSiteCount
    (w : B256) (i : Nat) (rest : Func) :
    sourceSstoreSiteCount (prependStore w i rest) =
      sourceSstoreSiteCount rest := by
  rfl

private theorem prependStoresRev_sourceSstoreSiteCount
    (stores : List (B256 × Nat)) (rest : Func) :
    sourceSstoreSiteCount (prependStoresRev stores rest) =
      sourceSstoreSiteCount rest := by
  induction stores generalizing rest with
  | nil => rfl
  | cons iw stores ih =>
      rw [show prependStoresRev (iw :: stores) rest =
        prependStoresRev stores (prependStore iw.1 iw.2 rest) from rfl,
        ih, prependStore_sourceSstoreSiteCount]

private theorem revWith_sourceSstoreSiteCount (reason : String) :
    sourceSstoreSiteCount (Func.revWith reason) = 0 := by
  unfold Func.revWith Func.revData
  rw [prependStoresRev_sourceSstoreSiteCount]
  rfl

private theorem rev_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount Func.rev = 0 := by rfl
private theorem flashTokenError_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount flashTokenError = 0 := by
  exact revWith_sourceSstoreSiteCount _
private theorem individualLimitError_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount individualLimitError = 0 := by
  exact revWith_sourceSstoreSiteCount _
private theorem totalLimitError_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount totalLimitError = 0 := by
  exact revWith_sourceSstoreSiteCount _
private theorem flashFailedError_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount flashFailedError = 0 := by
  exact revWith_sourceSstoreSiteCount _
private theorem allowanceError_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount allowanceError = 0 := by
  exact revWith_sourceSstoreSiteCount _
private theorem burnBalanceError_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount burnBalanceError = 0 := by
  exact revWith_sourceSstoreSiteCount _
private theorem expiredPermitError_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount expiredPermitError = 0 := by
  exact revWith_sourceSstoreSiteCount _
private theorem invalidPermitError_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount invalidPermitError = 0 := by
  exact revWith_sourceSstoreSiteCount _
private theorem transferBalanceError_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount transferBalanceError = 0 := by
  exact revWith_sourceSstoreSiteCount _
private theorem ethTransferError_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount ethTransferError = 0 := by
  exact revWith_sourceSstoreSiteCount _
private theorem etherTransferError_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount etherTransferError = 0 := by
  exact revWith_sourceSstoreSiteCount _
private theorem bubbleRevert_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount bubbleRevert = 0 := by rfl
private theorem boolReturn_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount boolReturn = 0 := by rfl
private theorem flashSettle_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount flashSettle = 1 := by rfl
private theorem transferFromCore_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount transferFromCore = 3 := by rfl
private theorem withdrawFromCore_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount withdrawFromCore = 1 := by rfl
private theorem flashBurn_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount flashBurn = 2 := by rfl
private theorem permitRecover_aux_sourceSstoreSiteCount :
    sourceSstoreSiteCount permitRecover = 1 := by rfl

/-- Literal SSTORE-node counts for the 27 public bodies, in the exact order of
`weth10Funcs`.  Shared called continuations are inventoried separately below. -/
theorem weth10Funcs_sourceSstoreSiteCounts (dp : DeployParams) :
    (weth10Funcs dp).map (fun entry => sourceSstoreSiteCount entry.2) =
      [0, 1, 0, 1, 1, 1, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 0, 1,
        0, 3, 1, 1, 0, 1, 1, 0, 0] := by
  rw [weth10Funcs_shape]
  simp only [List.map_cons, List.map_nil,
    name_public_sourceSstoreSiteCount,
    approve_public_sourceSstoreSiteCount,
    totalSupply_public_sourceSstoreSiteCount,
    withdrawTo_public_sourceSstoreSiteCount,
    transferFrom_public_sourceSstoreSiteCount,
    withdraw_public_sourceSstoreSiteCount,
    permitTypehash_public_sourceSstoreSiteCount,
    decimals_public_sourceSstoreSiteCount,
    domainSeparator_public_sourceSstoreSiteCount,
    transferAndCall_public_sourceSstoreSiteCount,
    flashLoan_public_sourceSstoreSiteCount,
    depositToAndCall_public_sourceSstoreSiteCount,
    maxFlashLoan_public_sourceSstoreSiteCount,
    balanceOf_public_sourceSstoreSiteCount,
    nonces_public_sourceSstoreSiteCount,
    callbackSuccess_public_sourceSstoreSiteCount,
    flashMinted_public_sourceSstoreSiteCount,
    withdrawFrom_public_sourceSstoreSiteCount,
    symbol_public_sourceSstoreSiteCount,
    transfer_public_sourceSstoreSiteCount,
    depositTo_public_sourceSstoreSiteCount,
    approveAndCall_public_sourceSstoreSiteCount,
    deploymentChainId_public_sourceSstoreSiteCount,
    deposit_public_sourceSstoreSiteCount,
    permit_public_sourceSstoreSiteCount,
    flashFee_public_sourceSstoreSiteCount,
    allowance_public_sourceSstoreSiteCount]

/-- Literal SSTORE-node counts for all 19 auxiliary bodies, in `weth10Aux`
order. -/
theorem weth10Aux_sourceSstoreSiteCounts :
    weth10Aux.map sourceSstoreSiteCount =
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 2, 1] := by
  rw [weth10Aux_shape]
  simp only [List.map_cons, List.map_nil,
    rev_aux_sourceSstoreSiteCount,
    flashTokenError_aux_sourceSstoreSiteCount,
    individualLimitError_aux_sourceSstoreSiteCount,
    totalLimitError_aux_sourceSstoreSiteCount,
    flashFailedError_aux_sourceSstoreSiteCount,
    allowanceError_aux_sourceSstoreSiteCount,
    burnBalanceError_aux_sourceSstoreSiteCount,
    expiredPermitError_aux_sourceSstoreSiteCount,
    invalidPermitError_aux_sourceSstoreSiteCount,
    transferBalanceError_aux_sourceSstoreSiteCount,
    ethTransferError_aux_sourceSstoreSiteCount,
    etherTransferError_aux_sourceSstoreSiteCount,
    bubbleRevert_aux_sourceSstoreSiteCount,
    boolReturn_aux_sourceSstoreSiteCount,
    flashSettle_aux_sourceSstoreSiteCount,
    transferFromCore_aux_sourceSstoreSiteCount,
    withdrawFromCore_aux_sourceSstoreSiteCount,
    flashBurn_aux_sourceSstoreSiteCount,
    permitRecover_aux_sourceSstoreSiteCount]

theorem receiveEther_sourceSstoreSiteCount :
    sourceSstoreSiteCount receiveEther = 1 := by
  decide +kernel

private theorem weth10Main_sourceSstoreSiteCount (dp : DeployParams) :
    sourceSstoreSiteCount (weth10Main dp) = 19 := by
  rw [weth10Main_shape, sourceSstoreSiteCount_prepend]
  have hentry : lineSourceSstoreSiteCount
      [Ninst.calldatasize, Ninst.iszero] = 0 := by rfl
  rw [hentry]
  simp only [sourceSstoreSiteCount, Nat.zero_add,
    sourceSstoreSiteCount_prepend, dispatchWith_sourceSstoreSiteCount,
    weth10Tree_sourceSstoreSiteCount, weth10Funcs_sourceSstoreSiteCounts,
    receiveEther_sourceSstoreSiteCount]
  decide

/-- Literal total number of source `SSTORE` nodes in the generated WETH10
runtime: the dispatched main body and every auxiliary body, with shared
auxiliaries counted once. -/
theorem weth10_sourceSstoreSiteCount (dp : DeployParams) :
    progSourceSstoreSiteCount (weth10 dp) = 27 := by
  unfold progSourceSstoreSiteCount weth10
  rw [weth10Main_sourceSstoreSiteCount,
    weth10Aux_sourceSstoreSiteCounts]
  decide +kernel

end Weth10

end Blanc
