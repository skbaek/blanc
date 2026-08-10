import Blanc.ExecDeterminism
import Blanc.Weth10HolderFlowAuthenticity
import Blanc.Weth10HolderFlowEth
import Blanc.Weth10HolderFlowLocal
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
  authentic : frame.AuthenticContext dp ca
  classified : frame.flowAction? dp ca = some action
  effect : RichLocalStorageEffect dp ca frame.sevm frame.pre frame.post action

/-- Proper-descendant labels of one retained frame, excluding its own
classification.  This is kept frame-indexed so later callback occurrence
witnesses can identify the exact child derivations contributing each suffix. -/
def Exec.Frame.descendantFlowActions (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) : List FlowAction :=
  (Exec.descendantFrames frame.run).filterMap
    (Exec.Frame.flowAction? dp ca)

/-- Proper-descendant labels for an arbitrary proof-indexed execution. -/
def Exec.Deriv.descendantFlowActions (dp : DeployParams) (ca : Adr)
    (deriv : Exec.Deriv) : List FlowAction :=
  (Exec.descendantFrames deriv.exc).filterMap
    (Exec.Frame.flowAction? dp ca)

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
        (if Blanc.Weth10.Frame.settlementCommits f raw = true then
          Exec.flowActions dp ca child
         else [])

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
          Blanc.Weth10.Frame.raw_commits_of_settlementCommits hcommit
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
  rich : frame.HasRichLocalStorageEffect dp ca action
  actions_eq : Exec.flowActions dp ca frame.run =
    action :: frame.descendantFlowActions dp ca

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

/-- An instruction occurrence exposes the exact chronological split of the
enclosing frame's proper-descendant ledger: all earlier settled children,
the selected instruction's settled child (or `[]`), then the continuation. -/
theorem Exec.Frame.NinstOccurrence.chronological_descendantFlowActions
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {n : Ninst} {stepPre stepPost : Devm} {xl : Xlot}
    (occurrence : frame.NinstOccurrence dp ca n stepPre stepPost xl) :
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
      frame.descendantFlowActions dp ca =
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
    (ledger : frame.ClassifiedActionLedger dp ca action)
    {before selected suffix : List FlowAction}
    (hdesc : frame.descendantFlowActions dp ca =
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
      frame.NinstOccurrence dp ca n stepPre stepPost xl := by
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
private theorem Ninst.StepRun.unique_exec_of_filled
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
      frame.NinstOccurrence dp ca n stepPre stepPost xl ∧
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
            if Blanc.Weth10.Frame.settlementCommits f raw = true then
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
private theorem ninstAt_of_subcode_next
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
          rcases frame.advance_runCompiled_next current hprefix hat
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
      rcases frame.advance_cont current hprefix hstepPush with
        ⟨afterPush, hpPush⟩
      rcases frame.advance_cont afterPush hpPush hstepJumpi with
        ⟨armExec, hpArm⟩
      exact Or.inl ⟨pc + 4, _, armExec, hpArm, hleft,
        hsubLeft, hboundLeft⟩
  | succ hne hroom hpop hright =>
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases frame.advance_cont current hprefix hstepPush with
        ⟨afterPush, hpPush⟩
      rcases frame.advance_cont afterPush hpPush hstepJumpi with
        ⟨afterJump, hpJump⟩
      rcases frame.advance_cont afterJump hpJump hstepJumpdest with
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

/-- Peel a source line at a proof-indexed compiled cursor. -/
theorem Exec.Frame.CompiledCursor.peelLine
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {line : Line} {tail : Func} {final : Devm}
    (cursor : frame.CompiledCursor dp ca fs table (line +++ tail) final) :
    ∃ tailCursor : frame.CompiledCursor dp ca fs table tail final,
      Line.Run frame.sevm cursor.pre line tailCursor.pre := by
  rcases frame.advance_runCompiled_prepend cursor.current cursor.parentPrefix
      cursor.run cursor.codeSlice cursor.codeBoundary with
    ⟨tailPc, tailPre, tailExec, crossed, htailPrefix, hline,
      htailRun, htailSub, htailBoundary⟩
  let tailCursor : frame.CompiledCursor dp ca fs table tail final :=
    ⟨tailPc, tailPre, tailExec, cursor.actions ++ crossed, htailPrefix,
      htailRun, htailSub, htailBoundary⟩
  exact ⟨tailCursor, hline⟩

/-- Select the actual branch arm at a proof-indexed compiled cursor. -/
theorem Exec.Frame.CompiledCursor.selectBranch
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : frame.CompiledCursor dp ca fs table
      (.branch left right) final) :
    Nonempty (frame.CompiledCursor dp ca fs table left final) ∨
      Nonempty (frame.CompiledCursor dp ca fs table right final) := by
  rcases frame.advance_runCompiled_branch cursor.current cursor.parentPrefix
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
    (cursor : frame.CompiledCursor dp ca fs table
      (.branch left right) final) :
    (∃ arm : frame.CompiledCursor dp ca fs table left final,
      arm.actions = cursor.actions) ∨
    (∃ arm : frame.CompiledCursor dp ca fs table right final,
      arm.actions = cursor.actions) := by
  rcases frame.advance_runCompiled_branch cursor.current cursor.parentPrefix
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
    (cursor : frame.CompiledCursor dp ca fs table
      (.branch left right) final)
    (hnoRight : ∀ pre, ¬ Func.Run fs frame.sevm pre right final) :
    ∃ arm : frame.CompiledCursor dp ca fs table left final,
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
      rcases frame.advance_cont cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hpPush⟩
      rcases frame.advance_cont afterPush hpPush hstepJumpi with
        ⟨armExec, hpArm⟩
      let arm : frame.CompiledCursor dp ca fs table left final :=
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
    (cursor : frame.CompiledCursor dp ca fs table
      (.branch left right) final)
    (hstack : (0 : B256) :: stack <<+ cursor.pre.stack) :
    ∃ arm : frame.CompiledCursor dp ca fs table left final,
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
      rcases frame.advance_cont cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hpPush⟩
      rcases frame.advance_cont afterPush hpPush hstepJumpi with
        ⟨armExec, hpArm⟩
      let arm : frame.CompiledCursor dp ca fs table left final :=
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
    (cursor : frame.CompiledCursor dp ca fs table
      (.branch left right) final)
    (hflag : flag ≠ 0)
    (hstack : flag :: stack <<+ cursor.pre.stack) :
    ∃ arm : frame.CompiledCursor dp ca fs table right final,
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
      rcases frame.advance_cont cursor.current cursor.parentPrefix
          hstepPush with ⟨afterPush, hpPush⟩
      rcases frame.advance_cont afterPush hpPush hstepJumpi with
        ⟨afterJump, hpJump⟩
      rcases frame.advance_cont afterJump hpJump hstepJumpdest with
        ⟨armExec, hpArm⟩
      let arm : frame.CompiledCursor dp ca fs table right final :=
        ⟨loc + 1, _, armExec, cursor.actions, hpArm,
          hright, hsubRight, hboundRight⟩
      exact ⟨arm, hw.2, rfl⟩

/-- Select the head instruction of a cursor and retain both its exact
occurrence and the proof-indexed cursor immediately after it. -/
theorem Exec.Frame.CompiledCursor.selectNext
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {n : Ninst} {tail : Func} {final : Devm}
    (cursor : frame.CompiledCursor dp ca fs table (.next n tail) final) :
    ∃ stepPre stepPost xl,
      frame.NinstOccurrence dp ca n stepPre stepPost xl ∧
      Nonempty (frame.CompiledCursor dp ca fs table tail final) := by
  have compiled := cursor.run
  cases compiled with
  | next hcompiled htail =>
      have hat : Ninst.At frame.sevm.code cursor.pc n :=
        ninstAt_of_subcode_next cursor.codeSlice
      rcases frame.advance_runCompiled_next cursor.current
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
    (cursor : frame.CompiledCursor dp ca fs table (.next n tail) final) :
    ∃ (tailCursor : frame.CompiledCursor dp ca fs table tail final)
        (xl : Xlot) (selected : List FlowAction),
      frame.NinstOccurrence dp ca n cursor.pre tailCursor.pre xl ∧
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
      rcases frame.advance_runCompiled_next cursor.current
          cursor.parentPrefix hat hcompiled with
        ⟨xl, continuation, selected, occurrence, hedge, hnextPrefix⟩
      obtain ⟨nextBoundary, nextSub⟩ :=
        Func.noPushBefore_next cursor.codeSlice cursor.codeBoundary
      let tailCursor : frame.CompiledCursor dp ca fs table tail final :=
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
    (cursor : frame.CompiledCursor dp ca fs table
      (.next (.exec x) tail) final)
    (rawFilled : rawSlot.Filled)
    (rawStep : Ninst.StepRun rawPc frame.sevm cursor.pre
      (.exec x) rawSlot (.ok rawPost)) :
    ∃ (tailCursor : frame.CompiledCursor dp ca fs table tail final)
        (selected : List FlowAction),
      tailCursor.pre = rawPost ∧
      frame.NinstOccurrence dp ca (.exec x)
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

/-- A clean retained `ProcessMessage` child survives the full settlement of
its ordinary CALL frame.  This is the exact settlement fact needed to turn a
selected parent CALL edge into the retained child's action list. -/
theorem ProcessMessage.settlementCommits_of_some_ok_clean
    {msg : Msg} {pc : Nat} {sevm : Sevm} {pre child : Devm}
    {raw : Execution}
    (hprocess : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, raw⟩) (.ok child))
    (hclean : child.error.isSome = false) :
    Frame.settlementCommits (Frame.ofCall msg) raw = true := by
  have hsettle := (RunFrame.some_inv hprocess).2
  have hclean' : child.error.isNone = true := by
    cases herror : child.error <;> simp_all
  unfold Frame.settlementCommits
  rw [← hsettle]
  exact hclean'

private theorem genericCall_step_spawn_exact_compiled
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isStatic : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume}
    (hspawn : genericCall.step sevm devm gas value caller target codeAddress
      stv isStatic ii isz oi osz code disablePrecompiles =
        .spawn frame resume) :
    frame = Frame.ofCall
      (callMsg sevm (devm.withReturnData []) gas value caller target
        codeAddress stv isStatic ((devm.memory.read ii isz).1) code
        disablePrecompiles) ∧
    resume = .call (devm.withReturnData []) oi osz := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hspawn
  repeat' split at hspawn
  all_goals
    simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hspawn
  all_goals obtain ⟨rfl, rfl⟩ := hspawn
  all_goals exact ⟨rfl, rfl⟩

private theorem Xinst.step_call_spawn_ofCall
    {sevm : Sevm} {devm : Devm} {frame : Frame} {resume : Resume}
    (hspawn : Xinst.step sevm devm .call = .spawn frame resume) :
    ∃ msg, frame = Frame.ofCall msg := by
  simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hspawn
  repeat' split at hspawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hspawn
  all_goals first
    | cases hspawn
    | exact ⟨_, (genericCall_step_spawn_exact_compiled hspawn).1⟩

private theorem Ninst.step_call_spawn_ofCall
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume}
    (hspawn : Ninst.step ⟨pc, sevm, pre⟩ Ninst.call =
      .spawn frame resume pc') :
    ∃ msg, frame = Frame.ofCall msg := by
  have hx : Xinst.step sevm pre .call = .spawn frame resume := by
    exact XStep.toStep_spawn (by
      simpa only [Ninst.call, Ninst.step_exec] using hspawn)
  exact Xinst.step_call_spawn_ofCall hx

private theorem Frame.settlementCommits_ofCall_of_raw_commits
    {msg : Msg} {raw : Execution}
    (hraw : Execution.commits raw = true) :
    Frame.settlementCommits (Frame.ofCall msg) raw = true := by
  cases raw with
  | error err =>
      simp [Execution.commits] at hraw
  | ok post =>
      cases herror : post.error with
      | none =>
          simp [Frame.settlementCommits, Frame.settle, Frame.settleMsg,
            Frame.ofCall, executeCode.handleError,
            processMessage.settle, herror]
      | some error =>
          simp [Execution.commits, herror] at hraw

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
    (commits : retained.RawCommits)
    (edge : Exec.Deriv.ParentStepActions dp ca
      ⟨nextPc, sevm, post, out, continuation⟩
      ⟨pc, sevm, pre, out, current⟩ selected) :
    selected = retained.flowActions dp ca := by
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
    (cursor : frame.CompiledCursor dp ca fs table
      (.next Ninst.call tail) final)
    (rawFilled : rawSlot.Filled)
    (rawStep : Ninst.StepRun rawPc frame.sevm cursor.pre
      Ninst.call rawSlot (.ok rawPost))
    (retained : RetainedXlot rawSlot)
    (commits : retained.RawCommits) :
    ∃ tailCursor : frame.CompiledCursor dp ca fs table tail final,
      tailCursor.pre = rawPost ∧
      frame.NinstOccurrence dp ca Ninst.call
        cursor.pre rawPost rawSlot ∧
      tailCursor.actions =
        cursor.actions ++ retained.flowActions dp ca := by
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
    (cursor : frame.CompiledCursor dp ca fs table (.next n tail) final)
    (hchildless : NinstIsChildless n) :
    ∃ (tailCursor : frame.CompiledCursor dp ca fs table tail final)
        (xl : Xlot),
      Ninst.Run frame.sevm cursor.pre n tailCursor.pre ∧
      frame.NinstOccurrence dp ca n cursor.pre tailCursor.pre xl ∧
      tailCursor.actions = cursor.actions := by
  cases hrun : cursor.run with
  | next hcompiled htail =>
      have hat : Ninst.At frame.sevm.code cursor.pc n :=
        ninstAt_of_subcode_next cursor.codeSlice
      rcases frame.advance_runCompiled_next cursor.current
          cursor.parentPrefix hat hcompiled with
        ⟨xl, continuation, selected, occurrence, hedge, hnextPrefix⟩
      have hselected : selected = [] :=
        hedge.eq_nil_of_isChildless hat hchildless
      subst selected
      obtain ⟨nextBoundary, nextSub⟩ :=
        Func.noPushBefore_next cursor.codeSlice cursor.codeBoundary
      let tailCursor : frame.CompiledCursor dp ca fs table tail final :=
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
    (cursor : frame.CompiledCursor dp ca fs table (line +++ tail) final)
    (hchildless : ∀ n ∈ line, NinstIsChildless n) :
    ∃ tailCursor : frame.CompiledCursor dp ca fs table tail final,
      Line.Run frame.sevm cursor.pre line tailCursor.pre ∧
      tailCursor.actions = cursor.actions := by
  induction line with
  | nil => exact ⟨cursor, .nil, rfl⟩
  | cons n line ih =>
      change frame.CompiledCursor dp ca fs table
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

set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
theorem weth10_pcFree (dp : DeployParams) :
    Prog.pcFree (weth10 dp) = true := by
  have hentries : ∀ entry ∈ weth10Funcs dp,
      entry.2.pcFreeBody = true := by
    have hall : (weth10Funcs dp).all
        (fun entry => entry.2.pcFreeBody) = true := by
      change (weth10Funcs (⟨0, 0⟩ : DeployParams)).all
        (fun entry => entry.2.pcFreeBody) = true
      decide +kernel
    simpa only [List.all_eq_true] using hall
  have htree : CompiledDispatchPcFree (weth10Tree dp) :=
    compiledDispatchPcFree_build (weth10Funcs dp).length
      (weth10Funcs dp) hentries
  have hdispatch := compiledDispatchWith_pcFree htree
  have hprefix :
      (fsig +++
        dispatchWith fallbackSlot (weth10Tree dp)).pcFreeBody = true := by
    simp [fsig, cdl, shiftRight, prepend, Func.pcFreeBody, Ninst.pcFree,
      Ninst.pushB256, hdispatch]
  have hmint : mintCaller.pcFreeBody = true := by decide +kernel
  have haux : weth10Aux.all Func.pcFreeBody = true := by decide +kernel
  simp [Prog.pcFree, Func.pcFree, weth10, weth10Main, receiveEther,
    Func.pcFreeBody, Ninst.pcFree, hprefix, hmint, haux]

/-- Exact gas burns from the same source state have the same target state. -/
private theorem Devm.eq_of_burnBy
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
    (context : frame.AuthenticContext dp ca) :
    ∃ cursor : frame.CompiledCursor dp ca
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
      rcases Exec.Frame.advance_cont
          (frame := ⟨0, e, pre, .ok post, run, committed⟩)
          run hrootPrefix hstep with
        ⟨actualContinuation, hentryPrefix⟩
      have hprefix : Exec.Deriv.ParentPrefixActions dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨1, e, actualMid, .ok post, actualContinuation⟩ [] := by
        simpa using hentryPrefix
      exact ⟨⟨1, actualMid, actualContinuation, [], hprefix, hmain,
        hsub, hboundary⟩, rfl⟩

/-- A matching compiled dispatch leaf advances to its stored body while
removing the selector word from the stack. -/
private theorem Exec.Frame.CompiledCursor.reachDispatchLeaf
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)} {final : Devm}
    {sig w : B256} {f body : Func} {k : Nat} {stack : Stack}
    (hmem : (sig, f) ∈ [(w, body)])
    (cursor : frame.CompiledCursor dp ca fs table
      (dispatchWith k (.leaf w body)) final)
    (hstack : sig :: stack <<+ cursor.pre.stack) :
    ∃ bodyCursor : frame.CompiledCursor dp ca fs table f final,
      stack <<+ bodyCursor.pre.stack ∧
      bodyCursor.actions = cursor.actions := by
  have heq : (sig, f) = (w, body) := List.mem_singleton.mp hmem
  injection heq with hsig hfun
  subst w
  subst body
  change frame.CompiledCursor dp ca fs table
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
      (cursor : frame.CompiledCursor dp ca fs table
        (dispatchWith k (DispatchTree.build n xs)) final) →
      (sig :: stack <<+ cursor.pre.stack) →
      ∃ bodyCursor : frame.CompiledCursor dp ca fs table f final,
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
        change frame.CompiledCursor dp ca fs table
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
    (cursor : frame.CompiledCursor dp ca fs table
      (dispatchWith k (DispatchTree.ofSorted funcs)) final)
    (hstack : sig :: stack <<+ cursor.pre.stack) :
    ∃ bodyCursor : frame.CompiledCursor dp ca fs table f final,
      stack <<+ bodyCursor.pre.stack ∧
      bodyCursor.actions = cursor.actions :=
  cursor.reachDispatchWith_build hsorted (Nat.le_succ _) hmem hstack

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
    (cursor : frame.CompiledCursor dp ca fs table (.last i) final) :
    frame.descendantFlowActions dp ca = cursor.actions := by
  have htail : Exec.Deriv.descendantFlowActions dp ca
      ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩ = [] := by
    have hat : Linst.At frame.sevm.code cursor.pc i :=
      Linst.at_of_slice cursor.codeSlice
    have hstep := Evm.step_last (devm := cursor.pre) hat
    simp [Exec.Deriv.descendantFlowActions,
      Exec.descendantFrames_eq_nil_of_halt_step cursor.current hstep]
  have hp := cursor.parentPrefix.descendantFlowActions_eq
  change frame.descendantFlowActions dp ca =
    cursor.actions ++ Exec.Deriv.descendantFlowActions dp ca
      ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩ at hp
  rw [htail] at hp
  simpa using hp

/-- A successful authentic non-receive invocation reaches the cursor for its
exact listed selector body.  This is the proof-indexed counterpart of
`reach_of_dispatchWith`: the returned cursor belongs to the original retained
frame and therefore remembers every earlier child action. -/
theorem Exec.Frame.compiledSelectorBodyCursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {body : Func}
    (context : frame.AuthenticContext dp ca)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp) :
    ∃ bodyCursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux)) body frame.post,
      [] <<+ bodyCursor.pre.stack ∧ bodyCursor.actions = [] := by
  rcases frame.compiledMainCursor context with
    ⟨mainCursor, hmainActions⟩
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ([Ninst.calldatasize, Ninst.iszero] +++
      (receiveEther <?>
        (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))))
    frame.post at mainCursor
  rcases mainCursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨entryBranchCursor, hentryLine, hentryActions⟩
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
  rcases entryBranchCursor.selectBranchZero hflagPrefix with
    ⟨dispatchPrefixCursor, hdispatchStack, hdispatchActions⟩
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))
    frame.post at dispatchPrefixCursor
  rcases dispatchPrefixCursor.peelChildlessLine
      (by simp [fsig, cdl, shiftRight, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨dispatchCursor, hfsig, hfsigActions⟩
  have hselectorPrefix : Sevm.selector frame.sevm :: [] <<+
      dispatchCursor.pre.stack :=
    prefix_of_fsig nil_pref hfsig
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (dispatchWith fallbackSlot
      (DispatchTree.ofSorted (weth10Funcs dp))) frame.post at dispatchCursor
  rcases dispatchCursor.reachDispatchWith (weth10Funcs_sorted dp)
      hmem hselectorPrefix with
    ⟨bodyCursor, hbodyStack, hbodyActions⟩
  refine ⟨bodyCursor, hbodyStack, ?_⟩
  exact hbodyActions.trans (hfsigActions.trans
    (hdispatchActions.trans (hentryActions.trans hmainActions)))

/-- A successful cursor at a nonpayable wrapper reaches its guarded body on
the original execution. -/
theorem Exec.Frame.CompiledCursor.enterNonpayable
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {final : Devm}
    (cursor : frame.CompiledCursor dp ca fs table
      (nonpayable body) final) :
    ∃ bodyCursor : frame.CompiledCursor dp ca fs table body final,
      [] <<+ bodyCursor.pre.stack ∧
      bodyCursor.actions = cursor.actions := by
  have hvalue : frame.sevm.value = 0 :=
    value_eq_zero_of_run_nonpayable
      (Func.Run.of_runCompiled cursor.run)
  change frame.CompiledCursor dp ca fs table
    ([Ninst.callvalue, Ninst.iszero] +++ (body <?> Func.rev)) final at cursor
  rcases cursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨branchCursor, hline, hbranchActions⟩
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
  rcases branchCursor.selectBranchSucc (flag := (1 : B256))
      (by decide) hflagPrefix with
    ⟨bodyCursor, hbodyStack, hbodyActions⟩
  exact ⟨bodyCursor, hbodyStack, hbodyActions.trans hbranchActions⟩

/-- Follow one generated internal source call while preserving the original
frame execution and its chronological child-action prefix.  The installed
program equation is explicit because the cursor's local code slice alone
cannot identify the called table body. -/
theorem Exec.Frame.CompiledCursor.enterCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      ∃ bodyCursor : frame.CompiledCursor dp ca (f₀ :: aux)
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
      rcases frame.advance_cont cursor.current cursor.parentPrefix
          hstepPush with
        ⟨afterPush, hprefixPush⟩
      rcases frame.advance_cont afterPush hprefixPush hstepJump with
        ⟨afterJump, hprefixJump⟩
      rcases frame.advance_cont afterJump hprefixJump hstepJumpdest with
        ⟨bodyExec, hprefixBody⟩
      let bodyCursor : frame.CompiledCursor dp ca (f₀ :: aux)
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
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux) table
      (callBoolCallback sel targetArg dataArg value) final)
    (hvalue : ∀ n ∈ value, NinstIsChildless n) :
    ∃ callCursor : frame.CompiledCursor dp ca (f₀ :: aux) table
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

/-- A childless line ending in a terminal instruction closes the chronological
cursor without crossing any additional retained child. -/
theorem Exec.Frame.CompiledCursor.finishTerminalChildlessLine
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {line : Line} {i : Linst} {final : Devm}
    (cursor : frame.CompiledCursor dp ca fs table
      (line +++ Func.last i) final)
    (hchildless : ∀ n ∈ line, NinstIsChildless n) :
    frame.descendantFlowActions dp ca = cursor.actions := by
  rcases cursor.peelChildlessLine hchildless with
    ⟨lastCursor, _hline, hactions⟩
  exact lastCursor.finishLast.trans hactions

/-- The successful Boolean decoder after an ERC-677 `CALL` contains no
external execution.  Its revert/bubble arms cannot produce the retained
frame's committed final state, while its decode arm is childless. -/
theorem Exec.Frame.CompiledCursor.finishBoolReturnCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {final : Devm}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (.call boolReturnSlot) final)
    (hcode : some frame.sevm.code.toList = Prog.compile (weth10 dp)) :
    frame.descendantFlowActions dp ca = cursor.actions := by
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
      change frame.CompiledCursor dp ca
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
  authentic : frame.AuthenticContext dp ca
  classified : frame.flowAction? dp ca = some action
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
  authentic : frame.AuthenticContext dp ca
  classified : frame.flowAction? dp ca = some action
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
  authentic : frame.AuthenticContext dp ca
  unclassified : frame.flowAction? dp ca = none
  effect : NoWethBalanceOwnEffect dp frame.sevm frame.pre frame.post

/-- Exhaustive own-storage classification of a successful authentic compiled
WETH10 frame.  The flow arm carries the exact action and rich operational
effect; the non-flow arm carries the selector-specific proof that the frame's
own code did not write a WETH balance slot. -/
inductive Exec.Frame.HasCompiledBalanceOwnEffect (dp : DeployParams)
    (ca : Adr) (frame : Exec.Frame) : Prop
  | flow (action : FlowAction)
      (effect : frame.HasRichLocalStorageEffect dp ca action)
  | noFlow (effect : frame.HasNoWethBalanceOwnEffect dp ca)

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
    (context : frame.AuthenticContext dp ca)
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
    (context : frame.AuthenticContext dp ca)
    (hatom : primaryFlowAtom frame.sevm = some atom)
    (haction : frame.flowAction? dp ca = some action) :
    action =
      { atom
        credit := atom.creditOccurrence frame.pre ca
        debit := primaryDebitProvenance frame.sevm frame.pre frame.post
        actualCaller := frame.sevm.caller
        currentTarget := frame.sevm.currentTarget
        codeAddress := frame.sevm.codeAddress
        depth := frame.sevm.depth } := by
  simp only [Exec.Frame.flowAction?, if_pos context.invocation, hatom,
    Option.map_some, Option.some.injEq] at haction
  exact haction.symm

private theorem debit_eq_of_flowAction_eq
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (haction : frame.flowAction? dp ca = some action) :
    action.debit =
      primaryDebitProvenance frame.sevm frame.pre frame.post := by
  unfold Exec.Frame.flowAction? at haction
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

private theorem flashAllowanceBranch_accepted_from_post
    {dp : DeployParams} {e : Sevm} {settle burn post : Devm}
    (h : FlashAllowanceOutcome e settle burn)
    (hburn : Func.Run ((weth10 dp).main :: weth10Aux) e burn
      flashBurn post) :
    FlashAllowanceAccepted e settle burn
      (flashAllowanceBranchFromPost e post) := by
  have hkey := flashBurn_storage_at_allowanceKey dp hburn
  unfold flashAllowanceBranchFromPost
  rcases h.1 with hmax | hfinite
  · have hpostmax : (Devm.getStor post e.currentTarget).get
        (flashAllowanceRuntimeKey e) = B256.max := by
      rw [hkey, hmax.2.1, hmax.1]
    rw [if_pos hpostmax]
    exact ⟨h, rfl, hmax.1⟩
  · rcases hfinite with
      ⟨allowance, hnotmax, hle, hread, hwrite, hlogs⟩
    have hpostafter : (Devm.getStor post e.currentTarget).get
        (flashAllowanceRuntimeKey e) =
          allowance - Sevm.argWord e 2 := by
      rw [hkey, hwrite, Stor.get_set_self]
    have hsuble : allowance - Sevm.argWord e 2 ≤ allowance := by
      apply B256.le_of_toNat_le_toNat
      rw [B256.toNat_sub_eq_of_le _ _ hle]
      omega
    have hallowlemax : allowance ≤ B256.max := by
      apply B256.le_of_toNat_le_toNat
      have hlt := B256.toNat_lt allowance
      change allowance.toNat ≤ 2 ^ 256 - 1
      omega
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
    refine ⟨h, rfl, ?_, ?_, ?_, ?_⟩
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
    (context : frame.AuthenticContext dp ca)
    (hempty : frame.sevm.data.length.toB256 = 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasLocalOwnEffect ca action := by
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
      simp [Exec.Frame.flowAction?, context.invocation, primaryFlowAtom,
        primaryDebitProvenance, hempty] at haction'
      symm at haction'
      subst action
      unfold Exec.Frame.HasLocalOwnEffect
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
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = depositSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasLocalOwnEffect ca action := by
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
      have hdTransfer : depositSelector ≠ transferSelector := by
        decide +kernel
      have hdTransferCall : depositSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hdWithdraw : depositSelector ≠ withdrawSelector := by
        decide +kernel
      have hdWithdrawTo : depositSelector ≠ withdrawToSelector := by
        decide +kernel
      have hdTransferFrom : depositSelector ≠ transferFromSelector := by
        decide +kernel
      have hdWithdrawFrom : depositSelector ≠ withdrawFromSelector := by
        decide +kernel
      have hdFlash : depositSelector ≠ flashLoanSelector := by
        decide +kernel
      have haction' := haction
      simp [Exec.Frame.flowAction?, context.invocation, primaryFlowAtom,
        primaryDebitProvenance, hnonempty, hselector, hdTransfer,
        hdTransferCall, hdWithdraw, hdWithdrawTo, hdTransferFrom,
        hdWithdrawFrom, hdFlash] at haction'
      symm at haction'
      subst action
      unfold Exec.Frame.HasLocalOwnEffect
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
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasLocalOwnEffect ca action := by
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
        have hsDeposit : transferSelector ≠ depositSelector := by
          decide +kernel
        have hsDepositTo : transferSelector ≠ depositToSelector := by
          decide +kernel
        have hsDepositCall :
            transferSelector ≠ depositToAndCallSelector := by
          decide +kernel
        have hatom : primaryFlowAtom e = some
            (.redemption e.caller.toB256 e.caller e.caller
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
            hsDepositTo, hsDepositCall, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        unfold Exec.Frame.HasLocalOwnEffect
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
        have hsDeposit : transferSelector ≠ depositSelector := by
          decide +kernel
        have hsDepositTo : transferSelector ≠ depositToSelector := by
          decide +kernel
        have hsDepositCall :
            transferSelector ≠ depositToAndCallSelector := by
          decide +kernel
        have hatom : primaryFlowAtom e = some
            (.transfer e.caller.toB256 (Sevm.argWord e 0) e.caller
              (Sevm.argWord e 0).toAdr
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
            hsDepositTo, hsDepositCall, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        unfold Exec.Frame.HasLocalOwnEffect
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
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = depositToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasLocalOwnEffect ca action := by
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
      have hsDeposit : depositToSelector ≠ depositSelector := by
        decide +kernel
      have hsTransfer : depositToSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          depositToSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsTransferFrom : depositToSelector ≠ transferFromSelector := by
        decide +kernel
      have hsWithdraw : depositToSelector ≠ withdrawSelector := by
        decide +kernel
      have hsWithdrawTo : depositToSelector ≠ withdrawToSelector := by
        decide +kernel
      have hsWithdrawFrom : depositToSelector ≠ withdrawFromSelector := by
        decide +kernel
      have hsFlash : depositToSelector ≠ flashLoanSelector := by
        decide +kernel
      have hatom : primaryFlowAtom e = some
          (.ordinaryMint (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            e.value.toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector, hsDeposit]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      unfold Exec.Frame.HasLocalOwnEffect
      refine ⟨Stor.rest (Devm.getStor post ca), ?_⟩
      apply localOwnEffect_ordinaryMint
      · rfl
      · unfold FlowAction.ExactCredit
        simp only [FlowAtom.creditOccurrence]
        rw [toB256_toNat]
      · simp [primaryDebitProvenance, hnonempty, hselector, hsTransfer,
          hsTransferCall, hsTransferFrom, hsWithdraw, hsWithdrawTo,
          hsWithdrawFrom, hsFlash]
      · exact hincrease

theorem Exec.Frame.hasLocalOwnEffect_of_depositToAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (hselector :
      Sevm.selector frame.sevm = depositToAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasLocalOwnEffect ca action := by
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
      have hsDeposit : depositToAndCallSelector ≠ depositSelector := by
        decide +kernel
      have hsTransfer :
          depositToAndCallSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          depositToAndCallSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsTransferFrom :
          depositToAndCallSelector ≠ transferFromSelector := by
        decide +kernel
      have hsWithdraw :
          depositToAndCallSelector ≠ withdrawSelector := by
        decide +kernel
      have hsWithdrawTo :
          depositToAndCallSelector ≠ withdrawToSelector := by
        decide +kernel
      have hsWithdrawFrom :
          depositToAndCallSelector ≠ withdrawFromSelector := by
        decide +kernel
      have hsFlash : depositToAndCallSelector ≠ flashLoanSelector := by
        decide +kernel
      have hatom : primaryFlowAtom e = some
          (.ordinaryMint (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            e.value.toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector, hsDeposit]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      unfold Exec.Frame.HasLocalOwnEffect
      refine ⟨Stor.rest (Devm.getStor callbackPre ca), ?_⟩
      apply localOwnEffect_ordinaryMint
      · rfl
      · unfold FlowAction.ExactCredit
        simp only [FlowAtom.creditOccurrence]
        rw [toB256_toNat]
      · simp [primaryDebitProvenance, hnonempty, hselector, hsTransfer,
          hsTransferCall, hsTransferFrom, hsWithdraw, hsWithdrawTo,
          hsWithdrawFrom, hsFlash]
      · exact hincrease

theorem Exec.Frame.hasLocalOwnEffect_of_transferAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasLocalOwnEffect ca action := by
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
      have hsDeposit : transferAndCallSelector ≠ depositSelector := by
        decide +kernel
      have hsDepositTo : transferAndCallSelector ≠ depositToSelector := by
        decide +kernel
      have hsDepositCall :
          transferAndCallSelector ≠ depositToAndCallSelector := by
        decide +kernel
      rcases heffect with hzero | hnonzero
      · rcases hzero with
          ⟨hraw, callPre, callbackPre, inputSize, input, hprefix,
            hboundary⟩
        unfold BurnCallPrefix at hprefix
        rw [htarget] at hprefix
        have hatom : primaryFlowAtom e = some
            (.redemption e.caller.toB256 e.caller e.caller
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
            hsDepositTo, hsDepositCall, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        unfold Exec.Frame.HasLocalOwnEffect
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
          simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
            hsDepositTo, hsDepositCall, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        unfold Exec.Frame.HasLocalOwnEffect
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
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasLocalOwnEffect ca action := by
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
      have hsDeposit : transferFromSelector ≠ depositSelector := by
        decide +kernel
      have hsDepositTo : transferFromSelector ≠ depositToSelector := by
        decide +kernel
      have hsDepositCall :
          transferFromSelector ≠ depositToAndCallSelector := by
        decide +kernel
      have hsTransfer : transferFromSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          transferFromSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsWithdraw : transferFromSelector ≠ withdrawSelector := by
        decide +kernel
      have hsWithdrawTo : transferFromSelector ≠ withdrawToSelector := by
        decide +kernel
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
          simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
            hsDepositTo, hsDepositCall, hsTransfer, hsTransferCall, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        unfold Exec.Frame.HasLocalOwnEffect
        refine ⟨Stor.rest (Devm.getStor callPre ca), ?_⟩
        apply localOwnEffect_redemption
        · rfl
        · rfl
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector, hsTransfer,
            hsTransferCall, hsWithdraw, hsWithdrawTo]
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
          simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
            hsDepositTo, hsDepositCall, hsTransfer, hsTransferCall, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        unfold Exec.Frame.HasLocalOwnEffect
        refine ⟨Stor.rest (Devm.getStor post ca), ?_⟩
        apply localOwnEffect_ordinaryTransfer
        · rfl
        · unfold FlowAction.ExactCredit
          simp only [FlowAtom.creditOccurrence]
          rw [toB256_toNat]
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector, hsTransfer,
            hsTransferCall, hsWithdraw, hsWithdrawTo]
        · exact htransfer

theorem Exec.Frame.hasLocalOwnEffect_of_withdraw
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = withdrawSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasLocalOwnEffect ca action := by
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
      have hsDeposit : withdrawSelector ≠ depositSelector := by
        decide +kernel
      have hsDepositTo : withdrawSelector ≠ depositToSelector := by
        decide +kernel
      have hsDepositCall :
          withdrawSelector ≠ depositToAndCallSelector := by
        decide +kernel
      have hsTransfer : withdrawSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          withdrawSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsTransferFrom : withdrawSelector ≠ transferFromSelector := by
        decide +kernel
      have hatom : primaryFlowAtom e = some
          (.redemption e.caller.toB256 e.caller e.caller
            (Sevm.argWord e 0).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
          hsDepositTo, hsDepositCall, hsTransfer, hsTransferCall,
          hsTransferFrom]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      unfold Exec.Frame.HasLocalOwnEffect
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
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = withdrawToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasLocalOwnEffect ca action := by
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
      have hsDeposit : withdrawToSelector ≠ depositSelector := by
        decide +kernel
      have hsDepositTo : withdrawToSelector ≠ depositToSelector := by
        decide +kernel
      have hsDepositCall :
          withdrawToSelector ≠ depositToAndCallSelector := by
        decide +kernel
      have hsTransfer : withdrawToSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          withdrawToSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsTransferFrom : withdrawToSelector ≠ transferFromSelector := by
        decide +kernel
      have hsWithdraw : withdrawToSelector ≠ withdrawSelector := by
        decide +kernel
      have hatom : primaryFlowAtom e = some
          (.redemption e.caller.toB256 e.caller
            (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
          hsDepositTo, hsDepositCall, hsTransfer, hsTransferCall,
          hsTransferFrom, hsWithdraw]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      unfold Exec.Frame.HasLocalOwnEffect
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
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = withdrawFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasLocalOwnEffect ca action := by
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
      have hsDeposit : withdrawFromSelector ≠ depositSelector := by
        decide +kernel
      have hsDepositTo : withdrawFromSelector ≠ depositToSelector := by
        decide +kernel
      have hsDepositCall :
          withdrawFromSelector ≠ depositToAndCallSelector := by
        decide +kernel
      have hsTransfer : withdrawFromSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          withdrawFromSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsTransferFrom : withdrawFromSelector ≠ transferFromSelector := by
        decide +kernel
      have hsWithdraw : withdrawFromSelector ≠ withdrawSelector := by
        decide +kernel
      have hsWithdrawTo : withdrawFromSelector ≠ withdrawToSelector := by
        decide +kernel
      have hatom : primaryFlowAtom e = some
          (.redemption (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            (Sevm.argWord e 1).toAdr (Sevm.argWord e 2).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
          hsDepositTo, hsDepositCall, hsTransfer, hsTransferCall,
          hsTransferFrom, hsWithdraw, hsWithdrawTo]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      unfold Exec.Frame.HasLocalOwnEffect
      refine ⟨Stor.rest (Devm.getStor callPre ca), ?_⟩
      apply localOwnEffect_redemption
      · rfl
      · rfl
      · unfold FlowAction.HasDebitSource
        simp [primaryDebitProvenance, hnonempty, hselector, hsTransfer,
          hsTransferCall, hsTransferFrom, hsWithdraw, hsWithdrawTo]
      · exact hprefix.2.1
      · exact hprefix.1

theorem Exec.Frame.hasLocalOwnEffect_of_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasLocalOwnEffect ca action := by
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
      have hsDeposit : flashLoanSelector ≠ depositSelector := by
        decide +kernel
      have hsDepositTo : flashLoanSelector ≠ depositToSelector := by
        decide +kernel
      have hsDepositCall :
          flashLoanSelector ≠ depositToAndCallSelector := by
        decide +kernel
      have hsTransfer : flashLoanSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          flashLoanSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsTransferFrom : flashLoanSelector ≠ transferFromSelector := by
        decide +kernel
      have hsWithdraw : flashLoanSelector ≠ withdrawSelector := by
        decide +kernel
      have hsWithdrawTo : flashLoanSelector ≠ withdrawToSelector := by
        decide +kernel
      have hsWithdrawFrom : flashLoanSelector ≠ withdrawFromSelector := by
        decide +kernel
      have hatom : primaryFlowAtom e = some
          (.flashPair (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            (Sevm.argWord e 2).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
          hsDepositTo, hsDepositCall, hsTransfer, hsTransferCall,
          hsTransferFrom, hsWithdraw, hsWithdrawTo, hsWithdrawFrom]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      unfold Exec.Frame.HasLocalOwnEffect
      refine ⟨Stor.rest (Devm.getStor post ca), ?_⟩
      apply localOwnEffect_flashPair
      · rfl
      · unfold FlowAction.ExactCredit
        simp only [FlowAtom.creditOccurrence]
        rw [toB256_toNat]
      · unfold FlowAction.HasFlashDebitSource
        simp [primaryDebitProvenance, hnonempty, hselector, hsTransfer,
          hsTransferCall, hsTransferFrom, hsWithdraw, hsWithdrawTo,
          hsWithdrawFrom]
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
    (context : frame.AuthenticContext dp ca)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasAcceptedDebit dp ca action := by
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
          have h₁ : transferFromSelector ≠ transferSelector := by
            decide +kernel
          have h₂ : transferFromSelector ≠ transferAndCallSelector := by
            decide +kernel
          have h₃ : transferFromSelector ≠ withdrawSelector := by
            decide +kernel
          have h₄ : transferFromSelector ≠ withdrawToSelector := by
            decide +kernel
          simp [primaryDebitProvenance, hnonempty, htransferFrom,
            h₁, h₂, h₃, h₄]
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
          have h₁ : withdrawFromSelector ≠ transferSelector := by
            decide +kernel
          have h₂ : withdrawFromSelector ≠ transferAndCallSelector := by
            decide +kernel
          have h₃ : withdrawFromSelector ≠ withdrawSelector := by
            decide +kernel
          have h₄ : withdrawFromSelector ≠ withdrawToSelector := by
            decide +kernel
          have h₅ : withdrawFromSelector ≠ transferFromSelector := by
            decide +kernel
          simp [primaryDebitProvenance, hnonempty, hwithdrawFrom,
            h₁, h₂, h₃, h₄, h₅]
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
          have h₁ : flashLoanSelector ≠ transferSelector := by
            decide +kernel
          have h₂ : flashLoanSelector ≠ transferAndCallSelector := by
            decide +kernel
          have h₃ : flashLoanSelector ≠ withdrawSelector := by
            decide +kernel
          have h₄ : flashLoanSelector ≠ withdrawToSelector := by
            decide +kernel
          have h₅ : flashLoanSelector ≠ transferFromSelector := by
            decide +kernel
          have h₆ : flashLoanSelector ≠ withdrawFromSelector := by
            decide +kernel
          simp [primaryDebitProvenance, hnonempty, hflash,
            h₁, h₂, h₃, h₄, h₅, h₆,
            Exec.Frame.post, Execution.committedPost]
        · exact flashAllowanceBranch_accepted_from_post hallowance hburnRun
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
    (context : frame.AuthenticContext dp ca)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasGenuineWethEmitterEffect dp ca action := by
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
      simp [Exec.Frame.flowAction?, context.invocation, hprimary] at haction

/-- Reverse leaf classification for every recognized non-flow selector.
The recognized-leaf premise is deliberately explicit: deriving it from an
arbitrary successful `Exec` is supplied by the compiled dispatch bridge below.

All fourteen read leaves and `approve` are silent at the public endpoint.
`approveAndCall` and `permit` retain their exact recursive machine boundaries,
with every own balance-region prefix and suffix proved silent. -/
theorem Exec.Frame.hasNoWethBalanceOwnEffect_of_recognized
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hnone : frame.flowAction? dp ca = none)
    (hrecognized : ∃ body,
      (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp) :
    frame.HasNoWethBalanceOwnEffect dp ca := by
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
        unfold Exec.Frame.flowAction? at hnone
        rw [if_pos context.invocation] at hnone
        cases h : primaryFlowAtom e with
        | none => exact (hprimary h).elim
        | some atom => simp [h] at hnone
      have hnonempty : e.data.length.toB256 ≠ 0 := hempty
      have hprimary : primaryFlowAtom e = none := by
        unfold Exec.Frame.flowAction? at hnone
        rw [if_pos context.invocation] at hnone
        cases h : primaryFlowAtom e with
        | none => rfl
        | some atom => simp [h] at hnone
      have hnotDeposit : Sevm.selector e ≠ depositSelector := by
        intro h
        simp [primaryFlowAtom, hnonempty, h] at hprimary
      have hnotDepositTo : Sevm.selector e ≠ depositToSelector := by
        intro h
        have hne : depositToSelector ≠ depositSelector := by
          decide +kernel
        simp [primaryFlowAtom, hnonempty, h, hne] at hprimary
      have hnotDepositCall :
          Sevm.selector e ≠ depositToAndCallSelector := by
        intro h
        have hne : depositToAndCallSelector ≠ depositSelector := by
          decide +kernel
        simp [primaryFlowAtom, hnonempty, h, hne] at hprimary
      have hnotTransfer : Sevm.selector e ≠ transferSelector := by
        intro h
        have hneDeposit : transferSelector ≠ depositSelector := by
          decide +kernel
        have hneDepositTo : transferSelector ≠ depositToSelector := by
          decide +kernel
        have hneDepositCall :
            transferSelector ≠ depositToAndCallSelector := by
          decide +kernel
        simp [primaryFlowAtom, hnonempty, h, hneDeposit, hneDepositTo,
          hneDepositCall] at hprimary
        split at hprimary <;> simp_all
      have hnotTransferCall :
          Sevm.selector e ≠ transferAndCallSelector := by
        intro h
        have hneDeposit : transferAndCallSelector ≠ depositSelector := by
          decide +kernel
        have hneDepositTo :
            transferAndCallSelector ≠ depositToSelector := by
          decide +kernel
        have hneDepositCall :
            transferAndCallSelector ≠ depositToAndCallSelector := by
          decide +kernel
        simp [primaryFlowAtom, hnonempty, h, hneDeposit, hneDepositTo,
          hneDepositCall] at hprimary
        split at hprimary <;> simp_all
      have hnotTransferFrom :
          Sevm.selector e ≠ transferFromSelector := by
        intro h
        have hneDeposit : transferFromSelector ≠ depositSelector := by
          decide +kernel
        have hneDepositTo : transferFromSelector ≠ depositToSelector := by
          decide +kernel
        have hneDepositCall :
            transferFromSelector ≠ depositToAndCallSelector := by
          decide +kernel
        have hneTransfer : transferFromSelector ≠ transferSelector := by
          decide +kernel
        have hneTransferCall :
            transferFromSelector ≠ transferAndCallSelector := by
          decide +kernel
        simp [primaryFlowAtom, hnonempty, h, hneDeposit, hneDepositTo,
          hneDepositCall, hneTransfer, hneTransferCall] at hprimary
        split at hprimary <;> simp_all
      have hnotWithdraw : Sevm.selector e ≠ withdrawSelector := by
        intro h
        have hneDeposit : withdrawSelector ≠ depositSelector := by
          decide +kernel
        have hneDepositTo : withdrawSelector ≠ depositToSelector := by
          decide +kernel
        have hneDepositCall :
            withdrawSelector ≠ depositToAndCallSelector := by
          decide +kernel
        have hneTransfer : withdrawSelector ≠ transferSelector := by
          decide +kernel
        have hneTransferCall :
            withdrawSelector ≠ transferAndCallSelector := by
          decide +kernel
        have hneTransferFrom :
            withdrawSelector ≠ transferFromSelector := by
          decide +kernel
        simp [primaryFlowAtom, hnonempty, h, hneDeposit, hneDepositTo,
          hneDepositCall, hneTransfer, hneTransferCall, hneTransferFrom]
          at hprimary
      have hnotWithdrawTo : Sevm.selector e ≠ withdrawToSelector := by
        intro h
        have hneDeposit : withdrawToSelector ≠ depositSelector := by
          decide +kernel
        have hneDepositTo : withdrawToSelector ≠ depositToSelector := by
          decide +kernel
        have hneDepositCall :
            withdrawToSelector ≠ depositToAndCallSelector := by
          decide +kernel
        have hneTransfer : withdrawToSelector ≠ transferSelector := by
          decide +kernel
        have hneTransferCall :
            withdrawToSelector ≠ transferAndCallSelector := by
          decide +kernel
        have hneTransferFrom :
            withdrawToSelector ≠ transferFromSelector := by
          decide +kernel
        have hneWithdraw : withdrawToSelector ≠ withdrawSelector := by
          decide +kernel
        simp [primaryFlowAtom, hnonempty, h, hneDeposit, hneDepositTo,
          hneDepositCall, hneTransfer, hneTransferCall, hneTransferFrom,
          hneWithdraw] at hprimary
      have hnotWithdrawFrom :
          Sevm.selector e ≠ withdrawFromSelector := by
        intro h
        have hneDeposit : withdrawFromSelector ≠ depositSelector := by
          decide +kernel
        have hneDepositTo :
            withdrawFromSelector ≠ depositToSelector := by
          decide +kernel
        have hneDepositCall :
            withdrawFromSelector ≠ depositToAndCallSelector := by
          decide +kernel
        have hneTransfer : withdrawFromSelector ≠ transferSelector := by
          decide +kernel
        have hneTransferCall :
            withdrawFromSelector ≠ transferAndCallSelector := by
          decide +kernel
        have hneTransferFrom :
            withdrawFromSelector ≠ transferFromSelector := by
          decide +kernel
        have hneWithdraw : withdrawFromSelector ≠ withdrawSelector := by
          decide +kernel
        have hneWithdrawTo :
            withdrawFromSelector ≠ withdrawToSelector := by
          decide +kernel
        simp [primaryFlowAtom, hnonempty, h, hneDeposit, hneDepositTo,
          hneDepositCall, hneTransfer, hneTransferCall, hneTransferFrom,
          hneWithdraw, hneWithdrawTo] at hprimary
      have hnotFlash : Sevm.selector e ≠ flashLoanSelector := by
        intro h
        have hneDeposit : flashLoanSelector ≠ depositSelector := by
          decide +kernel
        have hneDepositTo : flashLoanSelector ≠ depositToSelector := by
          decide +kernel
        have hneDepositCall :
            flashLoanSelector ≠ depositToAndCallSelector := by
          decide +kernel
        have hneTransfer : flashLoanSelector ≠ transferSelector := by
          decide +kernel
        have hneTransferCall :
            flashLoanSelector ≠ transferAndCallSelector := by
          decide +kernel
        have hneTransferFrom :
            flashLoanSelector ≠ transferFromSelector := by
          decide +kernel
        have hneWithdraw : flashLoanSelector ≠ withdrawSelector := by
          decide +kernel
        have hneWithdrawTo : flashLoanSelector ≠ withdrawToSelector := by
          decide +kernel
        have hneWithdrawFrom :
            flashLoanSelector ≠ withdrawFromSelector := by
          decide +kernel
        simp [primaryFlowAtom, hnonempty, h, hneDeposit, hneDepositTo,
          hneDepositCall, hneTransfer, hneTransferCall, hneTransferFrom,
          hneWithdraw, hneWithdrawTo, hneWithdrawFrom] at hprimary
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
    (context : frame.AuthenticContext dp ca)
    (hempty : frame.sevm.data.length.toB256 = 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action := by
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
      simp [Exec.Frame.flowAction?, context.invocation, primaryFlowAtom,
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
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = depositSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action := by
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
      have hdTransfer : depositSelector ≠ transferSelector := by
        decide +kernel
      have hdTransferCall : depositSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hdWithdraw : depositSelector ≠ withdrawSelector := by
        decide +kernel
      have hdWithdrawTo : depositSelector ≠ withdrawToSelector := by
        decide +kernel
      have hdTransferFrom : depositSelector ≠ transferFromSelector := by
        decide +kernel
      have hdWithdrawFrom : depositSelector ≠ withdrawFromSelector := by
        decide +kernel
      have hdFlash : depositSelector ≠ flashLoanSelector := by
        decide +kernel
      have haction' := haction
      simp [Exec.Frame.flowAction?, context.invocation, primaryFlowAtom,
        primaryDebitProvenance, hnonempty, hselector, hdTransfer,
        hdTransferCall, hdWithdraw, hdWithdrawTo, hdTransferFrom,
        hdWithdrawFrom, hdFlash] at haction'
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
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = depositToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action := by
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
      have hsDeposit : depositToSelector ≠ depositSelector := by
        decide +kernel
      have hsTransfer : depositToSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          depositToSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsTransferFrom : depositToSelector ≠ transferFromSelector := by
        decide +kernel
      have hsWithdraw : depositToSelector ≠ withdrawSelector := by
        decide +kernel
      have hsWithdrawTo : depositToSelector ≠ withdrawToSelector := by
        decide +kernel
      have hsWithdrawFrom : depositToSelector ≠ withdrawFromSelector := by
        decide +kernel
      have hsFlash : depositToSelector ≠ flashLoanSelector := by
        decide +kernel
      have hatom : primaryFlowAtom e = some
          (.ordinaryMint (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            e.value.toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector, hsDeposit]
      have heq := action_eq_of_flowAction_eq context hatom haction
      subst action
      refine ⟨context, haction, .ordinaryMint ?_⟩
      apply localSegment_ordinaryMint
      · rfl
      · unfold FlowAction.ExactCredit
        simp only [FlowAtom.creditOccurrence]
        rw [toB256_toNat]
      · simp [primaryDebitProvenance, hnonempty, hselector, hsTransfer,
          hsTransferCall, hsTransferFrom, hsWithdraw, hsWithdrawTo,
          hsWithdrawFrom, hsFlash]
      · exact hincrease

theorem Exec.Frame.hasRichLocalStorageEffect_of_depositToAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = depositToAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action := by
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
      have hsDeposit : depositToAndCallSelector ≠ depositSelector := by
        decide +kernel
      have hsTransfer :
          depositToAndCallSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          depositToAndCallSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsTransferFrom :
          depositToAndCallSelector ≠ transferFromSelector := by
        decide +kernel
      have hsWithdraw :
          depositToAndCallSelector ≠ withdrawSelector := by
        decide +kernel
      have hsWithdrawTo :
          depositToAndCallSelector ≠ withdrawToSelector := by
        decide +kernel
      have hsWithdrawFrom :
          depositToAndCallSelector ≠ withdrawFromSelector := by
        decide +kernel
      have hsFlash : depositToAndCallSelector ≠ flashLoanSelector := by
        decide +kernel
      have hatom : primaryFlowAtom e = some
          (.ordinaryMint (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            e.value.toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector, hsDeposit]
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
        · simp [primaryDebitProvenance, hnonempty, hselector, hsTransfer,
            hsTransferCall, hsTransferFrom, hsWithdraw, hsWithdrawTo,
            hsWithdrawFrom, hsFlash]
        · exact hincrease
      · exact congrFun hcode ca
      · exact hboundary

theorem Exec.Frame.hasRichLocalStorageEffect_of_transfer
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action := by
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
        have hsDeposit : transferSelector ≠ depositSelector := by
          decide +kernel
        have hsDepositTo : transferSelector ≠ depositToSelector := by
          decide +kernel
        have hsDepositCall :
            transferSelector ≠ depositToAndCallSelector := by
          decide +kernel
        have hatom : primaryFlowAtom e = some
            (.redemption e.caller.toB256 e.caller e.caller
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
            hsDepositTo, hsDepositCall, hraw]
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
        have hsDeposit : transferSelector ≠ depositSelector := by
          decide +kernel
        have hsDepositTo : transferSelector ≠ depositToSelector := by
          decide +kernel
        have hsDepositCall :
            transferSelector ≠ depositToAndCallSelector := by
          decide +kernel
        have hatom : primaryFlowAtom e = some
            (.transfer e.caller.toB256 (Sevm.argWord e 0) e.caller
              (Sevm.argWord e 0).toAdr
              (Sevm.argWord e 1).toNat) := by
          simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
            hsDepositTo, hsDepositCall, hraw]
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
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action := by
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
      have hsDeposit : transferAndCallSelector ≠ depositSelector := by
        decide +kernel
      have hsDepositTo : transferAndCallSelector ≠ depositToSelector := by
        decide +kernel
      have hsDepositCall :
          transferAndCallSelector ≠ depositToAndCallSelector := by
        decide +kernel
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
          simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
            hsDepositTo, hsDepositCall, hraw]
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
          simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
            hsDepositTo, hsDepositCall, hraw]
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
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action := by
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
      have hsDeposit : transferFromSelector ≠ depositSelector := by
        decide +kernel
      have hsDepositTo : transferFromSelector ≠ depositToSelector := by
        decide +kernel
      have hsDepositCall :
          transferFromSelector ≠ depositToAndCallSelector := by
        decide +kernel
      have hsTransfer : transferFromSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          transferFromSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsWithdraw : transferFromSelector ≠ withdrawSelector := by
        decide +kernel
      have hsWithdrawTo : transferFromSelector ≠ withdrawToSelector := by
        decide +kernel
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
          simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
            hsDepositTo, hsDepositCall, hsTransfer, hsTransferCall, hraw]
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
            simp [primaryDebitProvenance, hnonempty, hselector, hsTransfer,
              hsTransferCall, hsWithdraw, hsWithdrawTo]
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
          simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
            hsDepositTo, hsDepositCall, hsTransfer, hsTransferCall, hraw]
        have heq := action_eq_of_flowAction_eq context hatom haction
        subst action
        refine ⟨context, haction, .ordinaryTransfer ?_⟩
        apply localSegment_ordinaryTransfer
        · rfl
        · unfold FlowAction.ExactCredit
          simp only [FlowAtom.creditOccurrence]
          rw [toB256_toNat]
        · unfold FlowAction.HasDebitSource
          simp [primaryDebitProvenance, hnonempty, hselector, hsTransfer,
            hsTransferCall, hsWithdraw, hsWithdrawTo]
        · exact htransfer

theorem Exec.Frame.hasRichLocalStorageEffect_of_withdraw
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = withdrawSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action := by
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
      have hsDeposit : withdrawSelector ≠ depositSelector := by
        decide +kernel
      have hsDepositTo : withdrawSelector ≠ depositToSelector := by
        decide +kernel
      have hsDepositCall :
          withdrawSelector ≠ depositToAndCallSelector := by
        decide +kernel
      have hsTransfer : withdrawSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          withdrawSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsTransferFrom : withdrawSelector ≠ transferFromSelector := by
        decide +kernel
      have hatom : primaryFlowAtom e = some
          (.redemption e.caller.toB256 e.caller e.caller
            (Sevm.argWord e 0).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
          hsDepositTo, hsDepositCall, hsTransfer, hsTransferCall,
          hsTransferFrom]
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
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = withdrawToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action := by
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
      have hsDeposit : withdrawToSelector ≠ depositSelector := by
        decide +kernel
      have hsDepositTo : withdrawToSelector ≠ depositToSelector := by
        decide +kernel
      have hsDepositCall :
          withdrawToSelector ≠ depositToAndCallSelector := by
        decide +kernel
      have hsTransfer : withdrawToSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          withdrawToSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsTransferFrom : withdrawToSelector ≠ transferFromSelector := by
        decide +kernel
      have hsWithdraw : withdrawToSelector ≠ withdrawSelector := by
        decide +kernel
      have hatom : primaryFlowAtom e = some
          (.redemption e.caller.toB256 e.caller
            (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
          hsDepositTo, hsDepositCall, hsTransfer, hsTransferCall,
          hsTransferFrom, hsWithdraw]
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
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = withdrawFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action := by
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
      have hsDeposit : withdrawFromSelector ≠ depositSelector := by
        decide +kernel
      have hsDepositTo : withdrawFromSelector ≠ depositToSelector := by
        decide +kernel
      have hsDepositCall :
          withdrawFromSelector ≠ depositToAndCallSelector := by
        decide +kernel
      have hsTransfer : withdrawFromSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          withdrawFromSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsTransferFrom : withdrawFromSelector ≠ transferFromSelector := by
        decide +kernel
      have hsWithdraw : withdrawFromSelector ≠ withdrawSelector := by
        decide +kernel
      have hsWithdrawTo : withdrawFromSelector ≠ withdrawToSelector := by
        decide +kernel
      have hatom : primaryFlowAtom e = some
          (.redemption (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            (Sevm.argWord e 1).toAdr (Sevm.argWord e 2).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
          hsDepositTo, hsDepositCall, hsTransfer, hsTransferCall,
          hsTransferFrom, hsWithdraw, hsWithdrawTo]
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
          simp [primaryDebitProvenance, hnonempty, hselector, hsTransfer,
            hsTransferCall, hsTransferFrom, hsWithdraw, hsWithdrawTo]
        · exact hprefix'.2.1
        · exact hprefix'.1
      · simpa only [hsource] using hprefix
      · simpa only [hsource] using htrace
      · exact Stor.Weth10Silent.rfl

theorem Exec.Frame.hasRichLocalStorageEffect_of_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action := by
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
      have hsDeposit : flashLoanSelector ≠ depositSelector := by
        decide +kernel
      have hsDepositTo : flashLoanSelector ≠ depositToSelector := by
        decide +kernel
      have hsDepositCall :
          flashLoanSelector ≠ depositToAndCallSelector := by
        decide +kernel
      have hsTransfer : flashLoanSelector ≠ transferSelector := by
        decide +kernel
      have hsTransferCall :
          flashLoanSelector ≠ transferAndCallSelector := by
        decide +kernel
      have hsTransferFrom : flashLoanSelector ≠ transferFromSelector := by
        decide +kernel
      have hsWithdraw : flashLoanSelector ≠ withdrawSelector := by
        decide +kernel
      have hsWithdrawTo : flashLoanSelector ≠ withdrawToSelector := by
        decide +kernel
      have hsWithdrawFrom : flashLoanSelector ≠ withdrawFromSelector := by
        decide +kernel
      have hatom : primaryFlowAtom e = some
          (.flashPair (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
            (Sevm.argWord e 2).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector, hsDeposit,
          hsDepositTo, hsDepositCall, hsTransfer, hsTransferCall,
          hsTransferFrom, hsWithdraw, hsWithdrawTo, hsWithdrawFrom]
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
          simp [primaryDebitProvenance, hnonempty, hselector, hsTransfer,
            hsTransferCall, hsTransferFrom, hsWithdraw, hsWithdrawTo,
            hsWithdrawFrom])
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
    (context : frame.AuthenticContext dp ca)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action := by
  by_cases hempty : frame.sevm.data.length.toB256 = 0
  · exact frame.hasRichLocalStorageEffect_of_receive context hempty haction
  have hnonempty : frame.sevm.data.length.toB256 ≠ 0 := hempty
  by_cases hdeposit : Sevm.selector frame.sevm = depositSelector
  · exact frame.hasRichLocalStorageEffect_of_deposit context hdeposit
      hnonempty haction
  by_cases hdepositTo : Sevm.selector frame.sevm = depositToSelector
  · exact frame.hasRichLocalStorageEffect_of_depositTo context hdepositTo
      hnonempty haction
  by_cases hdepositCall :
      Sevm.selector frame.sevm = depositToAndCallSelector
  · exact frame.hasRichLocalStorageEffect_of_depositToAndCall context
      hdepositCall hnonempty haction
  by_cases htransfer : Sevm.selector frame.sevm = transferSelector
  · exact frame.hasRichLocalStorageEffect_of_transfer context htransfer
      hnonempty haction
  by_cases htransferCall :
      Sevm.selector frame.sevm = transferAndCallSelector
  · exact frame.hasRichLocalStorageEffect_of_transferAndCall context
      htransferCall hnonempty haction
  by_cases htransferFrom :
      Sevm.selector frame.sevm = transferFromSelector
  · exact frame.hasRichLocalStorageEffect_of_transferFrom context
      htransferFrom hnonempty haction
  by_cases hwithdraw : Sevm.selector frame.sevm = withdrawSelector
  · exact frame.hasRichLocalStorageEffect_of_withdraw context hwithdraw
      hnonempty haction
  by_cases hwithdrawTo : Sevm.selector frame.sevm = withdrawToSelector
  · exact frame.hasRichLocalStorageEffect_of_withdrawTo context hwithdrawTo
      hnonempty haction
  by_cases hwithdrawFrom :
      Sevm.selector frame.sevm = withdrawFromSelector
  · exact frame.hasRichLocalStorageEffect_of_withdrawFrom context
      hwithdrawFrom hnonempty haction
  by_cases hflash : Sevm.selector frame.sevm = flashLoanSelector
  · exact frame.hasRichLocalStorageEffect_of_flashLoan context hflash
      hnonempty haction
  have hprimary : primaryFlowAtom frame.sevm = none := by
    simp [primaryFlowAtom, hnonempty, hdeposit, hdepositTo,
      hdepositCall, htransfer, htransferCall, htransferFrom, hwithdraw,
      hwithdrawTo, hwithdrawFrom, hflash]
  simp [Exec.Frame.flowAction?, context.invocation, hprimary] at haction

/-- Exhaustive compiled-program classifier for receive plus all 27 selector
leaves.  Nonempty successful calldata is first proved to have entered an
actual listed dispatch leaf; therefore the non-flow arm is not conditional on
an externally supplied recognition assumption. -/
theorem Exec.Frame.hasCompiledBalanceOwnEffect
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca) :
    frame.HasCompiledBalanceOwnEffect dp ca := by
  cases haction : frame.flowAction? dp ca with
  | some action =>
      exact .flow action
        (frame.hasRichLocalStorageEffect_of_flowAction?_eq_some
          context haction)
  | none =>
      by_cases hempty : frame.sevm.data.length.toB256 = 0
      · have hprimary : primaryFlowAtom frame.sevm ≠ none := by
          simp [primaryFlowAtom, hempty]
        unfold Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation] at haction
        cases hatom : primaryFlowAtom frame.sevm with
        | none => exact (hprimary hatom).elim
        | some atom => simp [hatom] at haction
      · exact .noFlow
          (frame.hasNoWethBalanceOwnEffect_of_recognized context haction
            (frame.recognizedSelector_of_nonempty context hempty))

/-- Identifier-safe alias for tooling that cannot parse `?` in declaration
names. -/
theorem Exec.Frame.hasRichLocalStorageEffect_of_classified
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasRichLocalStorageEffect dp ca action :=
  frame.hasRichLocalStorageEffect_of_flowAction?_eq_some context haction

/-- A classified authentic frame contributes its own action first, followed
by exactly the labels computed from the original proof-indexed proper
descendant traversal. -/
theorem Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (haction : frame.flowAction? dp ca = some action) :
    frame.ClassifiedActionLedger dp ca action := by
  refine ⟨frame.hasRichLocalStorageEffect_of_classified context haction, ?_⟩
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  have hroot : Exec.Frame.flowAction? dp ca
      (Exec.Frame.ofRun run committed) = some action := by
    exact haction
  simp [Exec.flowActions, Exec.committedFrames,
    Exec.Frame.descendantFlowActions, committed, hroot]

/-- Every executable flow classification of an authentic committed WETH10
frame is backed by the exact local balance segment executed by that frame.
Callback and ETH-send children are excluded from the existential endpoint;
their effects remain available through the raw functional boundaries used by
the selector-specific proofs above. -/
theorem Exec.Frame.hasLocalOwnEffect_of_flowAction?_eq_some
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasLocalOwnEffect ca action := by
  by_cases hempty : frame.sevm.data.length.toB256 = 0
  · exact frame.hasLocalOwnEffect_of_receive context hempty haction
  have hnonempty : frame.sevm.data.length.toB256 ≠ 0 := hempty
  by_cases hdeposit : Sevm.selector frame.sevm = depositSelector
  · exact frame.hasLocalOwnEffect_of_deposit context hdeposit hnonempty
      haction
  by_cases hdepositTo : Sevm.selector frame.sevm = depositToSelector
  · exact frame.hasLocalOwnEffect_of_depositTo context hdepositTo
      hnonempty haction
  by_cases hdepositCall :
      Sevm.selector frame.sevm = depositToAndCallSelector
  · exact frame.hasLocalOwnEffect_of_depositToAndCall context hdepositCall
      hnonempty haction
  by_cases htransfer : Sevm.selector frame.sevm = transferSelector
  · exact frame.hasLocalOwnEffect_of_transfer context htransfer hnonempty
      haction
  by_cases htransferCall :
      Sevm.selector frame.sevm = transferAndCallSelector
  · exact frame.hasLocalOwnEffect_of_transferAndCall context htransferCall
      hnonempty haction
  by_cases htransferFrom :
      Sevm.selector frame.sevm = transferFromSelector
  · exact frame.hasLocalOwnEffect_of_transferFrom context htransferFrom
      hnonempty haction
  by_cases hwithdraw : Sevm.selector frame.sevm = withdrawSelector
  · exact frame.hasLocalOwnEffect_of_withdraw context hwithdraw hnonempty
      haction
  by_cases hwithdrawTo : Sevm.selector frame.sevm = withdrawToSelector
  · exact frame.hasLocalOwnEffect_of_withdrawTo context hwithdrawTo
      hnonempty haction
  by_cases hwithdrawFrom :
      Sevm.selector frame.sevm = withdrawFromSelector
  · exact frame.hasLocalOwnEffect_of_withdrawFrom context hwithdrawFrom
      hnonempty haction
  by_cases hflash : Sevm.selector frame.sevm = flashLoanSelector
  · exact frame.hasLocalOwnEffect_of_flashLoan context hflash hnonempty
      haction
  have hprimary : primaryFlowAtom frame.sevm = none := by
    simp [primaryFlowAtom, hnonempty, hdeposit, hdepositTo,
      hdepositCall, htransfer, htransferCall, htransferFrom, hwithdraw,
      hwithdrawTo, hwithdrawFrom, hflash]
  simp [Exec.Frame.flowAction?, context.invocation, hprimary] at haction

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

/-- Literal SSTORE-node counts for the 27 public bodies, in the exact order of
`weth10Funcs`.  Shared called continuations are inventoried separately below. -/
theorem weth10Funcs_sourceSstoreSiteCounts (dp : DeployParams) :
    (weth10Funcs dp).map (fun entry => sourceSstoreSiteCount entry.2) =
      [0, 1, 0, 1, 1, 1, 0, 0, 0, 3, 2, 1, 0, 0, 0, 0, 0, 1,
        0, 3, 1, 1, 0, 1, 1, 0, 0] := by
  change (weth10Funcs (⟨0, 0⟩ : DeployParams)).map
    (fun entry => sourceSstoreSiteCount entry.2) = _
  decide +kernel

/-- Literal SSTORE-node counts for all 19 auxiliary bodies, in `weth10Aux`
order. -/
theorem weth10Aux_sourceSstoreSiteCounts :
    weth10Aux.map sourceSstoreSiteCount =
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 1, 2, 1] := by
  decide +kernel

theorem receiveEther_sourceSstoreSiteCount :
    sourceSstoreSiteCount receiveEther = 1 := by
  decide +kernel

end Weth10

end Blanc
