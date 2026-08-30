import Blanc.Weth10HolderFlowFlashChronology
import Blanc.Weth10HolderFlowPermitChronology
import Blanc.Weth10HolderFlowStorage
import Blanc.Weth10HolderFlowConservation
import Blanc.Weth10HolderFlowTransferAndCallChronology
import Blanc.Weth10HolderFlowSelectorFacts

/-!
Execution-level storage accounting for the retained WETH10 action ledger.

The relation below is deliberately operational: its endpoints are concrete
`Devm` states, and its labels are the exact action list computed from retained
execution frames.  Both equations keep modular credit loss explicit.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

private theorem exec_result_unique
    {pc : Nat} {sevm : Sevm} {pre : Devm}
    {leftOut rightOut : Execution}
    (left : Exec pc sevm pre leftOut)
    (right : Exec pc sevm pre rightOut) : leftOut = rightOut := by
  have hleft := (exec_iff_exec_eq pc sevm pre leftOut).mp ⟨left⟩
  have hright := (exec_iff_exec_eq pc sevm pre rightOut).mp ⟨right⟩
  exact hleft.symm.trans hright

private theorem exec_unique
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (left right : Exec pc sevm pre out) : left = right := by
  induction left <;> cases right <;> simp_all <;>
    aesop (add safe forward exec_result_unique)

/-- Proof-indexed retained traversals are independent of which concrete
`Exec` witness was recovered from a `RunCompiled` callback slot. -/
theorem Exec.flowActions_eq_of_runs
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (left right : Exec pc sevm pre out) :
    Blanc.Weth10.Exec.flowActions dp ca left =
      Blanc.Weth10.Exec.flowActions dp ca right := by
  rw [exec_unique left right]

/-- The action labels contributed by committed proper descendants, excluding
the enclosing root frame. -/
def Exec.descendantActions (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List FlowAction :=
  (Exec.descendantFrames run).filterMap
    (Blanc.Weth10.Exec.Frame.flowAction? dp ca)

/-- On a committed execution, the retained action traversal is the optional
root action followed by the proper descendants. -/
theorem Exec.flowActions_eq_root_append_descendants
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hcommits : Execution.commits out = true) :
    Exec.flowActions dp ca run =
      (Blanc.Weth10.Exec.Frame.flowAction? dp ca
        (Exec.Frame.ofRun run hcommits)).toList ++
        Exec.descendantActions dp ca run := by
  unfold Exec.flowActions Exec.descendantActions Exec.committedFrames
  simp only [dif_pos hcommits, List.filterMap_cons, Option.toList]
  cases Blanc.Weth10.Exec.Frame.flowAction? dp ca
      (Exec.Frame.ofRun run hcommits) <;> rfl

/-- In a successful spawned step, descendant actions split into the child
traversal exactly when the complete message-frame settlement is clean, followed
by the continuation descendants.  This extra settlement check prunes CREATE
code-deposit rollback even when the raw constructor execution was clean. -/
theorem Exec.descendantActions_runOk
    {dp : DeployParams} {ca : Adr}
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {f : Jaune.Frame} {rsm : Resume}
    {cevm : Evm} {raw out : Execution}
    (hstep : Jaune.Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (next : Exec pc' sevm devm' out) :
    Exec.descendantActions dp ca
        (Exec.runOk hstep henter child hr next) =
      (if _h : Blanc.Frame.settlementCommits f raw = true then
        Exec.flowActions dp ca child
       else []) ++ Exec.descendantActions dp ca next := by
  unfold Exec.descendantActions Exec.flowActions
  simp only [Exec.descendantFrames, Exec.committedFrames,
    List.filterMap_append]
  by_cases hs : Blanc.Frame.settlementCommits f raw = true
  · have hc : Execution.commits raw = true :=
      Blanc.Frame.raw_commits_of_settlementCommits hs
    simp only [dif_pos hs, dif_pos hc]
  · simp only [dif_neg hs, List.filterMap_nil, List.nil_append]

/-- Exact wrap-aware balance-storage accounting for a labelled execution
segment.  The holder equation retains self-transfer on both sides; the supply
equation projects the same actions through `supplyFlowOfActions`. -/
structure StorageFlowAccounting (ca : Adr) (pre post : Devm)
    (actions : List FlowAction) : Prop where
  holderEquation : ∀ u : Adr,
    (Stor.rest (Devm.getStor pre ca) u).toNat +
          (holderFlowOfActions actions u).ordinaryIn +
          (holderFlowOfActions actions u).selfTransfer +
          (holderFlowOfActions actions u).flashCredit =
      (Stor.rest (Devm.getStor post ca) u).toNat +
          (holderFlowOfActions actions u).redeemed +
          (holderFlowOfActions actions u).externalTransferredOut +
          (holderFlowOfActions actions u).selfTransfer +
          (holderFlowOfActions actions u).flashRepayment +
          holderCreditLossOfActions actions u
  supplyEquation :
    balSum (Devm.getStor pre ca) +
          (supplyFlowOfActions actions).ordinaryIn +
          (supplyFlowOfActions actions).flashCredit =
      balSum (Devm.getStor post ca) +
          (supplyFlowOfActions actions).redeemed +
          (supplyFlowOfActions actions).flashRepayment +
          creditLossOfActions actions

/-- Canonical segment labels owned by one action.  Flash contributes two
labels because its credit and repayment surround the callback execution. -/
def FlowAction.localSegmentLabels (action : FlowAction) :
    List (LocalSegmentKind × FlowAction) :=
  match action.atom with
  | .ordinaryMint .. => [(.ordinaryMint, action)]
  | .transfer .. => [(.ordinaryTransfer, action)]
  | .redemption .. => [(.redemption, action)]
  | .flashPair .. => [(.flashCredit, action), (.flashRepayment, action)]

def localSegmentLabelsOfActions (actions : List FlowAction) :
    List (LocalSegmentKind × FlowAction) :=
  actions.flatMap FlowAction.localSegmentLabels

/-- The only atom/credit combination for which the canonical local labels do
not themselves count a credit is redemption.  Exact redemption segments prove
this property from their concrete `credit = none` witness. -/
def FlowAction.CreditShape (action : FlowAction) : Prop :=
  match action.atom with
  | .redemption .. => action.credit = none
  | _ => True

theorem LocalActionSegment.creditShape
    {kind : LocalSegmentKind} {action : FlowAction}
    {pre post : HolderBalances}
    (segment : LocalActionSegment kind action pre post) :
    action.CreditShape := by
  cases segment <;>
    simp_all [FlowAction.CreditShape]

theorem FlowAction.localSegmentsHolderIn_eq
    (action : FlowAction) (u : Adr) :
    localSegmentsHolderIn action.localSegmentLabels u =
      (action.atom.holderFlow u).ordinaryIn +
        (action.atom.holderFlow u).selfTransfer +
        (action.atom.holderFlow u).flashCredit := by
  rcases action with ⟨atom, credit, debit, actualCaller, currentTarget,
    codeAddress, depth⟩
  cases atom <;>
    simp [FlowAction.localSegmentLabels, localSegmentsHolderIn,
      LocalSegmentKind.holderIn, FlowAtom.holderFlow, HolderFlow.zero] <;>
    aesop

theorem FlowAction.localSegmentsHolderOut_eq
    (action : FlowAction) (u : Adr) :
    localSegmentsHolderOut action.localSegmentLabels u =
      (action.atom.holderFlow u).redeemed +
        (action.atom.holderFlow u).externalTransferredOut +
        (action.atom.holderFlow u).selfTransfer +
        (action.atom.holderFlow u).flashRepayment := by
  rcases action with ⟨atom, credit, debit, actualCaller, currentTarget,
    codeAddress, depth⟩
  cases atom <;>
    simp [FlowAction.localSegmentLabels, localSegmentsHolderOut,
      LocalSegmentKind.holderOut, FlowAtom.holderFlow, HolderFlow.zero] <;>
    aesop

theorem FlowAction.localSegmentsHolderLoss_eq
    (action : FlowAction) (u : Adr) (shape : action.CreditShape) :
    localSegmentsHolderLoss action.localSegmentLabels u =
      action.holderCreditLoss u := by
  rcases action with ⟨atom, credit, debit, actualCaller, currentTarget,
    codeAddress, depth⟩
  cases atom <;> cases credit <;>
    simp_all [FlowAction.CreditShape, FlowAction.localSegmentLabels,
      localSegmentsHolderLoss, LocalSegmentKind.holderLoss,
      FlowAction.holderCreditLoss]

theorem FlowAction.localSegmentsBookedIn_eq (action : FlowAction) :
    localSegmentsBookedIn action.localSegmentLabels =
      action.atom.supplyFlow.ordinaryIn +
        action.atom.supplyFlow.flashCredit := by
  rcases action with ⟨atom, credit, debit, actualCaller, currentTarget,
    codeAddress, depth⟩
  cases atom <;>
    simp [FlowAction.localSegmentLabels, localSegmentsBookedIn,
      LocalSegmentKind.bookedIn, FlowAtom.supplyFlow, SupplyFlow.zero]

theorem FlowAction.localSegmentsBookedOut_eq (action : FlowAction) :
    localSegmentsBookedOut action.localSegmentLabels =
      action.atom.supplyFlow.redeemed +
        action.atom.supplyFlow.flashRepayment := by
  rcases action with ⟨atom, credit, debit, actualCaller, currentTarget,
    codeAddress, depth⟩
  cases atom <;>
    simp [FlowAction.localSegmentLabels, localSegmentsBookedOut,
      LocalSegmentKind.bookedOut, FlowAtom.supplyFlow, SupplyFlow.zero]

theorem FlowAction.localSegmentsBookedLoss_eq (action : FlowAction) :
    action.CreditShape →
    localSegmentsBookedLoss action.localSegmentLabels =
      action.creditLossTotal := by
  intro shape
  rcases action with ⟨atom, credit, debit, actualCaller, currentTarget,
    codeAddress, depth⟩
  cases atom <;> cases credit <;>
    simp_all [FlowAction.CreditShape, FlowAction.localSegmentLabels,
      localSegmentsBookedLoss,
      LocalSegmentKind.bookedLoss, FlowAction.bookedCreditLoss,
      FlowAction.creditLossTotal]

@[simp] theorem localSegmentsHolderIn_append
    (left right : List (LocalSegmentKind × FlowAction)) (u : Adr) :
    localSegmentsHolderIn (left ++ right) u =
      localSegmentsHolderIn left u + localSegmentsHolderIn right u := by
  simp [localSegmentsHolderIn]

@[simp] theorem localSegmentsHolderOut_append
    (left right : List (LocalSegmentKind × FlowAction)) (u : Adr) :
    localSegmentsHolderOut (left ++ right) u =
      localSegmentsHolderOut left u + localSegmentsHolderOut right u := by
  simp [localSegmentsHolderOut]

@[simp] theorem localSegmentsHolderLoss_append
    (left right : List (LocalSegmentKind × FlowAction)) (u : Adr) :
    localSegmentsHolderLoss (left ++ right) u =
      localSegmentsHolderLoss left u + localSegmentsHolderLoss right u := by
  simp [localSegmentsHolderLoss]

@[simp] theorem localSegmentsBookedIn_append
    (left right : List (LocalSegmentKind × FlowAction)) :
    localSegmentsBookedIn (left ++ right) =
      localSegmentsBookedIn left + localSegmentsBookedIn right := by
  simp [localSegmentsBookedIn]

@[simp] theorem localSegmentsBookedOut_append
    (left right : List (LocalSegmentKind × FlowAction)) :
    localSegmentsBookedOut (left ++ right) =
      localSegmentsBookedOut left + localSegmentsBookedOut right := by
  simp [localSegmentsBookedOut]

@[simp] theorem localSegmentsBookedLoss_append
    (left right : List (LocalSegmentKind × FlowAction)) :
    localSegmentsBookedLoss (left ++ right) =
      localSegmentsBookedLoss left + localSegmentsBookedLoss right := by
  simp [localSegmentsBookedLoss]

@[simp] theorem holderFlowOfActions_singleton
    (action : FlowAction) (u : Adr) :
    holderFlowOfActions [action] u = action.atom.holderFlow u := by
  simp [holderFlowOfActions]

@[simp] theorem supplyFlowOfActions_singleton (action : FlowAction) :
    supplyFlowOfActions [action] = action.atom.supplyFlow := by
  simp [supplyFlowOfActions, SupplyFlow.zero, SupplyFlow.add]

theorem localSegmentsHolderIn_labels_eq
    (actions : List FlowAction) (u : Adr) :
    localSegmentsHolderIn (localSegmentLabelsOfActions actions) u =
      (holderFlowOfActions actions u).ordinaryIn +
        (holderFlowOfActions actions u).selfTransfer +
        (holderFlowOfActions actions u).flashCredit := by
  induction actions with
  | nil =>
      simp [localSegmentLabelsOfActions, localSegmentsHolderIn,
        holderFlowOfActions, HolderFlow.zero]
  | cons action actions ih =>
      rw [show localSegmentLabelsOfActions (action :: actions) =
        action.localSegmentLabels ++ localSegmentLabelsOfActions actions by
          rfl]
      rw [localSegmentsHolderIn_append,
        action.localSegmentsHolderIn_eq, ih]
      have hflow := holderFlowOfActions_append [action] actions u
      simp only [List.singleton_append] at hflow
      rw [hflow]
      simp only [holderFlowOfActions_singleton, HolderFlow.add]
      omega

theorem localSegmentsHolderOut_labels_eq
    (actions : List FlowAction) (u : Adr) :
    localSegmentsHolderOut (localSegmentLabelsOfActions actions) u =
      (holderFlowOfActions actions u).redeemed +
        (holderFlowOfActions actions u).externalTransferredOut +
        (holderFlowOfActions actions u).selfTransfer +
        (holderFlowOfActions actions u).flashRepayment := by
  induction actions with
  | nil =>
      simp [localSegmentLabelsOfActions, localSegmentsHolderOut,
        holderFlowOfActions, HolderFlow.zero]
  | cons action actions ih =>
      rw [show localSegmentLabelsOfActions (action :: actions) =
        action.localSegmentLabels ++ localSegmentLabelsOfActions actions by
          rfl]
      rw [localSegmentsHolderOut_append,
        action.localSegmentsHolderOut_eq, ih]
      have hflow := holderFlowOfActions_append [action] actions u
      simp only [List.singleton_append] at hflow
      rw [hflow]
      simp only [holderFlowOfActions_singleton, HolderFlow.add]
      omega

@[simp] theorem SupplyFlow.zero_add (flow : SupplyFlow) :
    SupplyFlow.zero.add flow = flow := by
  cases flow
  simp [SupplyFlow.zero, SupplyFlow.add]

@[simp] theorem SupplyFlow.add_zero (flow : SupplyFlow) :
    flow.add SupplyFlow.zero = flow := by
  cases flow
  simp [SupplyFlow.zero, SupplyFlow.add]

theorem SupplyFlow.add_assoc (left middle right : SupplyFlow) :
    (left.add middle).add right = left.add (middle.add right) := by
  cases left
  cases middle
  cases right
  simp [SupplyFlow.add, Nat.add_assoc]

private theorem supplyFlowOfActions_from_eq_add
    (actions : List FlowAction) (initial : SupplyFlow) :
    actions.foldl (fun total action =>
      total.add action.atom.supplyFlow) initial =
    initial.add (supplyFlowOfActions actions) := by
  unfold supplyFlowOfActions
  induction actions generalizing initial with
  | nil => simp
  | cons action actions ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rw [ih (initial := SupplyFlow.zero.add action.atom.supplyFlow)]
      rw [SupplyFlow.zero_add, SupplyFlow.add_assoc]

theorem supplyFlowOfActions_append (left right : List FlowAction) :
    supplyFlowOfActions (left ++ right) =
      (supplyFlowOfActions left).add (supplyFlowOfActions right) := by
  unfold supplyFlowOfActions
  rw [List.foldl_append]
  exact supplyFlowOfActions_from_eq_add right _

@[simp] theorem holderCreditLossOfActions_append
    (left right : List FlowAction) (u : Adr) :
    holderCreditLossOfActions (left ++ right) u =
      holderCreditLossOfActions left u +
        holderCreditLossOfActions right u := by
  simp [holderCreditLossOfActions]

@[simp] theorem creditLossOfActions_append
    (left right : List FlowAction) :
    creditLossOfActions (left ++ right) =
      creditLossOfActions left + creditLossOfActions right := by
  simp [creditLossOfActions]

theorem localSegmentsHolderLoss_labels_eq
    (actions : List FlowAction) (u : Adr)
    (shape : ∀ action ∈ actions, action.CreditShape) :
    localSegmentsHolderLoss (localSegmentLabelsOfActions actions) u =
      holderCreditLossOfActions actions u := by
  induction actions with
  | nil =>
      simp [localSegmentLabelsOfActions, localSegmentsHolderLoss,
        holderCreditLossOfActions]
  | cons action actions ih =>
      have hhead : action.CreditShape := shape action (by simp)
      have htail : ∀ tail ∈ actions, tail.CreditShape := by
        intro tail hmem
        exact shape tail (by simp [hmem])
      rw [show localSegmentLabelsOfActions (action :: actions) =
        action.localSegmentLabels ++ localSegmentLabelsOfActions actions by
          rfl]
      rw [localSegmentsHolderLoss_append,
        action.localSegmentsHolderLoss_eq u hhead, ih htail]
      simp [holderCreditLossOfActions]

theorem localSegmentsBookedIn_labels_eq (actions : List FlowAction) :
    localSegmentsBookedIn (localSegmentLabelsOfActions actions) =
      (supplyFlowOfActions actions).ordinaryIn +
        (supplyFlowOfActions actions).flashCredit := by
  induction actions with
  | nil =>
      simp [localSegmentLabelsOfActions, localSegmentsBookedIn,
        supplyFlowOfActions, SupplyFlow.zero]
  | cons action actions ih =>
      rw [show localSegmentLabelsOfActions (action :: actions) =
        action.localSegmentLabels ++ localSegmentLabelsOfActions actions by
          rfl]
      rw [localSegmentsBookedIn_append,
        action.localSegmentsBookedIn_eq, ih]
      have hflow := supplyFlowOfActions_append [action] actions
      simp only [List.singleton_append] at hflow
      rw [hflow]
      simp only [supplyFlowOfActions_singleton, SupplyFlow.add]
      omega

theorem localSegmentsBookedOut_labels_eq (actions : List FlowAction) :
    localSegmentsBookedOut (localSegmentLabelsOfActions actions) =
      (supplyFlowOfActions actions).redeemed +
        (supplyFlowOfActions actions).flashRepayment := by
  induction actions with
  | nil =>
      simp [localSegmentLabelsOfActions, localSegmentsBookedOut,
        supplyFlowOfActions, SupplyFlow.zero]
  | cons action actions ih =>
      rw [show localSegmentLabelsOfActions (action :: actions) =
        action.localSegmentLabels ++ localSegmentLabelsOfActions actions by
          rfl]
      rw [localSegmentsBookedOut_append,
        action.localSegmentsBookedOut_eq, ih]
      have hflow := supplyFlowOfActions_append [action] actions
      simp only [List.singleton_append] at hflow
      rw [hflow]
      simp only [supplyFlowOfActions_singleton, SupplyFlow.add]
      omega

theorem localSegmentsBookedLoss_labels_eq (actions : List FlowAction)
    (shape : ∀ action ∈ actions, action.CreditShape) :
    localSegmentsBookedLoss (localSegmentLabelsOfActions actions) =
      creditLossOfActions actions := by
  induction actions with
  | nil =>
      simp [localSegmentLabelsOfActions, localSegmentsBookedLoss,
        creditLossOfActions]
  | cons action actions ih =>
      have hhead : action.CreditShape := shape action (by simp)
      have htail : ∀ tail ∈ actions, tail.CreditShape := by
        intro tail hmem
        exact shape tail (by simp [hmem])
      rw [show localSegmentLabelsOfActions (action :: actions) =
        action.localSegmentLabels ++ localSegmentLabelsOfActions actions by
          rfl]
      rw [localSegmentsBookedLoss_append,
        action.localSegmentsBookedLoss_eq hhead, ih htail]
      simp [creditLossOfActions]

private theorem sum_map_eq_of_perm {alpha : Type}
    (f : alpha → Nat) {left right : List alpha}
    (h : left.Perm right) :
    (left.map f).sum = (right.map f).sum := by
  induction h with
  | nil => rfl
  | cons head perm ih => simp [ih]
  | swap left right tail =>
      simp only [List.map_cons, List.sum_cons]
      ac_rfl
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- A chronological exact segment chain accounts for its action ledger as
soon as its labels are a permutation of the canonical owned segments.  The
permutation is essential for flash: callback segments occur between the
parent's credit and repayment, while `Exec.flowActions` lists the parent first.
-/
theorem StorageFlowAccounting.of_localSegmentChain
    {ca : Adr} {pre post : Devm} {actions : List FlowAction}
    {segments : List (LocalSegmentKind × FlowAction)}
    (chain : LocalSegmentChain segments
      (Stor.rest (Devm.getStor pre ca))
      (Stor.rest (Devm.getStor post ca)))
    (labels : segments.Perm (localSegmentLabelsOfActions actions))
    (shape : ∀ action ∈ actions, action.CreditShape) :
    StorageFlowAccounting ca pre post actions := by
  constructor
  · intro u
    have equation := chain.holder_eq u
    have hin : localSegmentsHolderIn segments u =
        (holderFlowOfActions actions u).ordinaryIn +
          (holderFlowOfActions actions u).selfTransfer +
          (holderFlowOfActions actions u).flashCredit := by
      calc
        localSegmentsHolderIn segments u =
            localSegmentsHolderIn
              (localSegmentLabelsOfActions actions) u := by
          simpa [localSegmentsHolderIn] using
            sum_map_eq_of_perm
              (fun segment => segment.1.holderIn segment.2 u) labels
        _ = _ := localSegmentsHolderIn_labels_eq actions u
    have hout : localSegmentsHolderOut segments u =
        (holderFlowOfActions actions u).redeemed +
          (holderFlowOfActions actions u).externalTransferredOut +
          (holderFlowOfActions actions u).selfTransfer +
          (holderFlowOfActions actions u).flashRepayment := by
      calc
        localSegmentsHolderOut segments u =
            localSegmentsHolderOut
              (localSegmentLabelsOfActions actions) u := by
          simpa [localSegmentsHolderOut] using
            sum_map_eq_of_perm
              (fun segment => segment.1.holderOut segment.2 u) labels
        _ = _ := localSegmentsHolderOut_labels_eq actions u
    have hloss : localSegmentsHolderLoss segments u =
        holderCreditLossOfActions actions u := by
      calc
        localSegmentsHolderLoss segments u =
            localSegmentsHolderLoss
              (localSegmentLabelsOfActions actions) u := by
          simpa [localSegmentsHolderLoss] using
            sum_map_eq_of_perm
              (fun segment => segment.1.holderLoss segment.2 u) labels
        _ = _ := localSegmentsHolderLoss_labels_eq actions u shape
    rw [hin, hout, hloss] at equation
    omega

  · have equation := chain.balSum_eq
    have hin : localSegmentsBookedIn segments =
        (supplyFlowOfActions actions).ordinaryIn +
          (supplyFlowOfActions actions).flashCredit := by
      calc
        localSegmentsBookedIn segments =
            localSegmentsBookedIn
              (localSegmentLabelsOfActions actions) := by
          simpa [localSegmentsBookedIn] using
            sum_map_eq_of_perm
              (fun segment => segment.1.bookedIn segment.2) labels
        _ = _ := localSegmentsBookedIn_labels_eq actions
    have hout : localSegmentsBookedOut segments =
        (supplyFlowOfActions actions).redeemed +
          (supplyFlowOfActions actions).flashRepayment := by
      calc
        localSegmentsBookedOut segments =
            localSegmentsBookedOut
              (localSegmentLabelsOfActions actions) := by
          simpa [localSegmentsBookedOut] using
            sum_map_eq_of_perm
              (fun segment => segment.1.bookedOut segment.2) labels
        _ = _ := localSegmentsBookedOut_labels_eq actions
    have hloss : localSegmentsBookedLoss segments =
        creditLossOfActions actions := by
      calc
        localSegmentsBookedLoss segments =
            localSegmentsBookedLoss
              (localSegmentLabelsOfActions actions) := by
          simpa [localSegmentsBookedLoss] using
            sum_map_eq_of_perm
              (fun segment => segment.1.bookedLoss segment.2) labels
        _ = _ := localSegmentsBookedLoss_labels_eq actions shape
    rw [hin, hout, hloss] at equation
    omega

theorem LocalSegmentChain.append
    {left right : List (LocalSegmentKind × FlowAction)}
    {pre middle post : HolderBalances}
    (hleft : LocalSegmentChain left pre middle)
    (hright : LocalSegmentChain right middle post) :
    LocalSegmentChain (left ++ right) pre post := by
  induction hleft with
  | nil balances => exact hright
  | cons head rest ih => exact .cons head (ih hright)

/-- Monoid-labelled operational storage delta.  Unlike
`StorageFlowAccounting`, this retains every exact local segment and therefore
contains no supplied endpoint equation. -/
structure StorageSegmentDelta (ca : Adr) (pre post : Devm)
    (actions : List FlowAction) : Type where
  segments : List (LocalSegmentKind × FlowAction)
  chain : LocalSegmentChain segments
    (Stor.rest (Devm.getStor pre ca))
    (Stor.rest (Devm.getStor post ca))
  labels : segments.Perm (localSegmentLabelsOfActions actions)
  creditShape : ∀ action ∈ actions, action.CreditShape

def StorageSegmentDelta.refl (ca : Adr) (state : Devm) :
    StorageSegmentDelta ca state state [] :=
  ⟨[], .nil _, .refl [], by simp⟩

def StorageSegmentDelta.of_rest_eq
    {ca : Adr} {pre post : Devm}
    (h : Stor.rest (Devm.getStor pre ca) =
      Stor.rest (Devm.getStor post ca)) :
    StorageSegmentDelta ca pre post [] := by
  refine ⟨[], ?_, .refl [], by simp⟩
  rw [h]
  exact .nil _

def StorageSegmentDelta.of_weth10Silent
    {ca : Adr} {pre post : Devm}
    (silent : Stor.Weth10Silent
      (Devm.getStor pre ca) (Devm.getStor post ca)) :
    StorageSegmentDelta ca pre post [] :=
  StorageSegmentDelta.of_rest_eq silent.1

def StorageSegmentDelta.of_getStor_eq
    {ca : Adr} {pre post : Devm}
    (h : Devm.getStor pre ca = Devm.getStor post ca) :
    StorageSegmentDelta ca pre post [] :=
  StorageSegmentDelta.of_rest_eq (congrArg Stor.rest h)

def StorageSegmentDelta.append
    {ca : Adr} {pre middle post : Devm}
    {leftActions rightActions : List FlowAction}
    (left : StorageSegmentDelta ca pre middle leftActions)
    (right : StorageSegmentDelta ca middle post rightActions) :
    StorageSegmentDelta ca pre post (leftActions ++ rightActions) := by
  refine ⟨left.segments ++ right.segments,
    left.chain.append right.chain, ?_, ?_⟩
  · simpa [localSegmentLabelsOfActions] using
      left.labels.append right.labels
  · intro action hmem
    rcases List.mem_append.mp hmem with hleft | hright
    · exact left.creditShape action hleft
    · exact right.creditShape action hright

def StorageSegmentDelta.silentSurround
    {ca : Adr} {pre childPre childPost post : Devm}
    {children : List FlowAction}
    (entrySilent : Stor.Weth10Silent
      (Devm.getStor pre ca) (Devm.getStor childPre ca))
    (child : StorageSegmentDelta ca childPre childPost children)
    (exitSilent : Stor.Weth10Silent
      (Devm.getStor childPost ca) (Devm.getStor post ca)) :
    StorageSegmentDelta ca pre post children := by
  simpa only [List.nil_append, List.append_nil] using
    (StorageSegmentDelta.of_weth10Silent entrySilent).append
      (child.append (StorageSegmentDelta.of_weth10Silent exitSilent))

/-- A contiguous ordinary local segment is the complete delta for its one
action.  The label equality excludes using this constructor for only half of
a flash action. -/
def StorageSegmentDelta.singleton
    {ca : Adr} {pre post : Devm} {action : FlowAction}
    {kind : LocalSegmentKind}
    (segment : LocalActionSegment kind action
      (Stor.rest (Devm.getStor pre ca))
      (Stor.rest (Devm.getStor post ca)))
    (label : action.localSegmentLabels = [(kind, action)]) :
    StorageSegmentDelta ca pre post [action] := by
  refine ⟨[(kind, action)], .cons segment (.nil _), ?_, ?_⟩
  · simp [localSegmentLabelsOfActions, label]
  · intro candidate hmem
    simp only [List.mem_singleton] at hmem
    subst candidate
    exact segment.creditShape

def StorageSegmentDelta.ofOrdinaryMint
    {ca : Adr} {pre post : Devm} {action : FlowAction}
    (segment : LocalActionSegment .ordinaryMint action
      (Stor.rest (Devm.getStor pre ca))
      (Stor.rest (Devm.getStor post ca))) :
    StorageSegmentDelta ca pre post [action] := by
  apply StorageSegmentDelta.singleton segment
  cases segment with
  | ordinaryMint rawRecipient recipient amountWord atom_eq credit_eq
      debit_eq increase =>
      simp [FlowAction.localSegmentLabels, atom_eq]

def StorageSegmentDelta.ofOrdinaryTransfer
    {ca : Adr} {pre post : Devm} {action : FlowAction}
    (segment : LocalActionSegment .ordinaryTransfer action
      (Stor.rest (Devm.getStor pre ca))
      (Stor.rest (Devm.getStor post ca))) :
    StorageSegmentDelta ca pre post [action] := by
  apply StorageSegmentDelta.singleton segment
  cases segment with
  | ordinaryTransfer rawSource rawRecipient source recipient amountWord
      atom_eq transfer credit_eq debit_source =>
      simp [FlowAction.localSegmentLabels, atom_eq]

def StorageSegmentDelta.ofRedemption
    {ca : Adr} {pre post : Devm} {action : FlowAction}
    (segment : LocalActionSegment .redemption action
      (Stor.rest (Devm.getStor pre ca))
      (Stor.rest (Devm.getStor post ca))) :
    StorageSegmentDelta ca pre post [action] := by
  apply StorageSegmentDelta.singleton segment
  cases segment with
  | redemption rawSource source ethRecipient amountWord atom_eq credit_eq
      debit_source amount_le decrease =>
      simp [FlowAction.localSegmentLabels, atom_eq]

/-- A flash action surrounds the arbitrary committed callback delta with its
own mint and repayment segments.  The resulting chronological labels are a
permutation of the parent-first retained action ledger. -/
def StorageSegmentDelta.flashSurround
    {ca : Adr} {pre callbackPre callbackPost post : Devm}
    {action : FlowAction} {children : List FlowAction}
    (mint : LocalActionSegment .flashCredit action
      (Stor.rest (Devm.getStor pre ca))
      (Stor.rest (Devm.getStor callbackPre ca)))
    (callback : StorageSegmentDelta ca callbackPre callbackPost children)
    (repayment : LocalActionSegment .flashRepayment action
      (Stor.rest (Devm.getStor callbackPost ca))
      (Stor.rest (Devm.getStor post ca)))
    (label : action.localSegmentLabels =
      [(.flashCredit, action), (.flashRepayment, action)]) :
    StorageSegmentDelta ca pre post (action :: children) := by
  refine ⟨(.flashCredit, action) ::
      callback.segments ++ [(.flashRepayment, action)],
    .cons mint
      (callback.chain.append (.cons repayment (.nil _))), ?_, ?_⟩
  · rw [show localSegmentLabelsOfActions (action :: children) =
      action.localSegmentLabels ++ localSegmentLabelsOfActions children by rfl,
      label]
    apply List.Perm.cons _
    apply (callback.labels.append (.refl _)).trans
    exact (List.perm_append_comm :
        (localSegmentLabelsOfActions children ++
            [(LocalSegmentKind.flashRepayment, action)]).Perm
          ([(LocalSegmentKind.flashRepayment, action)] ++
            localSegmentLabelsOfActions children))
  · intro candidate hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hchild
    · exact mint.creditShape
    · exact callback.creditShape candidate hchild

/-- Constructor-oriented flash composition; the mint witness itself pins the
canonical two labels, so callers need not repeat that metadata equation. -/
def StorageSegmentDelta.ofFlashSegments
    {ca : Adr} {pre callbackPre callbackPost post : Devm}
    {action : FlowAction} {children : List FlowAction}
    (mint : LocalActionSegment .flashCredit action
      (Stor.rest (Devm.getStor pre ca))
      (Stor.rest (Devm.getStor callbackPre ca)))
    (callback : StorageSegmentDelta ca callbackPre callbackPost children)
    (repayment : LocalActionSegment .flashRepayment action
      (Stor.rest (Devm.getStor callbackPost ca))
      (Stor.rest (Devm.getStor post ca))) :
    StorageSegmentDelta ca pre post (action :: children) := by
  apply StorageSegmentDelta.flashSurround mint callback repayment
  cases mint with
  | flashCredit rawReceiver receiver amountWord atom_eq credit_eq
      debit_source increase =>
      simp [FlowAction.localSegmentLabels, atom_eq]

theorem StorageSegmentDelta.storageFlowAccounting
    {ca : Adr} {pre post : Devm} {actions : List FlowAction}
    (delta : StorageSegmentDelta ca pre post actions) :
    StorageFlowAccounting ca pre post actions :=
  StorageFlowAccounting.of_localSegmentChain delta.chain delta.labels
    delta.creditShape

/-- The recursive storage result carries code preservation separately from
holder accounting.  This is needed to feed the installed-code premise to a
later sibling or continuation; it is not inferred from balance/storage
equations. -/
structure StorageSegmentEffect (ca : Adr) (pre post : Devm)
    (actions : List FlowAction) : Type where
  delta : StorageSegmentDelta ca pre post actions
  codeEq : pre.getCode ca = post.getCode ca

def StorageSegmentEffect.refl (ca : Adr) (state : Devm) :
    StorageSegmentEffect ca state state [] :=
  ⟨StorageSegmentDelta.refl ca state, rfl⟩

def StorageSegmentEffect.of_getStorCode_eq
    {ca : Adr} {pre post : Devm}
    (hstorage : Devm.getStor pre ca = Devm.getStor post ca)
    (hcode : pre.getCode ca = post.getCode ca) :
    StorageSegmentEffect ca pre post [] :=
  ⟨StorageSegmentDelta.of_getStor_eq hstorage, hcode⟩

def StorageSegmentEffect.append
    {ca : Adr} {pre middle post : Devm}
    {leftActions rightActions : List FlowAction}
    (left : StorageSegmentEffect ca pre middle leftActions)
    (right : StorageSegmentEffect ca middle post rightActions) :
    StorageSegmentEffect ca pre post (leftActions ++ rightActions) :=
  ⟨left.delta.append right.delta, left.codeEq.trans right.codeEq⟩

/-- Contract-specific local segments composed with already-accounted retained
children.  The only list hypotheses are chronology equations for the actual
proper-descendant ledger; no endpoint balance equation is admitted. -/
inductive RichStorageAccounting (ca : Adr) (pre post : Devm)
    (action : FlowAction) (descendants : List FlowAction) : Prop
  | ordinaryMint
      (segment : LocalActionSegment .ordinaryMint action
        (Stor.rest (Devm.getStor pre ca))
        (Stor.rest (Devm.getStor post ca)))
      (chronology : descendants = [])
  | ordinaryTransfer
      (segment : LocalActionSegment .ordinaryTransfer action
        (Stor.rest (Devm.getStor pre ca))
        (Stor.rest (Devm.getStor post ca)))
      (chronology : descendants = [])
  | redemption
      {callPre guardPost : Devm} {children : List FlowAction}
      (segment : LocalActionSegment .redemption action
        (Stor.rest (Devm.getStor pre ca))
        (Stor.rest (Devm.getStor callPre ca)))
      (callback : StorageSegmentDelta ca callPre guardPost children)
      (suffix : Stor.Weth10Silent
        (Devm.getStor guardPost ca) (Devm.getStor post ca))
      (chronology : descendants = children)
  | tokenCallback
      {callbackPre : Devm} {children : List FlowAction}
      (own : StorageSegmentDelta ca pre callbackPre [action])
      (callback : StorageSegmentDelta ca callbackPre post children)
      (chronology : descendants = children)
  | redemptionThenTokenCallback
      {callPre callbackPre : Devm}
      {valueChildren callbackChildren : List FlowAction}
      (segment : LocalActionSegment .redemption action
        (Stor.rest (Devm.getStor pre ca))
        (Stor.rest (Devm.getStor callPre ca)))
      (valueCallback : StorageSegmentDelta ca callPre callbackPre
        valueChildren)
      (tokenCallback : StorageSegmentDelta ca callbackPre post
        callbackChildren)
      (chronology : descendants = valueChildren ++ callbackChildren)
  | flash
      {creditPost callbackPost settlePre debitPre : Devm}
      {children : List FlowAction}
      (credit : LocalActionSegment .flashCredit action
        (Stor.rest (Devm.getStor pre ca))
        (Stor.rest (Devm.getStor creditPost ca)))
      (callback : StorageSegmentDelta ca creditPost callbackPost children)
      (callbackToSettle : Devm.getStor callbackPost =
        Devm.getStor settlePre)
      (settleToDebit : Stor.Weth10Silent
        (Devm.getStor settlePre ca) (Devm.getStor debitPre ca))
      (repayment : LocalActionSegment .flashRepayment action
        (Stor.rest (Devm.getStor debitPre ca))
        (Stor.rest (Devm.getStor post ca)))
      (chronology : descendants = children)

/-- The classified frame composition above is already the exact parent-first
storage segment for the root action and its chronological descendants. -/
theorem RichStorageAccounting.storageSegmentEffect
    {ca : Adr} {pre post : Devm} {action : FlowAction}
    {descendants : List FlowAction}
    (accounting : RichStorageAccounting ca pre post action descendants)
    (codeEq : pre.getCode ca = post.getCode ca) :
    Nonempty (StorageSegmentEffect ca pre post
      (action :: descendants)) := by
  cases accounting with
  | ordinaryMint segment chronology =>
      subst descendants
      exact ⟨⟨StorageSegmentDelta.ofOrdinaryMint segment, codeEq⟩⟩
  | ordinaryTransfer segment chronology =>
      subst descendants
      exact ⟨⟨StorageSegmentDelta.ofOrdinaryTransfer segment, codeEq⟩⟩
  | redemption segment callback suffix chronology =>
      subst descendants
      have delta := (StorageSegmentDelta.ofRedemption segment).append
        (callback.append
          (StorageSegmentDelta.of_weth10Silent suffix))
      exact ⟨⟨by simpa only [List.singleton_append, List.append_nil]
        using delta, codeEq⟩⟩
  | tokenCallback own callback chronology =>
      subst descendants
      exact ⟨⟨by simpa only [List.singleton_append]
        using own.append callback, codeEq⟩⟩
  | redemptionThenTokenCallback segment valueCallback tokenCallback
      chronology =>
      subst descendants
      have delta := (StorageSegmentDelta.ofRedemption segment).append
        (valueCallback.append tokenCallback)
      exact ⟨⟨by simpa only [List.singleton_append,
        List.append_assoc] using delta, codeEq⟩⟩
  | flash credit callback callbackToSettle settleToDebit repayment
      chronology =>
      subst descendants
      have callbackDelta := callback.append
        ((StorageSegmentDelta.of_getStor_eq
            (congrFun callbackToSettle ca)).append
          (StorageSegmentDelta.of_weth10Silent settleToDebit))
      exact ⟨⟨by
        simpa only [List.append_nil] using
          StorageSegmentDelta.ofFlashSegments credit callbackDelta repayment,
        codeEq⟩⟩

/-- Storage composition for public leaves that emit no root flow action.
The recursive constructors retain the actual callback child delta and only
accept a chronology equation for the proof-indexed descendant ledger. -/
inductive NoFlowStorageAccounting (ca : Adr) (pre post : Devm)
    (descendants : List FlowAction) : Prop
  | silent
      (own : Stor.Weth10Silent
        (Devm.getStor pre ca) (Devm.getStor post ca))
      (chronology : descendants = [])
  | callback
      {callbackPre : Devm} {children : List FlowAction}
      (ownPrefix : Stor.Weth10Silent
        (Devm.getStor pre ca) (Devm.getStor callbackPre ca))
      (child : StorageSegmentDelta ca callbackPre post children)
      (chronology : descendants = children)
  | silentAround
      {callPre callPost : Devm} {children : List FlowAction}
      (ownPrefix : Stor.Weth10Silent
        (Devm.getStor pre ca) (Devm.getStor callPre ca))
      (child : StorageSegmentDelta ca callPre callPost children)
      (ownSuffix : Stor.Weth10Silent
        (Devm.getStor callPost ca) (Devm.getStor post ca))
      (chronology : descendants = children)

/-- A non-flow composition is exactly the delta of its retained descendants;
no endpoint equation is accepted in place of the operational child segment. -/
theorem NoFlowStorageAccounting.storageSegmentDelta
    {ca : Adr} {pre post : Devm} {descendants : List FlowAction}
    (accounting : NoFlowStorageAccounting ca pre post descendants) :
    Nonempty (StorageSegmentDelta ca pre post descendants) := by
  cases accounting with
  | silent own chronology =>
      subst descendants
      exact ⟨StorageSegmentDelta.of_weth10Silent own⟩
  | callback ownPrefix child chronology =>
      subst descendants
      refine ⟨?_⟩
      simpa only [List.nil_append] using
        (StorageSegmentDelta.of_weth10Silent ownPrefix).append child
  | silentAround ownPrefix child ownSuffix chronology =>
      subst descendants
      refine ⟨?_⟩
      simpa only [List.nil_append, List.append_nil] using
        (StorageSegmentDelta.of_weth10Silent ownPrefix).append
          (child.append (StorageSegmentDelta.of_weth10Silent ownSuffix))

/-- Message-entry value transfer changes balances but never persistent
storage.  This projection is useful both for ordinary calls and for callback
traces whose value is definitionally zero. -/
theorem benvAfterTransfer_getStor_eq
    {msg : Msg} {benv : Benv}
    (htransfer : msg.benvAfterTransfer = .ok benv) (a : Adr) :
    benv.state.getStor a = msg.benv.state.getStor a := by
  by_cases hstv : msg.shouldTransferValue = true
  · rcases of_benvAfterTransfer hstv htransfer with
      ⟨middle, hsub, rfl⟩
    exact (of_state_transfer_fields hsub).1 a
  · rw [of_benvAfterTransfer_no hstv htransfer]

theorem installedWeth10Code_size_ne_zero
    {dp : DeployParams} {ca : Adr} {pre : Devm}
    (hcode : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp)) :
    (pre.getCode ca).size ≠ 0 := by
  rw [weth10Code_compile] at hcode
  have hlist : (pre.getCode ca).toList = weth10Code dp :=
    Option.some.inj hcode
  have hsize : (pre.getCode ca).size = 6313 := by
    calc
      (pre.getCode ca).size = (pre.getCode ca).toList.length := by
        exact ByteArray.size_eq_length_toList _
      _ = (weth10Code dp).length := congrArg List.length hlist
      _ = 6313 := weth10Code_length dp
  omega

theorem GenericCreate.newAddress_ne_of_installed
    {dp : DeployParams} {ca : Adr}
    {sevm : Sevm} {pre : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    {cevm : Evm} {raw out : Execution}
    (hrun : GenericCreate sevm pre endowment newAddress mi ms
      (.some ⟨cevm, raw⟩) out)
    (hcode : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp)) :
    newAddress ≠ ca := by
  obtain ⟨frame, resume, hspawn, -, -⟩ := XStep.Run.some_inv hrun
  have hempty : pre.getCode newAddress = .empty :=
    (genericCreate.step_spawn_frame hspawn).2.2
  intro heq
  subst newAddress
  apply installedWeth10Code_size_ne_zero hcode
  rw [hempty]
  rfl

theorem processCreateMessage_msg_getStor_eq
    {msg : Msg} {ca : Adr} (htargetNe : msg.currentTarget ≠ ca) :
    (processCreateMessage.msg msg).benv.state.getStor ca =
      msg.benv.state.getStor ca := by
  dsimp [processCreateMessage.msg, Msg.withBenv,
    addCreatedAccount, Benv.setStor, Benv.incrNonce, State.getStor]
  rw [State.incrNonce_get_stor,
    State.setStor_get_stor_ne htargetNe]

theorem ProcessCreateMessage.ok_getStorCode_eq_inner_of_clean
    {msg : Msg} {slot : Xlot} {post : Devm} {ca : Adr}
    (hprocess : ProcessCreateMessage msg slot (.ok post))
    (herror : post.error.isSome = false)
    (htargetNe : msg.currentTarget ≠ ca) :
    ∃ inner : Devm,
      ProcessMessage (processCreateMessage.msg msg) slot (.ok inner) ∧
      post.state.getStor ca = inner.state.getStor ca ∧
      post.state.getCode ca = inner.state.getCode ca := by
  rcases ProcessCreateMessage.iff_processMessage.mp hprocess with
    ⟨result, hinner, hsettle⟩
  cases result with
  | error error =>
      simp [processCreateMessage.settle] at hsettle
  | ok inner =>
      unfold processCreateMessage.settle at hsettle
      simp only [bind, Except.bind] at hsettle
      by_cases hinnerNone : inner.error.isNone = true
      · rw [if_pos hinnerNone] at hsettle
        cases hcharge :
          processCreateMessage.chargeCodeGas
            msg.benv.stat.rules inner with
        | error error =>
            rw [hcharge] at hsettle
            rcases error with ⟨error, charged⟩
            cases error with
            | halt reason =>
                have heq := Except.ok.inj hsettle
                rw [heq] at herror
                simp [processCreateMessage.exceptionalHalt,
                  Devm.error, Devm.setMeta] at herror
            | revert => cases hsettle
            | crypto reason => cases hsettle
            | internal reason => cases hsettle
        | ok charged =>
            rw [hcharge] at hsettle
            have heq := Except.ok.inj hsettle
            refine ⟨inner, hinner, ?_, ?_⟩
            · calc
                post.state.getStor ca =
                    (charged.setCode msg.currentTarget
                      ⟨⟨charged.output⟩⟩).state.getStor ca :=
                  congrArg (fun d : Devm => d.state.getStor ca) heq
                _ = charged.state.getStor ca := by
                  change
                    ((charged.state.setCode msg.currentTarget
                      ⟨⟨charged.output⟩⟩).get ca).stor = _
                  exact State.setCode_get_stor
                _ = inner.state.getStor ca := by
                  rw [chargeCodeGas_state_ok hcharge]
            · calc
                post.state.getCode ca =
                    (charged.setCode msg.currentTarget
                      ⟨⟨charged.output⟩⟩).state.getCode ca :=
                  congrArg (fun d : Devm => d.state.getCode ca) heq
                _ = charged.state.getCode ca := by
                  change
                    ((charged.state.setCode msg.currentTarget
                      ⟨⟨charged.output⟩⟩).get ca).code = _
                  exact State.setCode_get_code_ne htargetNe
                _ = inner.state.getCode ca := by
                  rw [chargeCodeGas_state_ok hcharge]
      · rw [if_neg hinnerNone] at hsettle
        have heq := Except.ok.inj hsettle
        rw [heq] at herror
        simp [Devm.rollback, Devm.setWorld, Devm.error] at herror
        apply False.elim
        apply hinnerNone
        rw [show inner.error = none from herror]
        rfl

/-- The recursive premise needed to account for a concrete child message. -/
def StorageSegmentTraceBelow
    (dp : DeployParams) (ca : Adr) (depth : Nat) : Prop :=
  ∀ {pc : Nat} {sevm : Sevm} {pre raw : Devm}
    (run : Exec pc sevm pre (.ok raw))
    (_ : sevm.depth < depth)
    (_ : Prog.At (weth10 dp) ca pc sevm pre)
    (committed : Execution.commits (.ok raw) = true),
    Exec.Frame.IsRoot (Exec.Frame.ofRun run committed) →
    Nonempty (StorageSegmentEffect ca pre raw
      (Exec.flowActions dp ca run))

/-- A concrete retained message trace has an exact storage delta whenever
every committed entered child below the caller depth has one.  The theorem
handles the no-code/precompile slot and rollback internally; no endpoint
equality is supplied for a child that commits. -/
theorem ProcessMessageTrace.storageSegmentDelta
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {msg : Msg} {post parent : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hparent : parent.state = msg.benv.state)
    (hdepth : msg.depth < depth)
    (hcode : some (parent.getCode ca).toList =
      Prog.compile (weth10 dp))
    (htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp))
    (hbelow : StorageSegmentTraceBelow dp ca depth) :
    Nonempty (StorageSegmentEffect ca parent post
      (Blanc.Weth10.RetainedXlot.flowActions dp ca trace.retained)) := by
  rcases trace with ⟨slot, retained, hprocess⟩
  cases retained with
  | none =>
      have hstorage : Devm.getStor parent ca = Devm.getStor post ca := by
        rcases ProcessMessage.none_ok_state_cases hprocess with
          hrollback | ⟨benv, htransfer, hpost⟩
        · exact congrArg (fun state : State => state.getStor ca)
            (hparent.trans hrollback.symm)
        · change msg.benvAfterTransfer = .ok benv at htransfer
          exact (congrArg (fun state : State => state.getStor ca) hparent).trans <|
            (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
              (congrArg (fun state : State => state.getStor ca) hpost).symm
      have hcodeEq : parent.getCode ca = post.getCode ca := by
        rcases ProcessMessage.none_ok_state_cases hprocess with
          hrollback | ⟨benv, htransfer, hpost⟩
        · exact congrArg (fun state : State => state.getCode ca)
            (hparent.trans hrollback.symm)
        · change msg.benvAfterTransfer = .ok benv at htransfer
          exact (congrArg (fun state : State => state.getCode ca) hparent).trans <|
            (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
              (congrArg (fun state : State => state.getCode ca) hpost).symm
      exact ⟨StorageSegmentEffect.of_getStorCode_eq hstorage hcodeEq⟩
  | @some pc sevm pre out run =>
      have henter : (Frame.ofCall msg).enter =
          .run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hprocess).1
      rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hevm⟩
      simp only [Frame.ofCall] at htransfer hevm
      have hpreState : pre.state = benv.state := by
        have component := congrArg (fun evm : Evm => evm.dyna.state) hevm
        change pre.state = (initEvm (msg.withBenv benv)).dyna.state
        exact component
      have hsevm : sevm = initSevm (msg.withBenv benv) := by
        exact congrArg (fun evm : Evm => evm.sta) hevm
      have hpc : pc = 0 := by
        simpa [initEvm] using congrArg (fun evm : Evm => evm.pc) hevm
      have hmemory : pre.memory = Mem.empty := by
        have component := congrArg (fun evm : Evm => evm.dyna.memory) hevm
        change pre.memory = (initEvm (msg.withBenv benv)).dyna.memory
        simpa [initEvm, initDevm, Msg.withBenv] using component
      have hentryStorage : Devm.getStor parent ca = Devm.getStor pre ca := by
        exact (congrArg (fun state : State => state.getStor ca) hparent).trans <|
          (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
            (congrArg (fun state : State => state.getStor ca) hpreState).symm
      have hentryCodeEq : parent.getCode ca = pre.getCode ca := by
        exact (congrArg (fun state : State => state.getCode ca) hparent).trans <|
          (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
            (congrArg (fun state : State => state.getCode ca) hpreState).symm
      have hentryCode : some (pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        calc
          some (pre.getCode ca).toList =
              some (benv.state.getCode ca).toList := by
            change some (pre.state.getCode ca).toList = _
            rw [hpreState]
          _ = some (msg.benv.state.getCode ca).toList := by
            rw [benvAfterTransfer_ok_getCode htransfer ca]
          _ = some (parent.getCode ca).toList := by
            change some (msg.benv.state.getCode ca).toList =
              some (parent.state.getCode ca).toList
            rw [hparent]
          _ = _ := hcode
      have hat : Prog.At (weth10 dp) ca pc sevm pre := by
        refine ⟨hentryCode, ?_⟩
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        refine ⟨?_, hpc⟩
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using htargetCode hmsgTarget
      by_cases hcommit : Execution.commits out = true
      · cases out with
        | error err => simp [Execution.commits] at hcommit
        | ok raw =>
            rcases hbelow run (by
                rw [hsevm]
                simpa [initSevm, Msg.withBenv] using hdepth)
              hat hcommit ⟨hpc, hmemory⟩ with ⟨childEffect⟩
            have hpostState : post.state = raw.state :=
              ProcessMessage.ok_state_eq_committedPost hprocess hcommit
            have hpostStorage : Devm.getStor raw ca = Devm.getStor post ca :=
              congrArg (fun state : State => state.getStor ca) hpostState.symm
            have hpostCode : raw.getCode ca = post.getCode ca :=
              congrArg (fun state : State => state.getCode ca) hpostState.symm
            exact ⟨by
              simpa only [List.nil_append, List.append_nil,
                RetainedXlot.flowActions] using
                (StorageSegmentEffect.of_getStorCode_eq
                    hentryStorage hentryCodeEq).append
                  (childEffect.append
                    (StorageSegmentEffect.of_getStorCode_eq
                      hpostStorage hpostCode))⟩
      · have hactions : Exec.flowActions dp ca run = [] :=
          Exec.flowActions_eq_nil_of_not_commits run hcommit
        have hpostState : post.state = msg.benv.state :=
          ProcessMessage.ok_state_eq_of_not_commits hprocess hcommit
        have hstorage : Devm.getStor parent ca = Devm.getStor post ca :=
          congrArg (fun state : State => state.getStor ca)
            (hparent.trans hpostState.symm)
        have hcodeEq : parent.getCode ca = post.getCode ca :=
          congrArg (fun state : State => state.getCode ca)
            (hparent.trans hpostState.symm)
        simp only [Blanc.Weth10.RetainedXlot.flowActions, hactions]
        exact ⟨StorageSegmentEffect.of_getStorCode_eq hstorage hcodeEq⟩

/-- A filled CALL message is retained exactly when its complete frame
settlement is clean.  A noncommitting settlement restores the saved message
world and therefore contributes neither storage segments nor child labels. -/
theorem ProcessMessage.storageSegmentEffect_of_settlement
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {msg : Msg} {post parent : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hparent : parent.state = msg.benv.state)
    (hdepth : msg.depth < depth)
    (hcode : some (parent.getCode ca).toList =
      Prog.compile (weth10 dp))
    (htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp))
    (hbelow : StorageSegmentTraceBelow dp ca depth) :
    Nonempty (StorageSegmentEffect ca parent post
      (if Blanc.Frame.settlementCommits
          (Frame.ofCall msg) out = true
       then Exec.flowActions dp ca run else [])) := by
  by_cases hsettle : Blanc.Frame.settlementCommits
      (Frame.ofCall msg) out = true
  · rw [if_pos hsettle]
    let trace : ProcessMessageTrace msg (.ok post) :=
      ⟨.some ⟨⟨pc, sevm, pre⟩, out⟩, .some run, hprocess⟩
    simpa only [trace, RetainedXlot.flowActions] using
      trace.storageSegmentDelta hparent hdepth hcode htargetCode hbelow
  · rw [if_neg hsettle]
    have hset := (RunFrame.some_inv hprocess).2
    have herr : post.error.isSome = true := by
      have hnone : post.error.isNone ≠ true := by
        intro hnone
        apply hsettle
        unfold Blanc.Frame.settlementCommits
        rw [← hset]
        exact hnone
      cases he : post.error <;> simp_all
    have hpostState : post.state = msg.benv.state :=
      (ProcessMessage.rollback_of_error hprocess herr).1
    have hstorage : Devm.getStor parent ca = Devm.getStor post ca :=
      congrArg (fun state : State => state.getStor ca)
        (hparent.trans hpostState.symm)
    have hcodeEq : parent.getCode ca = post.getCode ca :=
      congrArg (fun state : State => state.getCode ca)
        (hparent.trans hpostState.symm)
    exact ⟨StorageSegmentEffect.of_getStorCode_eq hstorage hcodeEq⟩

/-- Proof-indexed form of `storageSegmentEffect_of_settlement`.  It consumes
the accounting theorem for this concrete child derivation, which is the form
available in the `lift_core` recursive handler. -/
theorem ProcessMessage.storageSegmentEffect_of_bodyEffect
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post parent : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hparent : parent.state = msg.benv.state)
    (hbody : ∀ (committed : Execution.commits out = true),
      Nonempty (StorageSegmentEffect ca pre
        (Execution.committedPost out committed)
        (Exec.flowActions dp ca run))) :
    Nonempty (StorageSegmentEffect ca parent post
      (if Blanc.Frame.settlementCommits
          (Frame.ofCall msg) out = true
       then Exec.flowActions dp ca run else [])) := by
  by_cases hsettle : Blanc.Frame.settlementCommits
      (Frame.ofCall msg) out = true
  · rw [if_pos hsettle]
    have committed : Execution.commits out = true :=
      Frame.raw_commits_of_settlementCommits hsettle
    rcases hbody committed with ⟨body⟩
    have henter : (Frame.ofCall msg).enter =
        .run ⟨pc, sevm, pre⟩ :=
      (RunFrame.some_inv hprocess).1
    rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hevm⟩
    simp only [Frame.ofCall] at htransfer hevm
    have hpreState : pre.state = benv.state := by
      have component := congrArg (fun evm : Evm => evm.dyna.state) hevm
      change pre.state = (initEvm (msg.withBenv benv)).dyna.state
      exact component
    have hentryStorage : Devm.getStor parent ca = Devm.getStor pre ca := by
      exact (congrArg (fun state : State => state.getStor ca) hparent).trans <|
        (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
          (congrArg (fun state : State => state.getStor ca) hpreState).symm
    have hentryCode : parent.getCode ca = pre.getCode ca := by
      exact (congrArg (fun state : State => state.getCode ca) hparent).trans <|
        (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
          (congrArg (fun state : State => state.getCode ca) hpreState).symm
    have hpostState : post.state =
        (Execution.committedPost out committed).state :=
      ProcessMessage.ok_state_eq_committedPost hprocess committed
    have hpostStorage : Devm.getStor
        (Execution.committedPost out committed) ca = Devm.getStor post ca :=
      congrArg (fun state : State => state.getStor ca) hpostState.symm
    have hpostCode : (Execution.committedPost out committed).getCode ca =
        post.getCode ca :=
      congrArg (fun state : State => state.getCode ca) hpostState.symm
    exact ⟨by
      simpa only [List.nil_append, List.append_nil] using
        (StorageSegmentEffect.of_getStorCode_eq
            hentryStorage hentryCode).append
          (body.append
            (StorageSegmentEffect.of_getStorCode_eq
              hpostStorage hpostCode))⟩
  · rw [if_neg hsettle]
    have hset := (RunFrame.some_inv hprocess).2
    have herr : post.error.isSome = true := by
      have hnone : post.error.isNone ≠ true := by
        intro hnone
        apply hsettle
        unfold Blanc.Frame.settlementCommits
        rw [← hset]
        exact hnone
      cases he : post.error <;> simp_all
    have hpostState : post.state = msg.benv.state :=
      (ProcessMessage.rollback_of_error hprocess herr).1
    have hstorage : Devm.getStor parent ca = Devm.getStor post ca :=
      congrArg (fun state : State => state.getStor ca)
        (hparent.trans hpostState.symm)
    have hcodeEq : parent.getCode ca = post.getCode ca :=
      congrArg (fun state : State => state.getCode ca)
        (hparent.trans hpostState.symm)
    exact ⟨StorageSegmentEffect.of_getStorCode_eq hstorage hcodeEq⟩

/-- A childless message (empty code or precompile) cannot write persistent
contract storage.  Message-entry balance transfer and settlement are both
projected from the actual `ProcessMessage` derivation. -/
theorem ProcessMessage.storageSegmentEffect_none
    {ca : Adr} {msg : Msg} {post parent : Devm}
    (hprocess : ProcessMessage msg .none (.ok post))
    (hparent : parent.state = msg.benv.state) :
    Nonempty (StorageSegmentEffect ca parent post []) := by
  have hstorage : Devm.getStor parent ca = Devm.getStor post ca := by
    rcases ProcessMessage.none_ok_state_cases hprocess with
      hrollback | ⟨benv, htransfer, hpost⟩
    · exact congrArg (fun state : State => state.getStor ca)
        (hparent.trans hrollback.symm)
    · change msg.benvAfterTransfer = .ok benv at htransfer
      exact (congrArg (fun state : State => state.getStor ca) hparent).trans <|
        (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
          (congrArg (fun state : State => state.getStor ca) hpost).symm
  have hcode : parent.getCode ca = post.getCode ca := by
    rcases ProcessMessage.none_ok_state_cases hprocess with
      hrollback | ⟨benv, htransfer, hpost⟩
    · exact congrArg (fun state : State => state.getCode ca)
        (hparent.trans hrollback.symm)
    · change msg.benvAfterTransfer = .ok benv at htransfer
      exact (congrArg (fun state : State => state.getCode ca) hparent).trans <|
        (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
          (congrArg (fun state : State => state.getCode ca) hpost).symm
  exact ⟨StorageSegmentEffect.of_getStorCode_eq hstorage hcode⟩

/-- CREATE settlement contributes its retained constructor actions exactly
when the final code-deposit result is clean.  Both constructor failure and
code-deposit failure are handled by the actual rollback path. -/
theorem ProcessCreateMessageTrace.storageSegmentDelta
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {msg : Msg} {post parent : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post))
    (hparent : parent.state = msg.benv.state)
    (hdepth : msg.depth < depth)
    (hcode : some (parent.getCode ca).toList =
      Prog.compile (weth10 dp))
    (htargetNe : msg.currentTarget ≠ ca)
    (hbelow : StorageSegmentTraceBelow dp ca depth) :
    Nonempty (StorageSegmentEffect ca parent post
      (if post.error.isSome then []
       else Blanc.Weth10.RetainedXlot.flowActions dp ca
         trace.retained)) := by
  cases herror : post.error.isSome with
  | true =>
      simp only [↓reduceIte]
      have hpostState : post.state = msg.benv.state :=
        ProcessCreateMessage.rollback_of_error trace.run herror
      have hstorage : Devm.getStor parent ca = Devm.getStor post ca :=
        congrArg (fun state : State => state.getStor ca)
          (hparent.trans hpostState.symm)
      have hcodeEq : parent.getCode ca = post.getCode ca :=
        congrArg (fun state : State => state.getCode ca)
          (hparent.trans hpostState.symm)
      exact ⟨StorageSegmentEffect.of_getStorCode_eq hstorage hcodeEq⟩
  | false =>
      simp only [Bool.false_eq]
      rcases ProcessCreateMessage.ok_getStorCode_eq_inner_of_clean
        trace.run herror htargetNe with
          ⟨inner, hinner, hpostStorage, hpostCode⟩
      let innerTrace : ProcessMessageTrace
          (processCreateMessage.msg msg) (.ok inner) :=
        ⟨trace.slot, trace.retained, hinner⟩
      let prepared : Devm :=
        parent.withState (processCreateMessage.msg msg).benv.state
      have hprefixStorage :
          Devm.getStor parent ca = Devm.getStor prepared ca := by
        change parent.state.getStor ca =
          (processCreateMessage.msg msg).benv.state.getStor ca
        rw [hparent,
          processCreateMessage_msg_getStor_eq htargetNe]
      have hprefixCode : parent.getCode ca = prepared.getCode ca := by
        change parent.state.getCode ca =
          (processCreateMessage.msg msg).benv.state.getCode ca
        rw [hparent, processCreateMessage.msg_getCode]
      have hpreparedCode : some (prepared.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        calc
          some (prepared.getCode ca).toList =
              some ((processCreateMessage.msg msg).benv.state.getCode ca).toList :=
            rfl
          _ = some (msg.benv.state.getCode ca).toList := by
            rw [processCreateMessage.msg_getCode]
          _ = some (parent.state.getCode ca).toList := by
            rw [hparent]
          _ = _ := hcode
      have hinnerDepth : (processCreateMessage.msg msg).depth < depth := by
        simpa [processCreateMessage.msg, Msg.withBenv] using hdepth
      have hinnerTargetCode :
          (processCreateMessage.msg msg).currentTarget = ca →
            some (processCreateMessage.msg msg).code.toList =
              Prog.compile (weth10 dp) := by
        intro htarget
        apply False.elim
        apply htargetNe
        simpa [processCreateMessage.msg, Msg.withBenv] using htarget
      rcases innerTrace.storageSegmentDelta (parent := prepared) rfl
          hinnerDepth hpreparedCode hinnerTargetCode hbelow with ⟨effect⟩
      have hsuffixStorage : Devm.getStor inner ca = Devm.getStor post ca :=
        hpostStorage.symm
      have hsuffixCode : inner.getCode ca = post.getCode ca :=
        hpostCode.symm
      exact ⟨by
        simpa only [innerTrace, herror, Bool.false_eq,
          Bool.true_eq_false, if_false,
          List.nil_append, List.append_nil] using
          (StorageSegmentEffect.of_getStorCode_eq
              hprefixStorage hprefixCode).append
            (effect.append
              (StorageSegmentEffect.of_getStorCode_eq
                hsuffixStorage hsuffixCode))⟩

/-- Proof-indexed CREATE counterpart of
`ProcessMessage.storageSegmentEffect_of_bodyEffect`.  The successful arm
threads the constructor's concrete body effect through code-deposit
settlement; the failed arm uses CREATE's actual saved-world rollback. -/
theorem ProcessCreateMessage.storageSegmentEffect_of_bodyEffect
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post parent : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess : ProcessCreateMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hparent : parent.state = msg.benv.state)
    (htargetNe : msg.currentTarget ≠ ca)
    (hbody : ∀ (committed : Execution.commits out = true),
      Nonempty (StorageSegmentEffect ca pre
        (Execution.committedPost out committed)
        (Exec.flowActions dp ca run))) :
    Nonempty (StorageSegmentEffect ca parent post
      (if Blanc.Frame.settlementCommits
          (Frame.ofCreate msg) out = true
       then Exec.flowActions dp ca run else [])) := by
  by_cases hsettle : Blanc.Frame.settlementCommits
      (Frame.ofCreate msg) out = true
  · rw [if_pos hsettle]
    have committed : Execution.commits out = true :=
      Frame.raw_commits_of_settlementCommits hsettle
    rcases hbody committed with ⟨body⟩
    have hset := (RunFrame.some_inv hprocess).2
    have hnone : post.error.isNone = true := by
      unfold Blanc.Frame.settlementCommits at hsettle
      rw [← hset] at hsettle
      exact hsettle
    have herr : post.error.isSome = false := by
      cases he : post.error <;> simp_all
    rcases ProcessCreateMessage.ok_getStorCode_eq_inner_of_clean
      hprocess herr htargetNe with
        ⟨inner, hinner, hpostStorage, hpostCode⟩
    have henter : (Frame.ofCall (processCreateMessage.msg msg)).enter =
        .run ⟨pc, sevm, pre⟩ :=
      (RunFrame.some_inv hinner).1
    rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hevm⟩
    simp only [Frame.ofCall] at htransfer hevm
    have hpreState : pre.state = benv.state := by
      have component := congrArg (fun evm : Evm => evm.dyna.state) hevm
      change pre.state =
        (initEvm ((processCreateMessage.msg msg).withBenv benv)).dyna.state
      exact component
    let prepared : Devm :=
      parent.withState (processCreateMessage.msg msg).benv.state
    have hprefixStorage : Devm.getStor parent ca =
        Devm.getStor prepared ca := by
      change parent.state.getStor ca =
        (processCreateMessage.msg msg).benv.state.getStor ca
      rw [hparent,
        processCreateMessage_msg_getStor_eq htargetNe]
    have hprefixCode : parent.getCode ca = prepared.getCode ca := by
      change parent.state.getCode ca =
        (processCreateMessage.msg msg).benv.state.getCode ca
      rw [hparent, processCreateMessage.msg_getCode]
    have hentryStorage : Devm.getStor prepared ca = Devm.getStor pre ca := by
      exact (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
        (congrArg (fun state : State => state.getStor ca) hpreState).symm
    have hentryCode : prepared.getCode ca = pre.getCode ca := by
      exact (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
        (congrArg (fun state : State => state.getCode ca) hpreState).symm
    have hinnerState : inner.state =
        (Execution.committedPost out committed).state :=
      ProcessMessage.ok_state_eq_committedPost hinner committed
    have hsuffixStorage : Devm.getStor
        (Execution.committedPost out committed) ca = Devm.getStor post ca :=
      (congrArg (fun state : State => state.getStor ca)
        hinnerState.symm).trans hpostStorage.symm
    have hsuffixCode : (Execution.committedPost out committed).getCode ca =
        post.getCode ca :=
      (congrArg (fun state : State => state.getCode ca)
        hinnerState.symm).trans hpostCode.symm
    exact ⟨by
      simpa only [List.nil_append, List.append_nil] using
        (StorageSegmentEffect.of_getStorCode_eq
            (hprefixStorage.trans hentryStorage)
            (hprefixCode.trans hentryCode)).append
          (body.append
            (StorageSegmentEffect.of_getStorCode_eq
              hsuffixStorage hsuffixCode))⟩
  · rw [if_neg hsettle]
    have hset := (RunFrame.some_inv hprocess).2
    have herr : post.error.isSome = true := by
      have hnone : post.error.isNone ≠ true := by
        intro hnone
        apply hsettle
        unfold Blanc.Frame.settlementCommits
        rw [← hset]
        exact hnone
      cases he : post.error <;> simp_all
    have hpostState : post.state = msg.benv.state :=
      ProcessCreateMessage.rollback_of_error hprocess herr
    have hstorage : Devm.getStor parent ca = Devm.getStor post ca :=
      congrArg (fun state : State => state.getStor ca)
        (hparent.trans hpostState.symm)
    have hcodeEq : parent.getCode ca = post.getCode ca :=
      congrArg (fun state : State => state.getCode ca)
        (hparent.trans hpostState.symm)
    exact ⟨StorageSegmentEffect.of_getStorCode_eq hstorage hcodeEq⟩

/-- A CALL-family instruction with a concrete child slot consists of a
storage-silent instruction prefix, the exact retained child message, and a
storage-silent resumption. -/
theorem GenericCall.storageSegmentDelta_some
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {sevm : Sevm} {pre inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray}
    {disablePrecompiles : Bool}
    {pc' : Nat} {childSevm : Sevm} {childPre : Devm}
    {childOut : Execution}
    (hrun : GenericCall sevm pre gas value caller target codeAddress stv
      isStatic ii is oi os code disablePrecompiles
      (.some ⟨⟨pc', childSevm, childPre⟩, childOut⟩) (.ok inter))
    (childRun : Exec pc' childSevm childPre childOut)
    (hdepth : childSevm.depth < depth)
    (hcode : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (htargetCode : target = ca →
      some code.toList = Prog.compile (weth10 dp))
    (hbelow : StorageSegmentTraceBelow dp ca depth) :
    Nonempty (StorageSegmentEffect ca pre inter
      (if Blanc.Frame.settlementCommits
          (Frame.ofCall
            (callMsg sevm (pre.withReturnData []) gas value caller target
              codeAddress stv isStatic ((pre.memory.read ii is).1)
              code disablePrecompiles)) childOut = true
       then Exec.flowActions dp ca childRun else [])) := by
  unfold GenericCall genericCall.step at hrun
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hrun
  repeat' split at hrun
  all_goals simp only [XStep.ofExcept, XStep.Run] at hrun
  · cases hrun.1
  · cases hrun.1
  · obtain ⟨result, hprocess, hresume⟩ := hrun
    rcases result with error | child
    · cases Resume.call_run_error hresume.symm
    have hinterState : inter.state = child.state :=
      Resume.call_state hresume.symm
    let callPre := pre.withReturnData []
    let msg := callMsg sevm callPre gas value caller target codeAddress stv
      isStatic ((callPre.memory.read ii is).1) code disablePrecompiles
    let trace : ProcessMessageTrace msg (.ok child) :=
      ⟨.some ⟨⟨pc', childSevm, childPre⟩, childOut⟩,
        .some childRun, by
          simpa only [ProcessMessage, msg, callPre, Mem.read] using hprocess⟩
    have hmsgDepth : msg.depth < depth := by
      rw [← ProcessMessage.depth_eq trace.run]
      exact hdepth
    have hmsgTargetCode : msg.currentTarget = ca →
        some msg.code.toList = Prog.compile (weth10 dp) := by
      intro htarget
      apply htargetCode
      simpa only [msg, callMsg] using htarget
    have hcallPreCode : some (callPre.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      change some (pre.getCode ca).toList = Prog.compile (weth10 dp)
      exact hcode
    rcases ProcessMessage.storageSegmentEffect_of_settlement childRun
        trace.run (parent := callPre) rfl hmsgDepth hcallPreCode
        hmsgTargetCode hbelow with ⟨effect⟩
    have hprefixStorage : Devm.getStor pre ca = Devm.getStor callPre ca := by
      rfl
    have hprefixCode : pre.getCode ca = callPre.getCode ca := by
      rfl
    have hpostStorage : Devm.getStor child ca = Devm.getStor inter ca :=
      (getStor_eq_of_state_eq hinterState ca).symm
    have hpostCode : child.getCode ca = inter.getCode ca :=
      congrArg (fun state : State => state.getCode ca) hinterState.symm
    have hmemory : callPre.memory = pre.memory := by
      rfl
    dsimp only [msg] at effect
    rw [hmemory] at effect
    dsimp only [callPre] at effect
    exact ⟨by
      convert
        (StorageSegmentEffect.of_getStorCode_eq
            hprefixStorage hprefixCode).append
          (effect.append
            (StorageSegmentEffect.of_getStorCode_eq
              hpostStorage hpostCode)) using 1
      by_cases hretain : Blanc.Frame.settlementCommits
          (Frame.ofCall
            (callMsg sevm (pre.withReturnData []) gas value caller target
              codeAddress stv isStatic ((pre.memory.read ii is).1) code
              disablePrecompiles)) childOut = true <;>
        simp [hretain]⟩

/-- Proof-indexed CALL transport: the recursive premise is the effect of this
exact filled child slot, rather than a depth-wide hypothesis. -/
theorem GenericCall.storageSegmentEffect_some_of_bodyEffect
    {dp : DeployParams} {ca : Adr}
    {sevm : Sevm} {pre inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray}
    {disablePrecompiles : Bool}
    {pc' : Nat} {childSevm : Sevm} {childPre : Devm}
    {childOut : Execution}
    (hrun : GenericCall sevm pre gas value caller target codeAddress stv
      isStatic ii is oi os code disablePrecompiles
      (.some ⟨⟨pc', childSevm, childPre⟩, childOut⟩) (.ok inter))
    (childRun : Exec pc' childSevm childPre childOut)
    (hbody : ∀ (committed : Execution.commits childOut = true),
      Nonempty (StorageSegmentEffect ca childPre
        (Execution.committedPost childOut committed)
        (Exec.flowActions dp ca childRun))) :
    Nonempty (StorageSegmentEffect ca pre inter
      (if Blanc.Frame.settlementCommits
          (Frame.ofCall
            (callMsg sevm (pre.withReturnData []) gas value caller target
              codeAddress stv isStatic ((pre.memory.read ii is).1)
              code disablePrecompiles)) childOut = true
       then Exec.flowActions dp ca childRun else [])) := by
  unfold GenericCall genericCall.step at hrun
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hrun
  repeat' split at hrun
  all_goals simp only [XStep.ofExcept, XStep.Run] at hrun
  · cases hrun.1
  · cases hrun.1
  · obtain ⟨result, hprocess, hresume⟩ := hrun
    rcases result with error | child
    · cases Resume.call_run_error hresume.symm
    have hinterState : inter.state = child.state :=
      Resume.call_state hresume.symm
    let callPre := pre.withReturnData []
    let msg := callMsg sevm callPre gas value caller target codeAddress stv
      isStatic ((callPre.memory.read ii is).1) code disablePrecompiles
    have hprocess' : ProcessMessage msg
        (.some ⟨⟨pc', childSevm, childPre⟩, childOut⟩) (.ok child) := by
      simpa only [ProcessMessage, msg, callPre, Mem.read] using hprocess
    rcases ProcessMessage.storageSegmentEffect_of_bodyEffect childRun
        hprocess' (parent := callPre) rfl hbody with ⟨effect⟩
    have hprefixStorage : Devm.getStor pre ca = Devm.getStor callPre ca := by
      rfl
    have hprefixCode : pre.getCode ca = callPre.getCode ca := by
      rfl
    have hpostStorage : Devm.getStor child ca = Devm.getStor inter ca :=
      (getStor_eq_of_state_eq hinterState ca).symm
    have hpostCode : child.getCode ca = inter.getCode ca :=
      congrArg (fun state : State => state.getCode ca) hinterState.symm
    have hmemory : callPre.memory = pre.memory := by
      rfl
    dsimp only [msg] at effect
    rw [hmemory] at effect
    dsimp only [callPre] at effect
    exact ⟨by
      convert
        (StorageSegmentEffect.of_getStorCode_eq
            hprefixStorage hprefixCode).append
          (effect.append
            (StorageSegmentEffect.of_getStorCode_eq
              hpostStorage hpostCode)) using 1
      by_cases hretain : Blanc.Frame.settlementCommits
          (Frame.ofCall
            (callMsg sevm (pre.withReturnData []) gas value caller target
              codeAddress stv isStatic ((pre.memory.read ii is).1) code
              disablePrecompiles)) childOut = true <;>
        simp [hretain]⟩

/-- A CALL-family opcode which completes without an interpreter child is
storage- and code-silent at every address. -/
theorem GenericCall.storageSegmentEffect_none
    {ca : Adr} {sevm : Sevm} {pre post : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray}
    {disablePrecompiles : Bool}
    (hrun : GenericCall sevm pre gas value caller target codeAddress stv
      isStatic ii is oi os code disablePrecompiles .none (.ok post)) :
    Nonempty (StorageSegmentEffect ca pre post []) := by
  unfold GenericCall genericCall.step at hrun
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hrun
  repeat' split at hrun
  all_goals simp only [XStep.ofExcept, XStep.Run] at hrun
  · cases hrun.2
  · rename_i hpush
    have hpost := Except.ok.inj hrun.2
    have hframe := Devm.push_instructionFrame 0
      ((pre.withReturnData []).withGasLeft
        ((pre.withReturnData []).gasLeft + gas))
    rw [hpush] at hframe
    have hstorage : Devm.getStor pre ca = Devm.getStor post ca :=
      (show Devm.getStor pre ca = Devm.getStor
          ((pre.withReturnData []).withGasLeft
            ((pre.withReturnData []).gasLeft + gas)) ca from rfl).trans
        ((hframe.getStor ca).trans
          (congrArg (fun d : Devm => Devm.getStor d ca) hpost.symm))
    have hcode : pre.getCode ca = post.getCode ca :=
      (show pre.getCode ca = ((pre.withReturnData []).withGasLeft
          ((pre.withReturnData []).gasLeft + gas)).getCode ca from rfl).trans
        ((hframe.getCode ca).trans
          (congrArg (fun d : Devm => d.getCode ca) hpost.symm))
    exact ⟨StorageSegmentEffect.of_getStorCode_eq hstorage hcode⟩
  · obtain ⟨result, hprocess, hresume⟩ := hrun
    cases result with
    | error error =>
        simp [Resume.run, liftToExecution] at hresume
    | ok child =>
        rcases ProcessMessage.storageSegmentEffect_none
            hprocess (parent := pre.withReturnData []) rfl with ⟨effect⟩
        have hresumeState : post.state = child.state :=
          Resume.call_state hresume.symm
        have hsuffixStorage : Devm.getStor child ca = Devm.getStor post ca :=
          congrArg (fun state : State => state.getStor ca) hresumeState.symm
        have hsuffixCode : child.getCode ca = post.getCode ca :=
          congrArg (fun state : State => state.getCode ca) hresumeState.symm
        exact ⟨by
          simpa only [List.nil_append] using
            (StorageSegmentEffect.of_getStorCode_eq
                (ca := ca) (pre := pre) (post := pre.withReturnData [])
                rfl rfl).append
              (effect.append
                (StorageSegmentEffect.of_getStorCode_eq
                  hsuffixStorage hsuffixCode))⟩

/-- A CREATE-family instruction with a concrete constructor slot retains the
child actions only when full create settlement (including code deposit)
commits.  Fresh-address separation from the installed contract follows from
the actual collision check that admitted the concrete child slot. -/
theorem GenericCreate.storageSegmentEffect_some
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {sevm : Sevm} {pre post : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    {cevm : Evm} {raw : Execution}
    (hrun : GenericCreate sevm pre endowment newAddress mi ms
      (.some ⟨cevm, raw⟩) (.ok post))
    (childRun : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hdepth : cevm.sta.depth < depth)
    (hcode : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hbelow : StorageSegmentTraceBelow dp ca depth) :
    Nonempty (StorageSegmentEffect ca pre post
      (if Blanc.Frame.settlementCommits
          (Frame.ofCreate
            (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1))) raw = true
       then Exec.flowActions dp ca childRun else [])) := by
  have hnewNe : newAddress ≠ ca :=
    GenericCreate.newAddress_ne_of_installed hrun hcode
  unfold GenericCreate genericCreate.step at hrun
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at hrun
  repeat' split at hrun
  all_goals simp only [XStep.ofExcept, XStep.Run] at hrun
  all_goals try
    (have hxl : (some ⟨cevm, raw⟩ : Xlot) = none := hrun.1
     cases hxl)
  obtain ⟨result, hframe, hresume⟩ := hrun
  cases result with
  | error error =>
      simp [Resume.run, liftToExecution] at hresume
  | ok settled =>
      let createPre :=
        addAccessedAddress
          (((pre.withGasLeft
              (pre.gasLeft - except64th pre.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress
      let msg := createMsg sevm createPre (except64th pre.gasLeft)
        endowment newAddress ((pre.memory.read mi ms).1)
      let trace : ProcessCreateMessageTrace msg (.ok settled) :=
        ⟨.some ⟨cevm, raw⟩, .some childRun, by
          simpa only [ProcessCreateMessage, msg, createPre, Mem.read] using
            hframe⟩
      have hmsgDepth : msg.depth < depth := by
        rw [← ProcessCreateMessage.depth_eq trace.run]
        exact hdepth
      have hcreatePreStorage :
          Devm.getStor pre ca = Devm.getStor createPre ca := by
        have hstate : createPre.state =
            pre.state.incrNonce sevm.currentTarget := by
          rfl
        change pre.state.getStor ca = createPre.state.getStor ca
        rw [hstate]
        exact State.incrNonce_get_stor.symm
      have hcreatePreCode : pre.getCode ca = createPre.getCode ca := by
        have hstate : createPre.state =
            pre.state.incrNonce sevm.currentTarget := by
          rfl
        change pre.state.getCode ca = createPre.state.getCode ca
        rw [hstate]
        exact State.incrNonce_get_code.symm
      have hcreatePreInstalled : some (createPre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        rw [← hcreatePreCode]
        exact hcode
      rcases trace.storageSegmentDelta (parent := createPre) rfl hmsgDepth
          hcreatePreInstalled hnewNe hbelow with ⟨effect⟩
      have hresumeState : post.state = settled.state :=
        Resume.create_state hresume.symm
      have hpostStorage : Devm.getStor settled ca = Devm.getStor post ca :=
        congrArg (fun state : State => state.getStor ca) hresumeState.symm
      have hpostCode : settled.getCode ca = post.getCode ca :=
        congrArg (fun state : State => state.getCode ca) hresumeState.symm
      have combined :=
        (StorageSegmentEffect.of_getStorCode_eq
            hcreatePreStorage hcreatePreCode).append
          (effect.append
            (StorageSegmentEffect.of_getStorCode_eq
              hpostStorage hpostCode))
      have hsettle :
          (Frame.ofCreate msg).settle raw = .ok settled :=
        (RunFrame.some_inv trace.run).2.symm
      cases hopt : settled.error <;>
        refine ⟨?_⟩ <;>
        simpa [msg, createPre, trace, RetainedXlot.flowActions,
          Frame.settlementCommits, hsettle, hopt]
          using combined

/-- Proof-indexed CREATE transport through full code-deposit settlement. -/
theorem GenericCreate.storageSegmentEffect_some_of_bodyEffect
    {dp : DeployParams} {ca : Adr}
    {sevm : Sevm} {pre post : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    {cevm : Evm} {raw : Execution}
    (hrun : GenericCreate sevm pre endowment newAddress mi ms
      (.some ⟨cevm, raw⟩) (.ok post))
    (childRun : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hcode : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hbody : ∀ (committed : Execution.commits raw = true),
      Nonempty (StorageSegmentEffect ca cevm.dyna
        (Execution.committedPost raw committed)
        (Exec.flowActions dp ca childRun))) :
    Nonempty (StorageSegmentEffect ca pre post
      (if Blanc.Frame.settlementCommits
          (Frame.ofCreate
            (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1))) raw = true
       then Exec.flowActions dp ca childRun else [])) := by
  have hnewNe : newAddress ≠ ca :=
    GenericCreate.newAddress_ne_of_installed hrun hcode
  unfold GenericCreate genericCreate.step at hrun
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at hrun
  repeat' split at hrun
  all_goals simp only [XStep.ofExcept, XStep.Run] at hrun
  all_goals try
    (have hxl : (some ⟨cevm, raw⟩ : Xlot) = none := hrun.1
     cases hxl)
  obtain ⟨result, hframe, hresume⟩ := hrun
  cases result with
  | error error =>
      simp [Resume.run, liftToExecution] at hresume
  | ok settled =>
      let createPre :=
        addAccessedAddress
          (((pre.withGasLeft
              (pre.gasLeft - except64th pre.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress
      let msg := createMsg sevm createPre (except64th pre.gasLeft)
        endowment newAddress ((pre.memory.read mi ms).1)
      have hprocess : ProcessCreateMessage msg
          (.some ⟨cevm, raw⟩) (.ok settled) := by
        simpa only [ProcessCreateMessage, msg, createPre, Mem.read] using hframe
      have hcreatePreStorage :
          Devm.getStor pre ca = Devm.getStor createPre ca := by
        have hstate : createPre.state =
            pre.state.incrNonce sevm.currentTarget := by
          rfl
        change pre.state.getStor ca = createPre.state.getStor ca
        rw [hstate]
        exact State.incrNonce_get_stor.symm
      have hcreatePreCode : pre.getCode ca = createPre.getCode ca := by
        have hstate : createPre.state =
            pre.state.incrNonce sevm.currentTarget := by
          rfl
        change pre.state.getCode ca = createPre.state.getCode ca
        rw [hstate]
        exact State.incrNonce_get_code.symm
      rcases ProcessCreateMessage.storageSegmentEffect_of_bodyEffect
          childRun hprocess (parent := createPre) rfl hnewNe hbody with
        ⟨effect⟩
      have hresumeState : post.state = settled.state :=
        Resume.create_state hresume.symm
      have hpostStorage : Devm.getStor settled ca = Devm.getStor post ca :=
        congrArg (fun state : State => state.getStor ca) hresumeState.symm
      have hpostCode : settled.getCode ca = post.getCode ca :=
        congrArg (fun state : State => state.getCode ca) hresumeState.symm
      dsimp only [msg, createPre] at effect
      exact ⟨by
        convert
          (StorageSegmentEffect.of_getStorCode_eq
              hcreatePreStorage hcreatePreCode).append
            (effect.append
              (StorageSegmentEffect.of_getStorCode_eq
                hpostStorage hpostCode)) using 1
        by_cases hretain : Blanc.Frame.settlementCommits
            (Frame.ofCreate
              (createMsg sevm
                (addAccessedAddress
                  (((pre.withGasLeft
                      (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                    []).incrNonce sevm.currentTarget) newAddress)
                (except64th pre.gasLeft) endowment newAddress
                ((pre.memory.read mi ms).1))) raw = true <;>
          simp [hretain]⟩

/-- A CREATE-family opcode with no interpreter child performs only
instruction preparation (and possibly a caller nonce increment), neither of
which changes storage or code at any address. -/
theorem GenericCreate.storageSegmentEffect_none
    {ca : Adr} {sevm : Sevm} {pre post : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    (hrun : GenericCreate sevm pre endowment newAddress mi ms
      .none (.ok post)) :
    Nonempty (StorageSegmentEffect ca pre post []) := by
  unfold GenericCreate genericCreate.step at hrun
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at hrun
  repeat' split at hrun
  all_goals simp only [XStep.ofExcept, XStep.Run] at hrun
  · cases hrun.2
  · cases hrun.2
  · cases hrun.2
  · rename_i hpush
    have hstate : post.state = pre.state := by
      rw [Except.ok.inj hrun.2, ← (Devm.push_of_push hpush).state]
      rfl
    exact ⟨StorageSegmentEffect.of_getStorCode_eq
      (congrArg (fun state : State => state.getStor ca) hstate.symm)
      (congrArg (fun state : State => state.getCode ca) hstate.symm)⟩
  · cases hrun.2
  · rename_i hpush
    have hstate : post.state = pre.state.incrNonce sevm.currentTarget := by
      rw [Except.ok.inj hrun.2, ← (Devm.push_of_push hpush).state]
      rfl
    have hstorage : Devm.getStor pre ca = Devm.getStor post ca :=
      State.incrNonce_get_stor.symm.trans
        (congrArg (fun state : State => state.getStor ca) hstate.symm)
    have hcode : pre.getCode ca = post.getCode ca :=
      State.incrNonce_get_code.symm.trans
        (congrArg (fun state : State => state.getCode ca) hstate.symm)
    exact ⟨StorageSegmentEffect.of_getStorCode_eq hstorage hcode⟩
  · exfalso
    obtain ⟨result, hframe, hresume⟩ := hrun
    obtain ⟨childMsg, hframe, hnone⟩ :
        ∃ childMsg : Msg,
          ProcessCreateMessage childMsg .none result ∧
          childMsg.codeAddress = .none :=
      ⟨_, hframe, rfl⟩
    obtain ⟨inner, hprocess, hsettle⟩ :=
      ProcessCreateMessage.iff_processMessage.mp hframe
    obtain ⟨raw, hbody, hprocessSettle⟩ :=
      ProcessMessage.iff_body.mp hprocess
    unfold FrameBody at hbody
    rcases htransfer :
        (processCreateMessage.msg childMsg).benvAfterTransfer with
      error | benv <;> rw [htransfer] at hbody
    · rw [hbody.2, processMessage.settle_error] at hprocessSettle
      rw [hprocessSettle, processCreateMessage.settle_error] at hsettle
      rw [hsettle] at hresume
      exact Resume.create_run_error hresume.symm
    · have hcodeAddress :
          ((processCreateMessage.msg childMsg).withBenv benv).codeAddress =
            .none := hnone
      obtain ⟨execution, hslot, -⟩ :=
        of_executeCode_noneCode hcodeAddress hbody
      cases hslot

/-- Contract-neutral recursive transport for the concrete filled slot of any
CALL/CREATE-family instruction.  Instruction prefixes preserve the installed
code and holder storage separately; the exact spawned frame supplies the
settlement-pruned child label. -/
theorem Xinst.storageSegmentEffect_some
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    {cevm : Evm} {raw : Execution} {settled : Devm}
    (hspawn : Xinst.step sevm pre x = .spawn frame resume)
    (hframe : RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled))
    (hresume : resume.run (.ok settled) = .ok post)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hdepth : cevm.sta.depth < depth)
    (hcode : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (htargetCode : frame.inner.currentTarget = ca →
      some frame.inner.code.toList = Prog.compile (weth10 dp))
    (hbelow : StorageSegmentTraceBelow dp ca depth) :
    Nonempty (StorageSegmentEffect ca pre post
      (if Blanc.Frame.settlementCommits frame raw = true
       then Exec.flowActions dp ca child else [])) := by
  rcases Xinst.step_shape sevm pre x with
    ⟨ex, hs, hprefix⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, hs⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, hs⟩ <;>
    rw [hs] at hspawn
  · cases hspawn
  · rcases genericCreate_step_spawn_exact hspawn with
      ⟨rfl, rfl⟩
    have grun : GenericCreate sevm d endowment newAddress mi ms
        (.some ⟨cevm, raw⟩) (.ok post) := by
      unfold GenericCreate XStep.Run
      rw [hspawn]
      exact ⟨.ok settled, hframe, hresume.symm⟩
    have hcodeD : some (d.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      rw [← hprefix.getCode ca]
      exact hcode
    rcases GenericCreate.storageSegmentEffect_some grun child hdepth
        hcodeD hbelow with ⟨effect⟩
    exact ⟨by
      simpa only [List.nil_append] using
        (StorageSegmentEffect.of_getStorCode_eq
          (hprefix.getStor ca) (hprefix.getCode ca)).append effect⟩
  · rcases genericCall_step_spawn_exact hspawn with
      ⟨rfl, rfl⟩
    have grun : GenericCall sevm d gas value caller target codeAddress
        stv isStatic ii isz oi osz code disablePrecompiles
        (.some ⟨cevm, raw⟩) (.ok post) := by
      unfold GenericCall XStep.Run
      rw [hspawn]
      exact ⟨.ok settled, hframe, hresume.symm⟩
    have hcodeD : some (d.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      rw [← hprefix.getCode ca]
      exact hcode
    have hcalleeCode : target = ca →
        some code.toList = Prog.compile (weth10 dp) := by
      simpa [Frame.ofCall, callMsg] using htargetCode
    rcases GenericCall.storageSegmentDelta_some grun child hdepth
        hcodeD hcalleeCode hbelow with ⟨effect⟩
    exact ⟨by
      simpa only [List.nil_append] using
        (StorageSegmentEffect.of_getStorCode_eq
          (hprefix.getStor ca) (hprefix.getCode ca)).append effect⟩

/-- Proof-indexed contract-neutral recursive transport.  The exact child
effect is threaded through the concrete filled interpreter slot. -/
theorem Xinst.storageSegmentEffect_some_of_bodyEffect
    {dp : DeployParams} {ca : Adr}
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    {cevm : Evm} {raw : Execution} {settled : Devm}
    (hspawn : Xinst.step sevm pre x = .spawn frame resume)
    (hframe : RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled))
    (hresume : resume.run (.ok settled) = .ok post)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hcode : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hbody : ∀ (committed : Execution.commits raw = true),
      Nonempty (StorageSegmentEffect ca cevm.dyna
        (Execution.committedPost raw committed)
        (Exec.flowActions dp ca child))) :
    Nonempty (StorageSegmentEffect ca pre post
      (if Blanc.Frame.settlementCommits frame raw = true
       then Exec.flowActions dp ca child else [])) := by
  rcases Xinst.step_shape sevm pre x with
    ⟨ex, hs, hprefix⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, hs⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, hs⟩ <;>
    rw [hs] at hspawn
  · cases hspawn
  · rcases genericCreate_step_spawn_exact hspawn with
      ⟨rfl, rfl⟩
    have grun : GenericCreate sevm d endowment newAddress mi ms
        (.some ⟨cevm, raw⟩) (.ok post) := by
      unfold GenericCreate XStep.Run
      rw [hspawn]
      exact ⟨.ok settled, hframe, hresume.symm⟩
    have hcodeD : some (d.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      rw [← hprefix.getCode ca]
      exact hcode
    rcases GenericCreate.storageSegmentEffect_some_of_bodyEffect
        grun child hcodeD hbody with ⟨effect⟩
    exact ⟨by
      simpa only [List.nil_append] using
        (StorageSegmentEffect.of_getStorCode_eq
          (hprefix.getStor ca) (hprefix.getCode ca)).append effect⟩
  · rcases genericCall_step_spawn_exact hspawn with
      ⟨rfl, rfl⟩
    have grun : GenericCall sevm d gas value caller target codeAddress
        stv isStatic ii isz oi osz code disablePrecompiles
        (.some ⟨cevm, raw⟩) (.ok post) := by
      unfold GenericCall XStep.Run
      rw [hspawn]
      exact ⟨.ok settled, hframe, hresume.symm⟩
    rcases GenericCall.storageSegmentEffect_some_of_bodyEffect
        grun child hbody with ⟨effect⟩
    exact ⟨by
      simpa only [List.nil_append] using
        (StorageSegmentEffect.of_getStorCode_eq
          (hprefix.getStor ca) (hprefix.getCode ca)).append effect⟩

/-- Contract-neutral childless interpreter transport. -/
theorem Xinst.storageSegmentEffect_none
    {ca : Adr} {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (hrun : Xinst.Run sevm pre x .none (.ok post)) :
    Nonempty (StorageSegmentEffect ca pre post []) := by
  unfold Xinst.Run at hrun
  rcases Xinst.step_shape sevm pre x with
    ⟨execution, hs, hframe⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, hs⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isStatic,
      ii, isz, oi, osz, code, disablePrecompiles, hprefix, _, _, _, hs⟩ <;>
    rw [hs] at hrun
  · obtain ⟨-, hpost⟩ := hrun
    rw [← hpost] at hframe
    exact ⟨StorageSegmentEffect.of_getStorCode_eq
      (hframe.getStor ca) (hframe.getCode ca)⟩
  · rcases GenericCreate.storageSegmentEffect_none hrun with ⟨effect⟩
    exact ⟨by
      simpa only [List.nil_append] using
        (StorageSegmentEffect.of_getStorCode_eq
          (hprefix.getStor ca) (hprefix.getCode ca)).append effect⟩
  · rcases GenericCall.storageSegmentEffect_none hrun with ⟨effect⟩
    exact ⟨by
      simpa only [List.nil_append] using
        (StorageSegmentEffect.of_getStorCode_eq
          (hprefix.getStor ca) (hprefix.getCode ca)).append effect⟩

/-- The exact remaining semantic target for one successful execution: a
chronological chain of operational segments whose multiset of owned labels is
exactly the canonical expansion of the rollback-pruned action traversal. -/
abbrev Exec.StorageSegmentTrace
    (dp : DeployParams) (ca : Adr)
    {pc : Nat} {sevm : Sevm} {pre post : Devm}
    (run : Exec pc sevm pre (.ok post)) : Type :=
  StorageSegmentEffect ca pre post
    (Blanc.Weth10.Exec.flowActions dp ca run)

/-- `RunCompiled` reconstruction may choose a different inhabitant of the same
`Exec` index, but the exact segment-trace target transports across that choice.
-/
def Exec.StorageSegmentTrace.congr_runs
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre post : Devm}
    {left right : Exec pc sevm pre (.ok post)}
    (trace : Blanc.Weth10.Exec.StorageSegmentTrace dp ca left) :
    Blanc.Weth10.Exec.StorageSegmentTrace dp ca right := by
  change StorageSegmentEffect ca pre post (Exec.flowActions dp ca left) at trace
  change StorageSegmentEffect ca pre post (Exec.flowActions dp ca right)
  rw [← Exec.flowActions_eq_of_runs (dp := dp) (ca := ca) left right]
  exact trace

/-- Constructing the exact execution segment trace is sufficient for the full
per-holder and aggregate storage theorem, with no endpoint equation supplied
as a premise. -/
theorem Exec.StorageSegmentTrace.storageFlowAccounting
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre post : Devm}
    {run : Exec pc sevm pre (.ok post)}
    (trace : Blanc.Weth10.Exec.StorageSegmentTrace dp ca run) :
    StorageFlowAccounting ca pre post
      (Blanc.Weth10.Exec.flowActions dp ca run) :=
  trace.delta.storageFlowAccounting

/-- A committed foreign frame contributes no root WETH10 action; its complete
ledger is exactly its settlement-pruned proper-descendant traversal. -/
theorem Exec.flowActions_eq_descendantActions_of_currentTarget_ne
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (hforeign : sevm.currentTarget ≠ ca) :
    Exec.flowActions dp ca run = Exec.descendantActions dp ca run := by
  rw [Exec.flowActions_eq_root_append_descendants run committed]
  simp [Blanc.Weth10.Exec.Frame.flowAction?, Blanc.Weth10.Exec.Frame.exactInvocation,
    exactInvocation, Exec.Frame.ofRun, hforeign]

/-- Proof-indexed storage predicate consumed by `lift_core`.  Root freshness
and direct code ownership are demanded only when this exact execution is at
the installed contract. -/
def Exec.CoreStorageSound (dp : DeployParams) (ca : Adr)
    (pc : Nat) (sevm : Sevm) (pre : Devm) (out : Execution) : Prop :=
  ∀ (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true),
    Prog.At (weth10 dp) ca pc sevm pre →
    (sevm.currentTarget = ca →
      Exec.Frame.IsRoot (Exec.Frame.ofRun run committed) ∧
        sevm.codeAddress = some ca) →
    Nonempty (StorageSegmentEffect ca pre
      (Execution.committedPost out committed)
      (Exec.flowActions dp ca run))

/-- The sole contract-specific obligation left by the generic interpreter
recursion.  It receives the concrete successful `Exec` witness and the exact
strong-depth hypotheses generated by `lift_core`. -/
def CompiledBodyStorageHandler (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm},
    Prog.Run sevm pre (weth10 dp) post →
    sevm.currentTarget = ca →
    ForallDeeperAt sevm.depth ca (weth10 dp)
      (fun pc s d out _ => Exec.CoreStorageSound dp ca pc s d out) →
    ∀ (run : Exec 0 sevm pre (.ok post))
      (committed : Execution.commits (.ok post) = true),
      Prog.At (weth10 dp) ca 0 sevm pre →
      (sevm.currentTarget = ca →
        Exec.Frame.IsRoot (Exec.Frame.ofRun run committed) ∧
          sevm.codeAddress = some ca) →
      Nonempty (StorageSegmentEffect ca pre post
        (Exec.flowActions dp ca run))

/-- Frame-oriented form of the sole compiled obligation.  This is the natural
consumer of selector chronology because it exposes the authentic frame and
its proof-indexed descendant ledger directly. -/
def CompiledFrameStorageHandler (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ (frame : Exec.Frame),
    Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame →
    ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out) →
    Nonempty (StorageSegmentEffect ca frame.pre frame.post
      (Exec.flowActions dp ca frame.run))

/-- Root/direct hypotheses reconstruct the authentic frame context required
by the selector classifier. -/
theorem CompiledFrameStorageHandler.compiledBodyStorageHandler
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledFrameStorageHandler dp ca) :
    CompiledBodyStorageHandler dp ca := by
  intro sevm pre post hrun htarget hdeeper run committed installed rootDirect
  let frame := Exec.Frame.ofRun run committed
  have hrootDirect := rootDirect htarget
  have context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame := by
    refine ⟨hrootDirect.1, ?_, installed⟩
    refine ⟨rfl, htarget, hrootDirect.2, ?_⟩
    exact (installed.2 htarget).1
  exact handler frame context hdeeper

/-- Direct-code version of retained CALL accounting.  Unlike the earlier
depth-bounded abstraction, this consumes `lift_core`'s exact strong-depth
hypothesis and therefore also proves the authentic child's direct code owner.
-/
theorem ProcessMessageTrace.storageSegmentDelta_of_forallDeeperAt
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {msg : Msg} {post parent : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hparent : parent.state = msg.benv.state)
    (hdepth : msg.depth < depth)
    (hcode : some (parent.getCode ca).toList =
      Prog.compile (weth10 dp))
    (htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp))
    (htargetDirect : msg.currentTarget = ca →
      msg.codeAddress = some ca)
    (hdeeper : ForallDeeperAt depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Nonempty (StorageSegmentEffect ca parent post
      (Blanc.Weth10.RetainedXlot.flowActions dp ca trace.retained)) := by
  rcases trace with ⟨slot, retained, hprocess⟩
  cases retained with
  | none =>
      exact ProcessMessage.storageSegmentEffect_none hprocess hparent
  | @some pc sevm pre out run =>
      have henter : (Frame.ofCall msg).enter =
          .run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hprocess).1
      rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hevm⟩
      simp only [Frame.ofCall] at htransfer hevm
      have hpreState : pre.state = benv.state := by
        have component := congrArg (fun evm : Evm => evm.dyna.state) hevm
        change pre.state = (initEvm (msg.withBenv benv)).dyna.state
        exact component
      have hsevm : sevm = initSevm (msg.withBenv benv) :=
        congrArg (fun evm : Evm => evm.sta) hevm
      have hpc : pc = 0 := by
        simpa [initEvm] using congrArg (fun evm : Evm => evm.pc) hevm
      have hmemory : pre.memory = Mem.empty := by
        have component := congrArg (fun evm : Evm => evm.dyna.memory) hevm
        change pre.memory = (initEvm (msg.withBenv benv)).dyna.memory
        simpa [initEvm, initDevm, Msg.withBenv] using component
      have hentryStorage : Devm.getStor parent ca = Devm.getStor pre ca := by
        exact (congrArg (fun state : State => state.getStor ca) hparent).trans <|
          (benvAfterTransfer_getStor_eq htransfer ca).symm.trans <|
            (congrArg (fun state : State => state.getStor ca) hpreState).symm
      have hentryCodeEq : parent.getCode ca = pre.getCode ca := by
        exact (congrArg (fun state : State => state.getCode ca) hparent).trans <|
          (benvAfterTransfer_ok_getCode htransfer ca).symm.trans <|
            (congrArg (fun state : State => state.getCode ca) hpreState).symm
      have hentryCode : some (pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        calc
          some (pre.getCode ca).toList =
              some (benv.state.getCode ca).toList := by
            change some (pre.state.getCode ca).toList = _
            rw [hpreState]
          _ = some (msg.benv.state.getCode ca).toList := by
            rw [benvAfterTransfer_ok_getCode htransfer ca]
          _ = some (parent.getCode ca).toList := by
            change some (msg.benv.state.getCode ca).toList =
              some (parent.state.getCode ca).toList
            rw [hparent]
          _ = _ := hcode
      have hat : Prog.At (weth10 dp) ca pc sevm pre := by
        refine ⟨hentryCode, ?_⟩
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        refine ⟨?_, hpc⟩
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using htargetCode hmsgTarget
      have hdirect : sevm.currentTarget = ca →
          sevm.codeAddress = some ca := by
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using htargetDirect hmsgTarget
      by_cases hcommit : Execution.commits out = true
      · cases out with
        | error error => simp [Execution.commits] at hcommit
        | ok raw =>
            have hchildDepth : sevm.depth < depth := by
              rw [hsevm]
              simpa [initSevm, Msg.withBenv] using hdepth
            have hcore := hdeeper pc sevm pre (.ok raw) run
              hchildDepth hat
            rcases hcore run hcommit hat
                (fun htarget =>
                  ⟨⟨hpc, hmemory⟩, hdirect htarget⟩) with
              ⟨childEffect⟩
            have hpostState : post.state = raw.state :=
              ProcessMessage.ok_state_eq_committedPost hprocess hcommit
            have hpostStorage : Devm.getStor raw ca =
                Devm.getStor post ca :=
              congrArg (fun state : State => state.getStor ca)
                hpostState.symm
            have hpostCode : raw.getCode ca = post.getCode ca :=
              congrArg (fun state : State => state.getCode ca)
                hpostState.symm
            exact ⟨by
              simpa only [List.nil_append, List.append_nil,
                RetainedXlot.flowActions] using
                (StorageSegmentEffect.of_getStorCode_eq
                    hentryStorage hentryCodeEq).append
                  (childEffect.append
                    (StorageSegmentEffect.of_getStorCode_eq
                      hpostStorage hpostCode))⟩
      · have hactions : Exec.flowActions dp ca run = [] :=
          Exec.flowActions_eq_nil_of_not_commits run hcommit
        have hpostState : post.state = msg.benv.state :=
          ProcessMessage.ok_state_eq_of_not_commits hprocess hcommit
        have hstorage : Devm.getStor parent ca = Devm.getStor post ca :=
          congrArg (fun state : State => state.getStor ca)
            (hparent.trans hpostState.symm)
        have hcodeEq : parent.getCode ca = post.getCode ca :=
          congrArg (fun state : State => state.getCode ca)
            (hparent.trans hpostState.symm)
        simp only [Blanc.Weth10.RetainedXlot.flowActions, hactions]
        exact ⟨StorageSegmentEffect.of_getStorCode_eq hstorage hcodeEq⟩

/-- A callback that targets the installed WETH10 address executes the
installed code itself: the delegated-code alternative is impossible for the
compiled runtime bytecode. -/
theorem callbackCode_eq_compiled_of_target_eq
    {dp : DeployParams} {ca target : Adr} {state : Devm}
    {code : ByteArray} {delegated : Bool}
    (installed : some (state.getCode ca).toList =
      Prog.compile (weth10 dp))
    (targetEq : target = ca)
    (delegation :
      (getDelegatedCodeAddress (state.getCode target) = none ∧
          code = state.getCode target ∧ delegated = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (state.getCode target) =
          some delegatedTarget ∧
        code = state.getCode delegatedTarget ∧ delegated = true)) :
    some code.toList = Prog.compile (weth10 dp) := by
  rcases delegation with
    ⟨_, hcode, _⟩ | ⟨delegatedTarget, hdelegated, _, _⟩
  · rw [hcode, targetEq]
    exact installed
  · exfalso
    have hnot : ¬ isValidDelegation (state.getCode ca) :=
      not_delegation_of_compile installed
    apply hnot
    unfold getDelegatedCodeAddress at hdelegated
    split at hdelegated
    · rename_i hvalid
      rw [targetEq] at hvalid
      exact hvalid
    · cases hdelegated

/-- Exact storage effect of a retained ERC-677 callback boundary.  The
existential `RetainedXlot` is for the very same slot named by the boundary's
parent `StepRun`, so selector chronology can identify its child label without
reconstructing an unrelated execution. -/
theorem RawTokenCallbackStepBoundary.storageSegmentEffect
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {self target : Adr}
    {rawTarget sel value tailLen inputSize : B256} {tail input : Bytes}
    {pre post : Devm}
    (callback : RawTokenCallbackStepBoundary dp e self target rawTarget sel
      value tailLen inputSize tail input pre post)
    (hself : e.currentTarget = ca)
    (installed : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreStorageSound dp ca pc sevm childPre out)) :
    ∃ (pc : Nat) (callPre callPost : Devm) (xl : Xlot)
        (retained : RetainedXlot xl),
      Ninst.StepRun pc e callPre Ninst.call xl (.ok callPost) ∧
      Nonempty (StorageSegmentEffect ca pre post
        (retained.flowActions dp ca)) := by
  rcases callback with
    ⟨targetEq, inputSizeEq, callPre, callPost, parent, child, xl,
      delegated, code, gasWord, avail, pc, hstep, hdepth, hstack,
      hinput, himage, hstorPre, hbalPre, hcodePre, hlogsPre,
      houtputPre, hparentState, hparentMemory, hparentLogs,
      hparentOutput, hdelegation, hfilled, hprocess, hclean,
      hresume, hcallPostState, hreturnData, hcallPostMemory,
      hcallPostStack, hcontinuation⟩
  obtain ⟨retained⟩ := exists_retainedXlot_of_filled hfilled
  let msg := callMsg e parent (min gasWord.toNat (except64th avail)) 0
    self target
    ((getDelegatedCodeAddress (callPre.getCode target)).getD target)
    true false input code delegated
  let trace : ProcessMessageTrace msg (.ok child) :=
    ⟨xl, retained, by simpa only [msg] using hprocess⟩
  have hcallPreCode : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← congrFun hcodePre ca]
    exact installed
  have hparent : callPre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < e.depth := by
    dsimp only [msg, callMsg]
    omega
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro htarget
    have htargetCa : target = ca := by
      simpa only [msg, callMsg] using htarget
    exact callbackCode_eq_compiled_of_target_eq hcallPreCode htargetCa
      hdelegation
  have htargetDirect : msg.currentTarget = ca →
      msg.codeAddress = some ca := by
    intro htarget
    have htargetCa : target = ca := by
      simpa only [msg, callMsg] using htarget
    have hnodel : getDelegatedCodeAddress (callPre.getCode ca) = none := by
      dsimp only [getDelegatedCodeAddress]
      rw [if_neg (not_delegation_of_compile hcallPreCode)]
    simp [msg, callMsg, htargetCa, hnodel]
  rcases trace.storageSegmentDelta_of_forallDeeperAt hparent hmsgDepth
      hcallPreCode htargetCode htargetDirect hdeeper with ⟨childEffect⟩
  have hprefix := StorageSegmentEffect.of_getStorCode_eq
    (congrFun hstorPre ca) (congrFun hcodePre ca)
  have hchildToCallPost := StorageSegmentEffect.of_getStorCode_eq
    (congrArg (fun state : State => state.getStor ca)
      hcallPostState.symm)
    (congrArg (fun state : State => state.getCode ca)
      hcallPostState.symm)
  obtain ⟨htailStor, _, htailCode⟩ :=
    of_run_call_boolReturn_preserves_fields dp hcontinuation
  have hsuffix := StorageSegmentEffect.of_getStorCode_eq
    (congrFun htailStor ca) (by simpa only [hself] using htailCode)
  have combined := hprefix.append
    (childEffect.append (hchildToCallPost.append hsuffix))
  exact ⟨pc, callPre, callPost, xl, retained, hstep, ⟨by
    simpa only [List.nil_append, List.append_nil, trace] using combined⟩⟩

/-- Indexed form of callback storage accounting.  The supplied retained
witness is the one selected by the enclosing compiled execution, so the
result keeps the callback ledger definitionally tied to that exact slot. -/
theorem RawTokenCallbackIndexedStepBoundary.storageSegmentEffect
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {self target : Adr}
    {rawTarget sel value tailLen inputSize : B256} {tail input : Bytes}
    {pre post callPre callPost parent child : Devm} {xl : Xlot}
    {pc : Nat}
    (callback : RawTokenCallbackIndexedStepBoundary dp e self target rawTarget
      sel value tailLen inputSize tail input pre post callPre callPost parent
      child xl pc)
    (retained : RetainedXlot xl)
    (hself : e.currentTarget = ca)
    (installed : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreStorageSound dp ca pc sevm childPre out)) :
    Nonempty (StorageSegmentEffect ca pre post
      (retained.flowActions dp ca)) := by
  rcases callback with
    ⟨_targetEq, _inputSizeEq, delegated, code, gasWord, avail, _hstep,
      hdepth, _hstack, _hinput, _himage, hstorPre, _hbalPre, hcodePre,
      _hlogsPre, _houtputPre, hparentState, _hparentMemory, _hparentLogs,
      _hparentOutput, hdelegation, _hfilled, hprocess, _hclean, _hresume,
      hcallPostState, _hreturnData, _hcallPostMemory, _hcallPostStack,
      hcontinuation⟩
  let msg := callMsg e parent (min gasWord.toNat (except64th avail)) 0
    self target
    ((getDelegatedCodeAddress (callPre.getCode target)).getD target)
    true false input code delegated
  let trace : ProcessMessageTrace msg (.ok child) :=
    ⟨xl, retained, by simpa only [msg] using hprocess⟩
  have hcallPreCode : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← congrFun hcodePre ca]
    exact installed
  have hparent : callPre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < e.depth := by
    dsimp only [msg, callMsg]
    omega
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro htarget
    have htargetCa : target = ca := by
      simpa only [msg, callMsg] using htarget
    exact callbackCode_eq_compiled_of_target_eq hcallPreCode htargetCa
      hdelegation
  have htargetDirect : msg.currentTarget = ca →
      msg.codeAddress = some ca := by
    intro htarget
    have htargetCa : target = ca := by
      simpa only [msg, callMsg] using htarget
    have hnodel : getDelegatedCodeAddress (callPre.getCode ca) = none := by
      dsimp only [getDelegatedCodeAddress]
      rw [if_neg (not_delegation_of_compile hcallPreCode)]
    simp [msg, callMsg, htargetCa, hnodel]
  rcases trace.storageSegmentDelta_of_forallDeeperAt hparent hmsgDepth
      hcallPreCode htargetCode htargetDirect hdeeper with ⟨childEffect⟩
  have hprefix := StorageSegmentEffect.of_getStorCode_eq
    (congrFun hstorPre ca) (congrFun hcodePre ca)
  have hchildToCallPost := StorageSegmentEffect.of_getStorCode_eq
    (congrArg (fun state : State => state.getStor ca)
      hcallPostState.symm)
    (congrArg (fun state : State => state.getCode ca)
      hcallPostState.symm)
  obtain ⟨htailStor, _, htailCode⟩ :=
    of_run_call_boolReturn_preserves_fields dp hcontinuation
  have hsuffix := StorageSegmentEffect.of_getStorCode_eq
    (congrFun htailStor ca) (by simpa only [hself] using htailCode)
  have combined := hprefix.append
    (childEffect.append (hchildToCallPost.append hsuffix))
  exact ⟨by
    simpa only [List.nil_append, List.append_nil, trace] using combined⟩

/-- Exact storage effect of the retained flash-borrower callback, ending at
the concrete parent state immediately after CALL resume. -/
theorem RawFlashCallbackStepBoundary.storageSegmentEffect
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {self receiver : Adr} {amount inputSize : B256}
    {callbackInput : Bytes} {pre mid : Devm}
    (callback : RawFlashCallbackStepBoundary e self receiver amount inputSize
      callbackInput pre mid)
    (_hself : e.currentTarget = ca)
    (installed : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreStorageSound dp ca pc sevm childPre out)) :
    ∃ (pc : Nat) (xl : Xlot) (retained : RetainedXlot xl),
      Ninst.StepRun pc e pre Ninst.call xl (.ok mid) ∧
      Nonempty (StorageSegmentEffect ca pre mid
        (retained.flowActions dp ca)) := by
  rcases callback with
    ⟨parent, child, xl, delegated, na, code, gasWord, avail, pc, hstep,
      hdepth, hstack, hpref, hparentState, hparentMemory, hparentLogs,
      hparentOutput, hdelegation, hfilled, hprocess, hclean, hlength,
      hmagic, hresume, hmidState, hreturnData, hmidStack, hmidLogs,
      hmidOutput⟩
  obtain ⟨retained⟩ := exists_retainedXlot_of_filled hfilled
  let msg := callMsg e parent (min gasWord.toNat (except64th avail)) 0
    self receiver na true false callbackInput code delegated
  let trace : ProcessMessageTrace msg (.ok child) :=
    ⟨xl, retained, by simpa only [msg] using hprocess⟩
  have hparent : pre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < e.depth := by
    dsimp only [msg, callMsg]
    omega
  have hdelegation' :
      (getDelegatedCodeAddress (pre.getCode receiver) = none ∧
          code = pre.getCode receiver ∧ delegated = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (pre.getCode receiver) =
          some delegatedTarget ∧
        code = pre.getCode delegatedTarget ∧ delegated = true) := by
    rcases hdelegation with ⟨hnone, _, hcode, hdel⟩ |
      ⟨delegatedTarget, hsome, _, hcode, hdel⟩
    · exact Or.inl ⟨hnone, hcode, hdel⟩
    · exact Or.inr ⟨delegatedTarget, hsome, hcode, hdel⟩
  have hresolved : receiver = ca → na = ca := by
    intro hreceiver
    have hnone : getDelegatedCodeAddress (pre.getCode receiver) = none := by
      rw [hreceiver]
      dsimp only [getDelegatedCodeAddress]
      rw [if_neg (not_delegation_of_compile installed)]
    rcases hdelegation with ⟨_, hna, _, _⟩ | ⟨_, hsome, _, _, _⟩
    · exact hna.trans hreceiver
    · simp [hnone] at hsome
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro htarget
    have hreceiver : receiver = ca := by
      simpa only [msg, callMsg] using htarget
    exact callbackCode_eq_compiled_of_target_eq installed hreceiver
      hdelegation'
  have htargetDirect : msg.currentTarget = ca →
      msg.codeAddress = some ca := by
    intro htarget
    have hreceiver : receiver = ca := by
      simpa only [msg, callMsg] using htarget
    simp [msg, callMsg, hresolved hreceiver]
  rcases trace.storageSegmentDelta_of_forallDeeperAt hparent hmsgDepth
      installed htargetCode htargetDirect hdeeper with ⟨childEffect⟩
  have hchildToMid := StorageSegmentEffect.of_getStorCode_eq
    (congrArg (fun state : State => state.getStor ca) hmidState.symm)
    (congrArg (fun state : State => state.getCode ca) hmidState.symm)
  have combined := childEffect.append hchildToMid
  exact ⟨pc, xl, retained, hstep, ⟨by
    simpa only [List.append_nil, trace] using combined⟩⟩

/-- Indexed flash-callback storage accounting using the exact retained child
selected by the enclosing compiled chronology. -/
theorem RawFlashCallbackIndexedStepBoundary.storageSegmentEffect
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {self receiver : Adr} {amount inputSize : B256}
    {callbackInput : Bytes} {pre mid parent child : Devm}
    {xl : Xlot} {pc : Nat}
    (callback : RawFlashCallbackIndexedStepBoundary e self receiver amount
      inputSize callbackInput pre mid parent child xl pc)
    (retained : RetainedXlot xl)
    (_hself : e.currentTarget = ca)
    (installed : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreStorageSound dp ca pc sevm childPre out)) :
    Nonempty (StorageSegmentEffect ca pre mid
      (retained.flowActions dp ca)) := by
  rcases callback with
    ⟨delegated, code, gasWord, avail, _hstep, hdepth, _hstack, _hpref,
      hparentState, _hparentMemory, _hparentLogs, _hparentOutput,
      hdelegation, _hfilled, hprocess, _hclean, _hlength, _hmagic,
      _hresume, hmidState, _hreturnData, _hmidStack, _hmidLogs,
      _hmidOutput⟩
  let msg := callMsg e parent (min gasWord.toNat (except64th avail)) 0
    self receiver
    ((getDelegatedCodeAddress (pre.getCode receiver)).getD receiver)
    true false callbackInput code delegated
  let trace : ProcessMessageTrace msg (.ok child) :=
    ⟨xl, retained, by simpa only [msg] using hprocess⟩
  have hparent : pre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < e.depth := by
    dsimp only [msg, callMsg]
    omega
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro htarget
    have hreceiver : receiver = ca := by
      simpa only [msg, callMsg] using htarget
    exact callbackCode_eq_compiled_of_target_eq installed hreceiver
      hdelegation
  have htargetDirect : msg.currentTarget = ca →
      msg.codeAddress = some ca := by
    intro htarget
    have hreceiver : receiver = ca := by
      simpa only [msg, callMsg] using htarget
    have hnodel : getDelegatedCodeAddress (pre.getCode ca) = none := by
      dsimp only [getDelegatedCodeAddress]
      rw [if_neg (not_delegation_of_compile installed)]
    simp [msg, callMsg, hreceiver, hnodel]
  rcases trace.storageSegmentDelta_of_forallDeeperAt hparent hmsgDepth
      installed htargetCode htargetDirect hdeeper with ⟨childEffect⟩
  have hchildToMid := StorageSegmentEffect.of_getStorCode_eq
    (congrArg (fun state : State => state.getStor ca) hmidState.symm)
    (congrArg (fun state : State => state.getCode ca) hmidState.symm)
  exact ⟨by
    simpa only [List.append_nil, trace] using
      childEffect.append hchildToMid⟩

/-- Exact storage effect of the accepted value-CALL inside a redemption
prefix, including the `iszero` success guard and final stack burn. -/
theorem BurnCallPrefix.storageSegmentEffect
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {pre callPre guardPost : Devm}
    {owner : Adr} {amount target : B256}
    (burn : BurnCallPrefix e pre callPre guardPost owner amount target)
    (_hself : e.currentTarget = ca)
    (installed : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreStorageSound dp ca pc sevm childPre out)) :
    ∃ (pc : Nat) (callPost : Devm) (xl : Xlot)
        (retained : RetainedXlot xl),
      Ninst.StepRun pc e callPre Ninst.call xl (.ok callPost) ∧
      Nonempty (StorageSegmentEffect ca callPre guardPost
        (retained.flowActions dp ca)) := by
  rcases burn.2.2.2.2.2.2.2 with
    ⟨gasWord, callPost, testPost, hstack, hcall, hiszero, hpop⟩
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
      ⟨parent, child, xl, delegated, na, code, availableGas, pc, hstep,
        hdepth, hcallStack, hparentState, hparentMemory, hparentLogs,
        hparentOutput, hdelegation, hfilled, hprocess, hclean,
        hresume, hcallPostState, hreturnData, hcallPostMemory,
        hcallPostStack⟩
    obtain ⟨retained⟩ := exists_retainedXlot_of_filled hfilled
    let msg := callMsg e parent
      (min gasWord.toNat (except64th availableGas) +
        (if amount.toNat = 0 then 0 else gCallStipend))
      amount e.currentTarget target.toAdr na true false
      ((callPre.memory.read (0 : B256).toNat (0 : B256).toNat).1)
      code delegated
    let trace : ProcessMessageTrace msg (.ok child) :=
      ⟨xl, retained, by simpa only [msg] using hprocess⟩
    have hparent : callPre.state = msg.benv.state := by
      simpa only [msg, callMsg] using hparentState.symm
    have hmsgDepth : msg.depth < e.depth := by
      dsimp only [msg, callMsg]
      omega
    have hdelegation' :
        (getDelegatedCodeAddress (callPre.getCode target.toAdr) = none ∧
            code = callPre.getCode target.toAdr ∧ delegated = false) ∨
        (∃ delegatedTarget,
          getDelegatedCodeAddress (callPre.getCode target.toAdr) =
            some delegatedTarget ∧
          code = callPre.getCode delegatedTarget ∧ delegated = true) := by
      rcases hdelegation with ⟨hnone, _, hcode, hdel⟩ |
        ⟨delegatedTarget, hsome, _, hcode, hdel⟩
      · exact Or.inl ⟨hnone, hcode, hdel⟩
      · exact Or.inr ⟨delegatedTarget, hsome, hcode, hdel⟩
    have hresolved : target.toAdr = ca → na = ca := by
      intro htargetCa
      have hnone :
          getDelegatedCodeAddress (callPre.getCode target.toAdr) = none := by
        rw [htargetCa]
        dsimp only [getDelegatedCodeAddress]
        rw [if_neg (not_delegation_of_compile installed)]
      rcases hdelegation with ⟨_, hna, _, _⟩ | ⟨_, hsome, _, _, _⟩
      · exact hna.trans htargetCa
      · simp [hnone] at hsome
    have htargetCode : msg.currentTarget = ca →
        some msg.code.toList = Prog.compile (weth10 dp) := by
      intro htarget
      have htargetCa : target.toAdr = ca := by
        simpa only [msg, callMsg] using htarget
      exact callbackCode_eq_compiled_of_target_eq installed htargetCa
        hdelegation'
    have htargetDirect : msg.currentTarget = ca →
        msg.codeAddress = some ca := by
      intro htarget
      have htargetCa : target.toAdr = ca := by
        simpa only [msg, callMsg] using htarget
      simp [msg, callMsg, hresolved htargetCa]
    rcases trace.storageSegmentDelta_of_forallDeeperAt hparent hmsgDepth
        installed htargetCode htargetDirect hdeeper with ⟨childEffect⟩
    have hguardState : guardPost.state = child.state := by
      calc
        guardPost.state = testPost.state := hpop.state.symm
        _ = callPost.state :=
          (Ninst.Hinv.inv (f := Devm.state) hiszero).symm
        _ = child.state := hcallPostState
    have hchildToGuard := StorageSegmentEffect.of_getStorCode_eq
      (congrArg (fun state : State => state.getStor ca)
        hguardState.symm)
      (congrArg (fun state : State => state.getCode ca)
        hguardState.symm)
    have combined := childEffect.append hchildToGuard
    exact ⟨pc, callPost, xl, retained, hstep, ⟨by
      simpa only [List.append_nil, trace] using combined⟩⟩

/-- Exact storage accounting for the particular retained child named by an
accepted value-call trace.  Unlike the existential burn-prefix adapter, this
form preserves the trace's retained index definitionally for selector
chronology consumers. -/
theorem AcceptedValueCallTrace.storageSegmentEffect
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {target value : B256} {callPre guardPost : Devm}
    (trace : AcceptedValueCallTrace e target value callPre guardPost)
    (_hself : e.currentTarget = ca)
    (installed : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreStorageSound dp ca pc sevm childPre out)) :
    Nonempty (StorageSegmentEffect ca callPre guardPost
      (Blanc.Weth10.RetainedXlot.flowActions dp ca
        trace.retained.retained)) := by
  have hparent : callPre.state = trace.childMessage.benv.state := by
    rw [trace.childMessage_eq]
    simpa only [callMsg] using trace.parent_state.symm
  have hmsgDepth : trace.childMessage.depth < e.depth := by
    rw [trace.childMessage_eq]
    simp only [callMsg]
    exact Nat.sub_lt trace.depth_pos (by decide)
  have htargetCode : trace.childMessage.currentTarget = ca →
      some trace.childMessage.code.toList = Prog.compile (weth10 dp) := by
    intro htarget
    rw [trace.childMessage_eq] at htarget ⊢
    have htarget' : target.toAdr = ca := by
      simpa only [callMsg] using htarget
    exact callbackCode_eq_compiled_of_target_eq installed htarget'
      trace.delegation_resolution
  have htargetDirect : trace.childMessage.currentTarget = ca →
      trace.childMessage.codeAddress = some ca := by
    intro htarget
    rw [trace.childMessage_eq] at htarget ⊢
    have htarget' : target.toAdr = ca := by
      simpa only [callMsg] using htarget
    have hnodel : getDelegatedCodeAddress (callPre.getCode ca) = none := by
      dsimp only [getDelegatedCodeAddress]
      rw [if_neg (not_delegation_of_compile installed)]
    simp only [callMsg, htarget', hnodel, Option.getD_none]
  rcases trace.retained.storageSegmentDelta_of_forallDeeperAt hparent
      hmsgDepth installed htargetCode htargetDirect hdeeper with
    ⟨childEffect⟩
  have hchildToGuard := StorageSegmentEffect.of_getStorCode_eq
    (congrArg (fun state : State => state.getStor ca)
      trace.guard_state.symm)
    (congrArg (fun state : State => state.getCode ca)
      trace.guard_state.symm)
  exact ⟨by
    simpa only [List.append_nil] using childEffect.append hchildToGuard⟩

/-- The exact childless instruction line underlying both `receiveEther` and
the payable `deposit` selector.  Naming it makes the terminal cursor shape
explicit instead of relying on higher-order unification through aliases. -/
private def mintCallerLine : Line :=
  [caller, sload, callvalue, add, caller, sstore, callvalue] ++
  mstoreAt 0 ++
  [caller, pushB256 0, pushB256 Blanc.transferEvent] ++
  logWith 2 0 1

private theorem weth10Main_entry_sourceShape (dp : DeployParams) :
    (weth10 dp).main =
      [Ninst.calldatasize, Ninst.iszero] +++
        (receiveEther <?>
          (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))) := by
  rfl

private theorem receiveEther_sourceShape :
    receiveEther = mintCallerLine +++ Func.stop := by
  rfl

private theorem deposit_sourceShape :
    deposit = mintCallerLine +++ Func.stop := by
  rfl

private theorem depositTo_sourceShape :
    depositTo = mintToPrefix +++ Func.stop := by
  rfl

/-- Transport a cursor across a small source-shape equality before peeling a
childless prefix.  Keeping the equality symbolic avoids changing the cursor's
proof-indexed action field in downstream equations. -/
private theorem Exec.Frame.CompiledCursor.peelChildlessLine_of_sourceShape
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {line : Line} {tail : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table body final)
    (shape : body = line +++ tail)
    (hchildless : ∀ n ∈ line, NinstIsChildless n) :
    ∃ tailCursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table tail final,
      Line.Run frame.sevm cursor.pre line tailCursor.pre ∧
      tailCursor.actions = cursor.actions := by
  subst body
  exact cursor.peelChildlessLine hchildless

/-- A proof-indexed cursor over a childless line ending in a terminal
instruction has crossed every proper descendant of its retained frame.
This is the reusable chronology close for receive/deposit and the call-free
selector arms. -/
theorem Exec.Frame.CompiledCursor.finishChildlessLine
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

/-- Finish a childless terminal line after exposing a concrete body through a
small named source-shape equality. -/
private theorem Exec.Frame.CompiledCursor.finishChildlessLine_of_sourceShape
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {line : Line} {i : Linst} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table body final)
    (shape : body = line +++ Func.last i)
    (hchildless : ∀ n ∈ line, NinstIsChildless n) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = cursor.actions := by
  subst body
  exact cursor.finishChildlessLine hchildless

/-- A childless prefix followed by a binary choice of childless terminal
lines also crosses no descendant action, independently of which concrete arm
the original execution selected. -/
theorem Exec.Frame.CompiledCursor.finishChildlessBranch
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {linePrefix left right : Line} {leftLast rightLast : Linst}
    {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table
      (linePrefix +++
        ((left +++ Func.last leftLast) <?>
          (right +++ Func.last rightLast))) final)
    (hprefix : ∀ n ∈ linePrefix, NinstIsChildless n)
    (hleft : ∀ n ∈ left, NinstIsChildless n)
    (hright : ∀ n ∈ right, NinstIsChildless n) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = cursor.actions := by
  rcases cursor.peelChildlessLine hprefix with
    ⟨branchCursor, _hline, hbranchActions⟩
  rcases branchCursor.selectBranchWithActions with hleftArm | hrightArm
  · rcases hleftArm with ⟨arm, harmActions⟩
    exact (arm.finishChildlessLine hright).trans
      (harmActions.trans hbranchActions)
  · rcases hrightArm with ⟨arm, harmActions⟩
    exact (arm.finishChildlessLine hleft).trans
      (harmActions.trans hbranchActions)

/-- Finish a two-arm childless terminal body after one symbolic source-shape
rewrite. -/
private theorem Exec.Frame.CompiledCursor.finishChildlessBranch_of_sourceShape
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {linePrefix left right : Line}
    {leftLast rightLast : Linst} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CompiledCursor dp ca frame fs table body final)
    (shape : body =
      linePrefix +++
        ((left +++ Func.last leftLast) <?>
          (right +++ Func.last rightLast)))
    (hprefix : ∀ n ∈ linePrefix, NinstIsChildless n)
    (hleft : ∀ n ∈ left, NinstIsChildless n)
    (hright : ∀ n ∈ right, NinstIsChildless n) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = cursor.actions := by
  subst body
  exact cursor.finishChildlessBranch hprefix hleft hright

/-- The empty-calldata receive arm contains no recursive instruction, so its
original retained execution has no proper-descendant flow actions. -/
theorem Exec.Frame.descendantFlowActions_eq_nil_of_receive
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hempty : frame.sevm.data.length.toB256 = 0) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = [] := by
  rcases Blanc.Weth10.Exec.Frame.compiledMainCursor (frame := frame) context with
    ⟨mainCursor, hmainActions⟩
  rcases mainCursor.peelChildlessLine_of_sourceShape
      (weth10Main_entry_sourceShape dp)
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
  rw [hempty] at hflagPrefix
  have hone : ((0 : B256) =? 0) = 1 := by simp [B256.eqCheck]
  rw [hone] at hflagPrefix
  rcases entryBranchCursor.selectBranchSucc (flag := (1 : B256))
      (by decide) hflagPrefix with
    ⟨receiveCursor, _hstack, hreceiveActions⟩
  have hdesc := receiveCursor.finishChildlessLine_of_sourceShape
    receiveEther_sourceShape
    (by simp [mintCallerLine, NinstIsChildless, Ninst.pushB256,
      mstoreAt, logWith])
  exact hdesc.trans (hreceiveActions.trans
    (hentryActions.trans hmainActions))

/-- The payable `deposit` dispatch body is the same childless mint body as
the receive arm, so its exact original-frame descendant ledger is empty. -/
theorem Exec.Frame.descendantFlowActions_eq_nil_of_deposit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = depositSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = [] := by
  have hmem : (Sevm.selector frame.sevm, deposit) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [depositSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursor (frame := frame) context hnonempty hmem with
    ⟨bodyCursor, _hstack, hbodyActions⟩
  have hdesc := bodyCursor.finishChildlessLine_of_sourceShape
    deposit_sourceShape
    (by simp [mintCallerLine, NinstIsChildless, Ninst.pushB256,
      mstoreAt, logWith])
  exact hdesc.trans hbodyActions

/-- The payable `depositTo` dispatch body is childless through its terminal
stop, hence it also has an empty proper-descendant ledger. -/
theorem Exec.Frame.descendantFlowActions_eq_nil_of_depositTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = depositToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = [] := by
  have hmem : (Sevm.selector frame.sevm, depositTo) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [depositToSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursor (frame := frame) context hnonempty hmem with
    ⟨bodyCursor, _hstack, hbodyActions⟩
  have hdesc := bodyCursor.finishChildlessLine_of_sourceShape
    depositTo_sourceShape
    (by simp [mintToPrefix, addressArg, arg, cdl,
      normalizeAddress, pushAddressMask, NinstIsChildless,
      Ninst.pushB256, mstoreAt, logWith])
  exact hdesc.trans hbodyActions

/-- Any listed nonpayable selector whose guarded body is a childless line
ending in a terminal instruction has an empty proper-descendant ledger. -/
theorem Exec.Frame.descendantFlowActions_eq_nil_of_nonpayableChildless
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {line : Line} {i : Linst}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm,
      nonpayable (line +++ Func.last i)) ∈ weth10Funcs dp)
    (hchildless : ∀ n ∈ line, NinstIsChildless n) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = [] := by
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursor (frame := frame) context hnonempty hmem with
    ⟨wrapperCursor, _hstack, hwrapperActions⟩
  rcases wrapperCursor.enterNonpayable with
    ⟨bodyCursor, _hbodyStack, hbodyActions⟩
  exact (bodyCursor.finishChildlessLine hchildless).trans
    (hbodyActions.trans hwrapperActions)

private def transferSelectLine : Line := arg 0 ++ [iszero]

private def transferBalanceCheckLine : Line :=
  loadCallerBalanceAmount 1 ++ balanceTooSmall

private def transferNonzeroSuccessLine : Line :=
  debitLoadedBalance ++
  addressArg 0 ++ [dup 0, sload] ++ arg 1 ++
  [add, swap 0, sstore, caller] ++ arg 1 ++ addressArg 0 ++
  emitTransfer ++
  [pushB256 1] ++ mstoreAt 0 ++ pushList [32, 0]

private theorem transfer_sourceShape :
    transfer =
      transferSelectLine +++
        (transferZeroThen returnTrue <?>
          transferNonzeroThen returnTrue) := by
  rfl

private theorem transferNonzeroThen_returnTrue_sourceShape :
    transferNonzeroThen returnTrue =
      transferBalanceCheckLine +++
        ((.call transferBalanceErrorSlot) <?>
          (transferNonzeroSuccessLine +++ Func.ret)) := by
  rfl

/-- A successful ordinary `transfer` takes the nonzero-recipient branch.
Both that branch and its terminal return are childless; the only other inner
branch tail-calls a fixed reverter and therefore cannot be the cursor of this
committed frame. -/
theorem Exec.Frame.descendantFlowActions_eq_nil_of_transferNonzero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 0 ≠ 0) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = [] := by
  have hmem :
      (Sevm.selector frame.sevm, nonpayable transfer) ∈ weth10Funcs dp := by
    rw [hselector]
    simp [transferSelector, weth10Funcs]
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursor (frame := frame) context hnonempty hmem with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions⟩
  rcases wrapperCursor.enterNonpayable with
    ⟨transferCursor, _htransferStack, htransferActions⟩
  rcases transferCursor.peelChildlessLine_of_sourceShape
      transfer_sourceShape
      (by simp [transferSelectLine, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨targetBranchCursor, htargetLine, htargetActions⟩
  have htargetPrefix :
      [Sevm.argWord frame.sevm 0 =? 0] <<+
        targetBranchCursor.pre.stack := by
    unfold transferSelectLine at htargetLine
    rcases of_run_append (arg 0) htargetLine with
      ⟨afterArg, harg, hzeroLine⟩
    rcases Line.of_run_cons hzeroLine with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    exact prefix_of_iszero hzero (prefix_of_arg nil_pref harg)
  have htargetCheck : (Sevm.argWord frame.sevm 0 =? 0) = 0 := by
    simp [B256.eqCheck, hto]
  rw [htargetCheck] at htargetPrefix
  rcases targetBranchCursor.selectBranchZero htargetPrefix with
    ⟨nonzeroCursor, _hnonzeroStack, hnonzeroActions⟩
  rcases nonzeroCursor.peelChildlessLine_of_sourceShape
      transferNonzeroThen_returnTrue_sourceShape
      (by simp [transferBalanceCheckLine, loadCallerBalanceAmount,
        balanceTooSmall, arg, cdl, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨balanceBranchCursor, _hbalanceLine, hbalanceActions⟩
  rcases balanceBranchCursor.selectBranchWithActions with
      hsuccess | herror
  · rcases hsuccess with ⟨successCursor, hsuccessActions⟩
    have hdesc := successCursor.finishChildlessLine
      (by simp [transferNonzeroSuccessLine, debitLoadedBalance,
        addressArg, arg, cdl, normalizeAddress, pushAddressMask,
        emitTransfer, Blanc.transferFromLog, NinstIsChildless,
        Ninst.pushB256, mstoreAt, logWith, pushList])
    exact hdesc.trans (hsuccessActions.trans
      (hbalanceActions.trans (hnonzeroActions.trans
        (htargetActions.trans
          (htransferActions.trans hwrapperActions)))))
  · rcases herror with ⟨errorCursor, _herrorActions⟩
    rcases errorCursor.enterCall context.invocation.2.2.2 with
      ⟨body, hget, bodyCursor, _hbodyActions⟩
    have hbody : body = transferBalanceError := by
      simpa [weth10Aux, transferBalanceErrorSlot] using hget.symm
    subst body
    exact (Func.not_run_revWith
      (Func.Run.of_runCompiled bodyCursor.run)).elim

private def returnTrueLine : Line :=
  [pushB256 1] ++ mstoreAt 0 ++ pushList [32, 0]

private def approveLine : Line := approvePrefix ++ returnTrueLine

/-- Downstream copy of the private compiled-classifier projection: once the
exact invocation guard and primary atom are fixed, the `some` payload of
`flowAction?` is definitionally determined. -/
private theorem action_eq_of_primaryFlowAtom
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

/-- Normalizing an ABI address word is exactly round-tripping it through
`Adr`.  The compiled classifier keeps its equivalent lemma private, so the
proof-indexed accounting layer records its own local algebraic copy. -/
private theorem normalizedAddressArg_eq_toAdr_toB256_local
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

/-- Executable evidence that a nonempty invocation selector belongs to none
of the ten primary-flow families. -/
structure SelectsNoPrimaryFlow (e : Sevm) : Prop where
  deposit : Sevm.selector e ≠ depositSelector
  depositTo : Sevm.selector e ≠ depositToSelector
  depositToAndCall : Sevm.selector e ≠ depositToAndCallSelector
  transfer : Sevm.selector e ≠ transferSelector
  transferAndCall : Sevm.selector e ≠ transferAndCallSelector
  transferFrom : Sevm.selector e ≠ transferFromSelector
  withdraw : Sevm.selector e ≠ withdrawSelector
  withdrawTo : Sevm.selector e ≠ withdrawToSelector
  withdrawFrom : Sevm.selector e ≠ withdrawFromSelector
  flashLoan : Sevm.selector e ≠ flashLoanSelector

theorem SelectsNoPrimaryFlow.primaryFlowAtom_eq_none
    {e : Sevm} (selected : SelectsNoPrimaryFlow e)
    (hnonempty : e.data.length.toB256 ≠ 0) :
    primaryFlowAtom e = none := by
  simp [primaryFlowAtom, hnonempty, selected.deposit,
    selected.depositTo, selected.depositToAndCall, selected.transfer,
    selected.transferAndCall, selected.transferFrom, selected.withdraw,
    selected.withdrawTo, selected.withdrawFrom, selected.flashLoan]

theorem Exec.Frame.flowAction_eq_none_of_selectsNoPrimaryFlow
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (selected : SelectsNoPrimaryFlow frame.sevm)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = none := by
  simp [Blanc.Weth10.Exec.Frame.flowAction?, context.invocation,
    selected.primaryFlowAtom_eq_none hnonempty]

/-- The ordinary `approve` body contains no recursive instruction, so a
successful authentic frame has no proper-descendant WETH flow actions. -/
theorem Exec.Frame.descendantFlowActions_eq_nil_of_approve
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "approve" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (approveLine +++ Func.ret)) ∈ weth10Funcs dp := by
    rw [hselector]
    simp only [weth10Funcs, List.mem_cons]
    exact Or.inr (Or.inl (by rfl))
  have hchildless : ∀ n ∈ approveLine, NinstIsChildless n := by
    simp [approveLine, approvePrefix, returnTrueLine,
      argCopy, cdc, arg, cdl, allowanceKeyFromMemory, Blanc.logApprove,
      NinstIsChildless, Ninst.pushB256, mstoreAt, logWith, pushList]
  exact Blanc.Weth10.Exec.Frame.descendantFlowActions_eq_nil_of_nonpayableChildless (frame := frame)
    context hnonempty hmem hchildless

/-- An actual execution starting with installed WETH10 code preserves that
code at `ca`; this is kept separate from holder-storage accounting. -/
theorem Exec.installedCodeEq
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre post : Devm}
    (run : Exec pc sevm pre (.ok post))
    (installed : Prog.At (weth10 dp) ca pc sevm pre) :
    pre.getCode ca = post.getCode ca := by
  have hnonempty : (pre.getCode ca).toList ≠ [] := by
    intro hempty
    exact Prog.compile_ne_nil
      (installed.1.symm.trans (congrArg some hempty))
  exact (Exec.preserves_getCode run ca hnonempty).symm

theorem Exec.installedCodeEq_committed
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (installed : Prog.At (weth10 dp) ca pc sevm pre) :
    pre.getCode ca =
      (Execution.committedPost out committed).getCode ca := by
  cases out with
  | error error => simp [Execution.commits] at committed
  | ok post => exact Exec.installedCodeEq run installed

/-- Once selector chronology supplies the child deltas, the classified root
ledger and global code preservation close the exact frame effect. -/
theorem Exec.Frame.ClassifiedActionLedger.storageSegmentEffect
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (ledger : Blanc.Weth10.Exec.Frame.ClassifiedActionLedger dp ca frame action)
    (accounting : RichStorageAccounting ca frame.pre frame.post action
      (Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame)) :
    Nonempty (StorageSegmentEffect ca frame.pre frame.post
      (Exec.flowActions dp ca frame.run)) := by
  have hcode : frame.pre.getCode ca = frame.post.getCode ca :=
    Exec.installedCodeEq_committed frame.run frame.committed
      ledger.rich.authentic.installed
  rcases accounting.storageSegmentEffect hcode with ⟨effect⟩
  rw [ledger.actions_eq]
  exact ⟨effect⟩

/-- An authentic unclassified root has no root action, so an exact delta for
its chronological descendants is already the full frame effect. -/
theorem Exec.Frame.HasNoWethBalanceOwnEffect.storageSegmentEffect
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (own : Blanc.Weth10.Exec.Frame.HasNoWethBalanceOwnEffect dp ca frame)
    (delta : StorageSegmentDelta ca frame.pre frame.post
      (Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame)) :
    Nonempty (StorageSegmentEffect ca frame.pre frame.post
      (Exec.flowActions dp ca frame.run)) := by
  have hcode : frame.pre.getCode ca = frame.post.getCode ca :=
    Exec.installedCodeEq_committed frame.run frame.committed
      own.authentic.installed
  have hframe : Exec.Frame.ofRun frame.run frame.committed = frame := by
    cases frame
    rfl
  have hroot : Blanc.Weth10.Exec.Frame.flowAction? dp ca
      (Exec.Frame.ofRun frame.run frame.committed) = none := by
    rw [hframe]
    exact own.unclassified
  rw [Exec.flowActions_eq_root_append_descendants
      frame.run frame.committed]
  simp only [hroot, Option.toList, List.nil_append]
  change Nonempty (StorageSegmentEffect ca frame.pre frame.post
    (Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame))
  exact ⟨⟨delta, hcode⟩⟩

/-- Final proof-indexed storage package for one authentic compiled frame.
The flow arm combines the classified root ledger with exact local/child
composition; the no-flow arm accounts only for the actual descendants. -/
inductive Exec.Frame.HasProofIndexedStorageAccounting
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame) : Prop
  | flow {action : FlowAction}
      (ledger : Blanc.Weth10.Exec.Frame.ClassifiedActionLedger dp ca frame action)
      (accounting : RichStorageAccounting ca frame.pre frame.post action
        (Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame))
  | noFlow
      (own : Blanc.Weth10.Exec.Frame.HasNoWethBalanceOwnEffect dp ca frame)
      (accounting : NoFlowStorageAccounting ca frame.pre frame.post
        (Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame))

/-- Either exhaustive frame-accounting arm yields the exact storage effect
for the frame's complete settlement-pruned action ledger. -/
theorem Exec.Frame.HasProofIndexedStorageAccounting.storageSegmentEffect
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (accounting : Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame) :
    Nonempty (StorageSegmentEffect ca frame.pre frame.post
      (Exec.flowActions dp ca frame.run)) := by
  cases accounting with
  | flow ledger rich => exact ledger.storageSegmentEffect rich
  | noFlow own silent =>
      rcases silent.storageSegmentDelta with ⟨delta⟩
      exact own.storageSegmentEffect delta

/-- Every classified no-flow leaf except the two callback-bearing selectors
is silent for WETH balance storage through its public endpoint.  This is a
projection from the compiled operational classification, not an endpoint
assumption. -/
theorem Exec.Frame.HasNoWethBalanceOwnEffect.weth10Silent_of_not_recursive
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (own : Blanc.Weth10.Exec.Frame.HasNoWethBalanceOwnEffect dp ca frame)
    (happroveCall : Sevm.selector frame.sevm ≠ approveAndCallSelector)
    (hpermit : Sevm.selector frame.sevm ≠ permitSelector) :
    Stor.Weth10Silent (Devm.getStor frame.pre ca)
      (Devm.getStor frame.post ca) := by
  have htarget : frame.sevm.currentTarget = ca :=
    own.authentic.invocation.2.1
  have hcurrent : Stor.Weth10Silent
      (Devm.getStor frame.pre frame.sevm.currentTarget)
      (Devm.getStor frame.post frame.sevm.currentTarget) := by
    cases own.effect with
    | name _ silent => exact silent
    | approve _ silent => exact silent
    | totalSupply _ silent => exact silent
    | permitTypehash _ silent => exact silent
    | decimals _ silent => exact silent
    | domainSeparator _ silent => exact silent
    | maxFlashLoan _ silent => exact silent
    | balanceOf _ silent => exact silent
    | nonces _ silent => exact silent
    | callbackSuccess _ silent => exact silent
    | flashMinted _ silent => exact silent
    | symbol _ silent => exact silent
    | approveAndCall selected _ _ _ =>
        exact (happroveCall selected).elim
    | deploymentChainId _ silent => exact silent
    | permit selected _ => exact (hpermit selected).elim
    | flashFee _ silent => exact silent
    | allowance _ silent => exact silent
  simpa only [htarget] using hcurrent

/-- Turn exact childless chronology for a classified nonrecursive no-flow
leaf into the final proof-indexed storage package. -/
theorem Exec.Frame.HasNoWethBalanceOwnEffect.proofIndexed_of_childless
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (own : Blanc.Weth10.Exec.Frame.HasNoWethBalanceOwnEffect dp ca frame)
    (happroveCall : Sevm.selector frame.sevm ≠ approveAndCallSelector)
    (hpermit : Sevm.selector frame.sevm ≠ permitSelector)
    (chronology : Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = []) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame :=
  .noFlow own (.silent
    (own.weth10Silent_of_not_recursive happroveCall hpermit) chronology)

/-- A source function is childless-terminal when it consists of a line with
no recursive instruction followed by one terminal instruction. -/
def ChildlessTerminal (body : Func) : Prop :=
  ∃ (line : Line) (terminal : Linst),
    body = line +++ Func.last terminal ∧
    ∀ n ∈ line, NinstIsChildless n

/-- Concrete executable certificate for a childless, non-flow WETH selector.
It carries only selector/body membership and instruction shape; storage
silence is recovered from the compiled functional classifier. -/
def Exec.Frame.ChildlessNoFlowStorageCase
    (dp : DeployParams) (frame : Exec.Frame) : Prop :=
  ∃ body : Func,
    frame.sevm.data.length.toB256 ≠ 0 ∧
    (Sevm.selector frame.sevm, nonpayable body) ∈ weth10Funcs dp ∧
    ChildlessTerminal body ∧
    SelectsNoPrimaryFlow frame.sevm ∧
    Sevm.selector frame.sevm ≠ approveAndCallSelector ∧
    Sevm.selector frame.sevm ≠ permitSelector

/-- Every certified childless non-flow selector has exact proof-indexed
storage accounting for the original retained execution. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (branch : Blanc.Weth10.Exec.Frame.ChildlessNoFlowStorageCase dp frame) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  rcases branch with ⟨body, hnonempty, hmember,
    ⟨line, terminal, hbody, hchildless⟩,
    hnoFlow, hnotApproveCall, hnotPermit⟩
  have hmember' : (Sevm.selector frame.sevm,
      nonpayable (line +++ Func.last terminal)) ∈ weth10Funcs dp := by
    simpa only [← hbody] using hmember
  have chronology :=
    Blanc.Weth10.Exec.Frame.descendantFlowActions_eq_nil_of_nonpayableChildless (frame := frame) context
      hnonempty hmember' hchildless
  have hnone := Blanc.Weth10.Exec.Frame.flowAction_eq_none_of_selectsNoPrimaryFlow (frame := frame) context
    hnoFlow hnonempty
  have own := Blanc.Weth10.Exec.Frame.hasNoWethBalanceOwnEffect_of_recognized (frame := frame) context hnone
    ⟨nonpayable body, hmember⟩
  exact own.proofIndexed_of_childless hnotApproveCall hnotPermit chronology

/-- Generic packaging once a nonrecursive no-flow selector's exact original
cursor chronology has independently been closed. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_noFlowNil
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {body : Func}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmember : (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp)
    (hnoFlow : SelectsNoPrimaryFlow frame.sevm)
    (hnotApproveCall : Sevm.selector frame.sevm ≠ approveAndCallSelector)
    (hnotPermit : Sevm.selector frame.sevm ≠ permitSelector)
    (chronology : Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = []) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  have hnone := Blanc.Weth10.Exec.Frame.flowAction_eq_none_of_selectsNoPrimaryFlow (frame := frame) context
    hnoFlow hnonempty
  have own := Blanc.Weth10.Exec.Frame.hasNoWethBalanceOwnEffect_of_recognized (frame := frame) context hnone
    ⟨body, hmember⟩
  exact own.proofIndexed_of_childless hnotApproveCall hnotPermit chronology

/-!
The selector proofs below used to ask the kernel to reduce both Keccak calls in
each selector inequality.  Freeze each selector word once, then keep the
seventeen-word disjointness table entirely literal.  This is the same
small-shape boundary used by the deployment proofs: the expensive source
computation occurs once per named selector, while consumers only transport
already-normalized facts.
-/

private theorem primaryDepositSelector_word_eq :
    depositSelector = (0xd0e30db0 : B256) := by decide +kernel

private theorem primaryDepositToSelector_word_eq :
    depositToSelector = (0xb760faf9 : B256) := by decide +kernel

private theorem primaryDepositToAndCallSelector_word_eq :
    depositToAndCallSelector = (0x5ddb7d7e : B256) := by decide +kernel

private theorem primaryTransferSelector_word_eq :
    transferSelector = (0xa9059cbb : B256) := by decide +kernel

private theorem primaryTransferAndCallSelector_word_eq :
    transferAndCallSelector = (0x4000aea0 : B256) := by decide +kernel

private theorem primaryTransferFromSelector_word_eq :
    transferFromSelector = (0x23b872dd : B256) := by decide +kernel

private theorem primaryWithdrawSelector_word_eq :
    withdrawSelector = (0x2e1a7d4d : B256) := by decide +kernel

private theorem primaryWithdrawToSelector_word_eq :
    withdrawToSelector = (0x205c2878 : B256) := by decide +kernel

private theorem primaryWithdrawFromSelector_word_eq :
    withdrawFromSelector = (0x9555a942 : B256) := by decide +kernel

private theorem primaryFlashLoanSelector_word_eq :
    flashLoanSelector = (0x5cffe9de : B256) := by decide +kernel

private structure SelectorWordNoPrimaryFlow (word : B256) : Prop where
  deposit : word ≠ 0xd0e30db0
  depositTo : word ≠ 0xb760faf9
  depositToAndCall : word ≠ 0x5ddb7d7e
  transfer : word ≠ 0xa9059cbb
  transferAndCall : word ≠ 0x4000aea0
  transferFrom : word ≠ 0x23b872dd
  withdraw : word ≠ 0x2e1a7d4d
  withdrawTo : word ≠ 0x205c2878
  withdrawFrom : word ≠ 0x9555a942
  flashLoan : word ≠ 0x5cffe9de

private theorem SelectorWordNoPrimaryFlow.selectsNoPrimaryFlow
    {e : Sevm} {word : B256}
    (literal : SelectorWordNoPrimaryFlow word)
    (selected : Sevm.selector e = word) :
    SelectsNoPrimaryFlow e := by
  constructor
  · rw [selected, primaryDepositSelector_word_eq]
    exact literal.deposit
  · rw [selected, primaryDepositToSelector_word_eq]
    exact literal.depositTo
  · rw [selected, primaryDepositToAndCallSelector_word_eq]
    exact literal.depositToAndCall
  · rw [selected, primaryTransferSelector_word_eq]
    exact literal.transfer
  · rw [selected, primaryTransferAndCallSelector_word_eq]
    exact literal.transferAndCall
  · rw [selected, primaryTransferFromSelector_word_eq]
    exact literal.transferFrom
  · rw [selected, primaryWithdrawSelector_word_eq]
    exact literal.withdraw
  · rw [selected, primaryWithdrawToSelector_word_eq]
    exact literal.withdrawTo
  · rw [selected, primaryWithdrawFromSelector_word_eq]
    exact literal.withdrawFrom
  · rw [selected, primaryFlashLoanSelector_word_eq]
    exact literal.flashLoan

private theorem nameSelector_word_eq :
    selector "name" [] = (0x06fdde03 : B256) := by decide +kernel

private theorem approveSelector_word_eq :
    selector "approve" [.address, .uint256] =
      (0x095ea7b3 : B256) := by decide +kernel

private theorem totalSupplySelector_word_eq :
    selector "totalSupply" [] = (0x18160ddd : B256) := by decide +kernel

private theorem permitTypehashSelector_word_eq_local :
    selector "PERMIT_TYPEHASH" [] =
      (0x30adf81f : B256) := by decide +kernel

private theorem decimalsSelector_word_eq_local :
    selector "decimals" [] = (0x313ce567 : B256) := by decide +kernel

private theorem domainSeparatorSelector_word_eq :
    selector "DOMAIN_SEPARATOR" [] =
      (0x3644e515 : B256) := by decide +kernel

private theorem maxFlashLoanSelector_word_eq :
    selector "maxFlashLoan" [.address] =
      (0x613255ab : B256) := by decide +kernel

private theorem balanceOfSelector_word_eq :
    selector "balanceOf" [.address] =
      (0x70a08231 : B256) := by decide +kernel

private theorem noncesSelector_word_eq_local :
    selector "nonces" [.address] =
      (0x7ecebe00 : B256) := by decide +kernel

private theorem callbackSuccessSelector_word_eq :
    selector "CALLBACK_SUCCESS" [] =
      (0x8237e538 : B256) := by decide +kernel

private theorem flashMintedSelector_word_eq :
    selector "flashMinted" [] = (0x8b28d32f : B256) := by decide +kernel

private theorem symbolSelector_word_eq :
    selector "symbol" [] = (0x95d89b41 : B256) := by decide +kernel

private theorem deploymentChainIdSelector_word_eq :
    selector "deploymentChainId" [] =
      (0xcd0d0096 : B256) := by decide +kernel

private theorem approveAndCallSelector_word_eq :
    approveAndCallSelector = (0xcae9ca51 : B256) := by decide +kernel

private theorem permitSelector_word_eq :
    permitSelector = (0xd505accf : B256) := by decide +kernel

private theorem flashFeeSelector_word_eq_local :
    selector "flashFee" [.address, .uint256] =
      (0xd9d98ce4 : B256) := by decide +kernel

private theorem allowanceSelector_word_eq_local :
    selector "allowance" [.address, .address] =
      (0xdd62ed3e : B256) := by decide +kernel

private theorem nameSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0x06fdde03 := by constructor <;> decide +kernel

private theorem approveSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0x095ea7b3 := by constructor <;> decide +kernel

private theorem totalSupplySelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0x18160ddd := by constructor <;> decide +kernel

private theorem permitTypehashSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0x30adf81f := by constructor <;> decide +kernel

private theorem decimalsSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0x313ce567 := by constructor <;> decide +kernel

private theorem domainSeparatorSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0x3644e515 := by constructor <;> decide +kernel

private theorem maxFlashLoanSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0x613255ab := by constructor <;> decide +kernel

private theorem balanceOfSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0x70a08231 := by constructor <;> decide +kernel

private theorem noncesSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0x7ecebe00 := by constructor <;> decide +kernel

private theorem callbackSuccessSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0x8237e538 := by constructor <;> decide +kernel

private theorem flashMintedSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0x8b28d32f := by constructor <;> decide +kernel

private theorem symbolSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0x95d89b41 := by constructor <;> decide +kernel

private theorem deploymentChainIdSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0xcd0d0096 := by constructor <;> decide +kernel

private theorem approveAndCallSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0xcae9ca51 := by constructor <;> decide +kernel

private theorem permitSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0xd505accf := by constructor <;> decide +kernel

private theorem flashFeeSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0xd9d98ce4 := by constructor <;> decide +kernel

private theorem allowanceSelector_noPrimaryFlow : SelectorWordNoPrimaryFlow 0xdd62ed3e := by constructor <;> decide +kernel

private def nameLine : Line :=
  [pushB256 (Blanc.String.toBytes "Wrapped Ether v10").toB256,
    pushB256 120, shl] ++
  pushList [17, 32] ++ mstoreAt 0 ++ mstoreAt 1 ++ mstoreAt 2 ++
  pushList [96, 0]

private theorem name_childlessTerminal : ChildlessTerminal name := by
  exact ⟨nameLine, .ret, rfl, by
    simp [nameLine, NinstIsChildless, Ninst.pushB256,
      pushList, mstoreAt]⟩

private theorem approve_childlessTerminal : ChildlessTerminal approve := by
  exact ⟨approveLine, .ret, rfl, by
    simp [approveLine, approvePrefix, returnTrueLine,
      argCopy, cdc, arg, cdl, allowanceKeyFromMemory, Blanc.logApprove,
      NinstIsChildless, Ninst.pushB256, mstoreAt, logWith, pushList]⟩

/-- Exact proof-indexed accounting for the childless `name` view. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_name
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = selector "name" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow (frame := frame) context
  refine ⟨name, hnonempty, ?_, name_childlessTerminal, ?_, ?_, ?_⟩
  · rw [hselector]
    exact List.mem_cons.mpr (Or.inl rfl)
  · exact nameSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans nameSelector_word_eq)
  · rw [hselector, nameSelector_word_eq]
    decide +kernel
  · rw [hselector, nameSelector_word_eq]
    decide +kernel

private def returnWordLine (w : B256) : Line :=
  [pushB256 w] ++ mstoreAt 0 ++ pushList [32, 0]

private theorem returnWord_childlessTerminal (w : B256) :
    ChildlessTerminal (returnWord w) :=
  ⟨returnWordLine w, .ret, rfl, by
    simp [returnWordLine, NinstIsChildless, Ninst.pushB256,
      mstoreAt, pushList]⟩

/-- Exact proof-indexed accounting for the childless `PERMIT_TYPEHASH` view. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_permitTypehash
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "PERMIT_TYPEHASH" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow (frame := frame) context
  refine ⟨permitTypehash, hnonempty, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  · simpa only [permitTypehash] using
      returnWord_childlessTerminal PERMIT_TYPEHASH
  · exact permitTypehashSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans permitTypehashSelector_word_eq_local)
  · rw [hselector, permitTypehashSelector_word_eq_local]
    decide +kernel
  · rw [hselector, permitTypehashSelector_word_eq_local]
    decide +kernel

/-- Exact proof-indexed accounting for the childless `decimals` view. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_decimals
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = selector "decimals" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow (frame := frame) context
  refine ⟨decimals, hnonempty, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  · exact ⟨returnWordLine 0x12, .ret, rfl, by
      simp [returnWordLine, NinstIsChildless, Ninst.pushB256,
        mstoreAt, pushList]⟩
  · exact decimalsSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans decimalsSelector_word_eq_local)
  · rw [hselector, decimalsSelector_word_eq_local]
    decide +kernel
  · rw [hselector, decimalsSelector_word_eq_local]
    decide +kernel

/-- Exact proof-indexed accounting for the childless `CALLBACK_SUCCESS` view. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_callbackSuccess
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "CALLBACK_SUCCESS" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow (frame := frame) context
  refine ⟨callbackSuccess, hnonempty, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  · simpa only [callbackSuccess] using
      returnWord_childlessTerminal CALLBACK_SUCCESS
  · exact callbackSuccessSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans callbackSuccessSelector_word_eq)
  · rw [hselector, callbackSuccessSelector_word_eq]
    decide +kernel
  · rw [hselector, callbackSuccessSelector_word_eq]
    decide +kernel

private def totalSupplyLine : Line :=
  [selfbalance] ++ pushFlashMintedSlot ++ [sload, add] ++
  mstoreAt 0 ++ pushList [32, 0]

private theorem totalSupply_childlessTerminal :
    ChildlessTerminal totalSupply :=
  ⟨totalSupplyLine, .ret, rfl, by
    simp [totalSupplyLine, pushFlashMintedSlot, NinstIsChildless,
      Ninst.pushB256, mstoreAt, pushList]⟩

private def balanceOfLine : Line :=
  arg 0 ++ [sload] ++ mstoreAt 0 ++ pushList [32, 0]

private theorem balanceOf_childlessTerminal :
    ChildlessTerminal balanceOfEndpoint :=
  ⟨balanceOfLine, .ret, rfl, by
    simp [balanceOfLine, arg, cdl, NinstIsChildless,
      Ninst.pushB256, mstoreAt, pushList]⟩

private def noncesLine : Line :=
  arg 0 ++ tagNonceKey ++ [sload] ++ mstoreAt 0 ++ pushList [32, 0]

private theorem nonces_childlessTerminal : ChildlessTerminal nonces :=
  ⟨noncesLine, .ret, rfl, by
    simp [noncesLine, arg, cdl, tagNonceKey, NinstIsChildless,
      Ninst.pushB256, mstoreAt, pushList]⟩

private def flashMintedLine : Line :=
  pushFlashMintedSlot ++ [sload] ++ mstoreAt 0 ++ pushList [32, 0]

private theorem flashMinted_childlessTerminal :
    ChildlessTerminal flashMinted :=
  ⟨flashMintedLine, .ret, rfl, by
    simp [flashMintedLine, pushFlashMintedSlot, NinstIsChildless,
      Ninst.pushB256, mstoreAt, pushList]⟩

private def symbolLine : Line :=
  [pushB256 (Blanc.String.toBytes "WETH10").toB256,
    pushB256 208, shl] ++
  pushList [6, 32] ++ mstoreAt 0 ++ mstoreAt 1 ++ mstoreAt 2 ++
  pushList [96, 0]

private theorem symbol_childlessTerminal : ChildlessTerminal symbol :=
  ⟨symbolLine, .ret, rfl, by
    simp [symbolLine, NinstIsChildless, Ninst.pushB256,
      pushList, mstoreAt]⟩

private def deploymentChainIdLine (dp : DeployParams) : Line :=
  [pushDeployWord dp.deploymentChainId] ++
  mstoreAt 0 ++ pushList [32, 0]

private theorem deploymentChainId_childlessTerminal (dp : DeployParams) :
    ChildlessTerminal (deploymentChainId dp) :=
  ⟨deploymentChainIdLine dp, .ret, rfl, by
    simp [deploymentChainIdLine, pushDeployWord, NinstIsChildless,
      Ninst.pushB256, mstoreAt, pushList]⟩

private def allowanceLine : Line :=
  argCopy 0 0 2 ++ allowanceKeyFromMemory ++ [sload] ++
  mstoreAt 0 ++ pushList [32, 0]

private theorem allowance_childlessTerminal : ChildlessTerminal allowance :=
  ⟨allowanceLine, .ret, rfl, by
    simp [allowanceLine, argCopy, cdc, allowanceKeyFromMemory,
      NinstIsChildless, Ninst.pushB256, mstoreAt, pushList]⟩

/-- Exact proof-indexed accounting for the childless `totalSupply` view. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_totalSupply
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = selector "totalSupply" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow (frame := frame) context
  refine ⟨totalSupply, hnonempty, ?_, totalSupply_childlessTerminal,
    ?_, ?_, ?_⟩
  · rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  · exact totalSupplySelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans totalSupplySelector_word_eq)
  · rw [hselector, totalSupplySelector_word_eq]
    decide +kernel
  · rw [hselector, totalSupplySelector_word_eq]
    decide +kernel

/-- Exact proof-indexed accounting for the childless `balanceOf` view. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_balanceOf
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "balanceOf" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow (frame := frame) context
  refine ⟨balanceOfEndpoint, hnonempty, ?_, balanceOf_childlessTerminal,
    ?_, ?_, ?_⟩
  · rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  · exact balanceOfSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans balanceOfSelector_word_eq)
  · rw [hselector, balanceOfSelector_word_eq]
    decide +kernel
  · rw [hselector, balanceOfSelector_word_eq]
    decide +kernel

/-- Exact proof-indexed accounting for the childless `nonces` view. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_nonces
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = selector "nonces" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow (frame := frame) context
  refine ⟨nonces, hnonempty, ?_, nonces_childlessTerminal, ?_, ?_, ?_⟩
  · rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  · exact noncesSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans noncesSelector_word_eq_local)
  · rw [hselector, noncesSelector_word_eq_local]
    decide +kernel
  · rw [hselector, noncesSelector_word_eq_local]
    decide +kernel

/-- Exact proof-indexed accounting for the childless `flashMinted` view. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_flashMinted
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = selector "flashMinted" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow (frame := frame) context
  refine ⟨flashMinted, hnonempty, ?_, flashMinted_childlessTerminal,
    ?_, ?_, ?_⟩
  · rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  · exact flashMintedSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans flashMintedSelector_word_eq)
  · rw [hselector, flashMintedSelector_word_eq]
    decide +kernel
  · rw [hselector, flashMintedSelector_word_eq]
    decide +kernel

/-- Exact proof-indexed accounting for the childless `symbol` view. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_symbol
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = selector "symbol" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow (frame := frame) context
  refine ⟨symbol, hnonempty, ?_, symbol_childlessTerminal, ?_, ?_, ?_⟩
  · rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  · exact symbolSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans symbolSelector_word_eq)
  · rw [hselector, symbolSelector_word_eq]
    decide +kernel
  · rw [hselector, symbolSelector_word_eq]
    decide +kernel

/-- Exact proof-indexed accounting for the childless deployment-chain view. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_deploymentChainId
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "deploymentChainId" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow (frame := frame) context
  refine ⟨deploymentChainId dp, hnonempty, ?_,
    deploymentChainId_childlessTerminal dp, ?_, ?_, ?_⟩
  · rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  · exact deploymentChainIdSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans deploymentChainIdSelector_word_eq)
  · rw [hselector, deploymentChainIdSelector_word_eq]
    decide +kernel
  · rw [hselector, deploymentChainIdSelector_word_eq]
    decide +kernel

/-- Exact proof-indexed accounting for the childless `allowance` view. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_allowance
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "allowance" [.address, .address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow (frame := frame) context
  refine ⟨allowance, hnonempty, ?_, allowance_childlessTerminal,
    ?_, ?_, ?_⟩
  · rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  · exact allowanceSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans allowanceSelector_word_eq_local)
  · rw [hselector, allowanceSelector_word_eq_local]
    decide +kernel
  · rw [hselector, allowanceSelector_word_eq_local]
    decide +kernel

private def domainSelectLine (dp : DeployParams) : Line :=
  [chainid, dup 0, pushDeployWord dp.deploymentChainId, eq]

private def domainCachedLine (dp : DeployParams) : Line :=
  [pop, pushDeployWord dp.cachedDomainSeparator] ++
  mstoreAt 0 ++ pushList [32, 0]

private def domainFreshLine : Line :=
  calculateDomainSeparator ++ mstoreAt 0 ++ pushList [32, 0]

private theorem domainSeparator_sourceShape (dp : DeployParams) :
    domainSeparator dp =
      domainSelectLine dp +++
        ((domainCachedLine dp +++ Func.ret) <?>
          (domainFreshLine +++ Func.ret)) := by
  rfl

/-- Both executable arms of `DOMAIN_SEPARATOR` are childless, so its exact
original-frame descendant action ledger is empty. -/
theorem Exec.Frame.descendantFlowActions_eq_nil_of_domainSeparator
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "DOMAIN_SEPARATOR" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable (domainSeparator dp)) ∈ weth10Funcs dp := by
    rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursor (frame := frame) context hnonempty hmem with
    ⟨wrapperCursor, _hstack, hwrapperActions⟩
  rcases wrapperCursor.enterNonpayable with
    ⟨bodyCursor, _hbodyStack, hbodyActions⟩
  have hdesc := bodyCursor.finishChildlessBranch_of_sourceShape
    (domainSeparator_sourceShape dp)
    (by simp [domainSelectLine, pushDeployWord, NinstIsChildless])
    (by simp [domainCachedLine, pushDeployWord, NinstIsChildless,
      Ninst.pushB256, mstoreAt, pushList])
    (by simp [domainFreshLine, calculateDomainSeparator,
      NinstIsChildless, Ninst.pushB256, mstoreAt, pushList])
  exact hdesc.trans (hbodyActions.trans hwrapperActions)

/-- Exact proof-indexed accounting for both childless domain-separator arms. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_domainSeparator
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "DOMAIN_SEPARATOR" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  have hmember : (Sevm.selector frame.sevm,
      nonpayable (domainSeparator dp)) ∈ weth10Funcs dp := by
    rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_noFlowNil (frame := frame) context
    hnonempty hmember
  · exact domainSeparatorSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans domainSeparatorSelector_word_eq)
  · rw [hselector, domainSeparatorSelector_word_eq]
    decide +kernel
  · rw [hselector, domainSeparatorSelector_word_eq]
    decide +kernel
  · exact Blanc.Weth10.Exec.Frame.descendantFlowActions_eq_nil_of_domainSeparator (frame := frame)
      context hselector hnonempty

private def maxFlashLoanSelectLine : Line := arg 0 ++ [address, eq]

private def maxFlashLoanAvailableLine : Line :=
  pushFlashMintedSlot ++
  [sload, pushB256 (Nat.toB256 maxFlashMinted), sub] ++
  mstoreAt 0 ++ pushList [32, 0]

private theorem maxFlashLoan_sourceShape :
    maxFlashLoan =
      maxFlashLoanSelectLine +++
        ((maxFlashLoanAvailableLine +++ Func.ret) <?>
          (returnWordLine 0 +++ Func.ret)) := by
  rfl

/-- Both successful `maxFlashLoan` result arms are childless. -/
theorem Exec.Frame.descendantFlowActions_eq_nil_of_maxFlashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "maxFlashLoan" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable maxFlashLoan) ∈ weth10Funcs dp := by
    rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursor (frame := frame) context hnonempty hmem with
    ⟨wrapperCursor, _hstack, hwrapperActions⟩
  rcases wrapperCursor.enterNonpayable with
    ⟨bodyCursor, _hbodyStack, hbodyActions⟩
  have hdesc := bodyCursor.finishChildlessBranch_of_sourceShape
    maxFlashLoan_sourceShape
    (by simp [maxFlashLoanSelectLine, arg, cdl,
      NinstIsChildless, Ninst.pushB256])
    (by simp [maxFlashLoanAvailableLine, pushFlashMintedSlot,
      NinstIsChildless, Ninst.pushB256, mstoreAt, pushList])
    (by simp [returnWordLine, NinstIsChildless,
      Ninst.pushB256, mstoreAt, pushList])
  exact hdesc.trans (hbodyActions.trans hwrapperActions)

/-- Exact proof-indexed accounting for both `maxFlashLoan` result arms. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_maxFlashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "maxFlashLoan" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  have hmember : (Sevm.selector frame.sevm,
      nonpayable maxFlashLoan) ∈ weth10Funcs dp := by
    rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_noFlowNil (frame := frame) context
    hnonempty hmember
  · exact maxFlashLoanSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans maxFlashLoanSelector_word_eq)
  · rw [hselector, maxFlashLoanSelector_word_eq]
    decide +kernel
  · rw [hselector, maxFlashLoanSelector_word_eq]
    decide +kernel
  · exact Blanc.Weth10.Exec.Frame.descendantFlowActions_eq_nil_of_maxFlashLoan (frame := frame)
      context hselector hnonempty

private def flashFeeSelectLine : Line :=
  arg 0 ++ [address, eq, iszero]

private theorem flashFee_sourceShape :
    flashFee =
      flashFeeSelectLine +++
        ((.call flashTokenErrorSlot) <?>
          (returnWordLine 0 +++ Func.ret)) := by
  rfl

/-- The successful `flashFee` arm is childless.  The other source arm enters
the fixed `flashTokenError` reverter and therefore cannot be the successful
cursor of this retained frame. -/
theorem Exec.Frame.descendantFlowActions_eq_nil_of_flashFee
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "flashFee" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = [] := by
  have hmem : (Sevm.selector frame.sevm,
      nonpayable flashFee) ∈ weth10Funcs dp := by
    rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursor (frame := frame) context hnonempty hmem with
    ⟨wrapperCursor, _hstack, hwrapperActions⟩
  rcases wrapperCursor.enterNonpayable with
    ⟨bodyCursor, _hbodyStack, hbodyActions⟩
  rcases bodyCursor.peelChildlessLine_of_sourceShape
      flashFee_sourceShape
      (by simp [flashFeeSelectLine, arg, cdl,
        NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, _hline, hbranchActions⟩
  rcases branchCursor.selectBranchWithActions with hsuccess | herror
  · rcases hsuccess with ⟨successCursor, hsuccessActions⟩
    have hdesc := successCursor.finishChildlessLine
      (by simp [returnWordLine, NinstIsChildless,
        Ninst.pushB256, mstoreAt, pushList])
    exact hdesc.trans (hsuccessActions.trans
      (hbranchActions.trans (hbodyActions.trans hwrapperActions)))
  · rcases herror with ⟨errorCursor, _herrorActions⟩
    rcases errorCursor.enterCall context.invocation.2.2.2 with
      ⟨body, hget, errorBodyCursor, _herrorBodyActions⟩
    have hbody : body = flashTokenError := by
      simpa [weth10Aux, flashTokenErrorSlot] using hget.symm
    subst body
    exact (Func.not_run_revWith
      (Func.Run.of_runCompiled errorBodyCursor.run)).elim

/-- Exact proof-indexed accounting for successful `flashFee`. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_flashFee
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "flashFee" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  have hmember : (Sevm.selector frame.sevm,
      nonpayable flashFee) ∈ weth10Funcs dp := by
    rw [hselector]
    simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    aesop
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_noFlowNil (frame := frame) context
    hnonempty hmember
  · exact flashFeeSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans flashFeeSelector_word_eq_local)
  · rw [hselector, flashFeeSelector_word_eq_local]
    decide +kernel
  · rw [hselector, flashFeeSelector_word_eq_local]
    decide +kernel
  · exact Blanc.Weth10.Exec.Frame.descendantFlowActions_eq_nil_of_flashFee (frame := frame)
      context hselector hnonempty

/-- Selector chronology provider expected from the concrete compiled WETH10
body.  It consumes only the authentic frame and the recursive deeper-frame
soundness generated by `lift_core`; its result is the operational package
above, never an assumed endpoint equation. -/
def CompiledStorageAccountingProvider
    (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ (frame : Exec.Frame),
    Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame →
    ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out) →
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame

/-- A concrete proof-indexed selector chronology provider is exactly the
remaining compiled-frame handler needed by the generic interpreter lift. -/
theorem CompiledStorageAccountingProvider.compiledFrameStorageHandler
    {dp : DeployParams} {ca : Adr}
    (provider : CompiledStorageAccountingProvider dp ca) :
    CompiledFrameStorageHandler dp ca := by
  intro frame context hdeeper
  exact (provider frame context hdeeper).storageSegmentEffect

/-- Exact proof-indexed accounting for the childless receive mint. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_receive
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hempty : frame.sevm.data.length.toB256 = 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | none =>
      have hprimary : primaryFlowAtom frame.sevm ≠ none := by
        simp [primaryFlowAtom, hempty]
      unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation] at haction
      cases hatom : primaryFlowAtom frame.sevm with
      | none => exact (hprimary hatom).elim
      | some atom => simp [hatom] at haction
  | some action =>
      have ledger :=
        Blanc.Weth10.Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some (frame := frame)
          context haction
      have chronology :=
        Blanc.Weth10.Exec.Frame.descendantFlowActions_eq_nil_of_receive (frame := frame) context hempty
      rcases frame with ⟨pc, e, pre, out, run, committed⟩
      cases out with
      | error err => simp [Execution.commits] at committed
      | ok post =>
          have hpc : pc = 0 := context.root.1
          subst pc
          have heffect := receive_exec_effect dp context.memory_wf
            context.memory_reads_empty run context.invocation.2.2.2 hempty
          have hinc := heffect.1
          have htarget : e.currentTarget = ca :=
            context.invocation.2.1
          rw [htarget] at hinc
          have haction' := haction
          simp [Blanc.Weth10.Exec.Frame.flowAction?, context.invocation,
            primaryFlowAtom, primaryDebitProvenance, hempty] at haction'
          symm at haction'
          subst action
          apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.flow ledger
          apply RichStorageAccounting.ordinaryMint
          · exact LocalActionSegment.ordinaryMint
              e.caller.toB256 e.caller e.value rfl (by
                unfold FlowAction.ExactCredit
                simp only [FlowAtom.creditOccurrence]
                rw [toB256_toNat]) rfl hinc
          · exact chronology

/-- Exact proof-indexed accounting for the childless `deposit` mint. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_deposit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = depositSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | none =>
      have hatom : primaryFlowAtom frame.sevm = some
          (.ordinaryMint frame.sevm.caller.toB256 frame.sevm.caller
            frame.sevm.value.toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector]
      unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hatom] at haction
      simp at haction
  | some action =>
      have ledger :=
        Blanc.Weth10.Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some (frame := frame)
          context haction
      have chronology :=
        Blanc.Weth10.Exec.Frame.descendantFlowActions_eq_nil_of_deposit (frame := frame)
          context hselector hnonempty
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
          have htarget : e.currentTarget = ca :=
            context.invocation.2.1
          rw [htarget] at hinc
          have haction' := haction
          simp [Blanc.Weth10.Exec.Frame.flowAction?, context.invocation,
            primaryFlowAtom, primaryDebitProvenance, hnonempty, hselector,
            depositSelector_ne_transferSelector,
            depositSelector_ne_transferAndCallSelector,
            depositSelector_ne_withdrawSelector,
            depositSelector_ne_withdrawToSelector,
            depositSelector_ne_transferFromSelector,
            depositSelector_ne_withdrawFromSelector,
            depositSelector_ne_flashLoanSelector] at haction'
          symm at haction'
          subst action
          apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.flow ledger
          apply RichStorageAccounting.ordinaryMint
          · exact LocalActionSegment.ordinaryMint
              e.caller.toB256 e.caller e.value rfl (by
                unfold FlowAction.ExactCredit
                simp only [FlowAtom.creditOccurrence]
                rw [toB256_toNat]) rfl hinc
          · exact chronology

/-- Exact proof-indexed accounting for the childless `depositTo` mint. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_depositTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = depositToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | none =>
      have hatom : primaryFlowAtom frame.sevm = some
          (.ordinaryMint (Sevm.argWord frame.sevm 0)
            (Sevm.argWord frame.sevm 0).toAdr frame.sevm.value.toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          depositToSelector_ne_depositSelector]
      unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hatom] at haction
      simp at haction
  | some action =>
      have ledger :=
        Blanc.Weth10.Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some (frame := frame)
          context haction
      have chronology :=
        Blanc.Weth10.Exec.Frame.descendantFlowActions_eq_nil_of_depositTo (frame := frame)
          context hselector hnonempty
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
          have htarget : e.currentTarget = ca :=
            context.invocation.2.1
          rw [htarget,
            normalizedAddressArg_eq_toAdr_toB256_local] at hstor
          have hincrease : Increase (Sevm.argWord e 0).toAdr e.value
              (Stor.rest (Devm.getStor pre ca))
              (Stor.rest (Devm.getStor post ca)) := by
            rw [hstor]
            exact Stor.increase_set _ _ _
          have hatom : primaryFlowAtom e = some
              (.ordinaryMint (Sevm.argWord e 0)
                (Sevm.argWord e 0).toAdr e.value.toNat) := by
            simp [primaryFlowAtom, hnonempty, hselector,
              depositToSelector_ne_depositSelector]
          have heq := action_eq_of_primaryFlowAtom context hatom haction
          subst action
          apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.flow ledger
          apply RichStorageAccounting.ordinaryMint
          · exact LocalActionSegment.ordinaryMint
              (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr e.value
              rfl (by
                unfold FlowAction.ExactCredit
                simp only [FlowAtom.creditOccurrence]
                rw [toB256_toNat])
              (by simp [primaryDebitProvenance, hnonempty, hselector,
                depositToSelector_ne_transferSelector,
                depositToSelector_ne_transferAndCallSelector,
                depositToSelector_ne_transferFromSelector,
                depositToSelector_ne_withdrawSelector,
                depositToSelector_ne_withdrawToSelector,
                depositToSelector_ne_withdrawFromSelector,
                depositToSelector_ne_flashLoanSelector])
              hincrease
          · exact chronology

/-- Exact proof-indexed accounting for `depositToAndCall`: the mint prefix
ends at the indexed callback boundary, whose retained child is then accounted
by the strong-depth hypothesis. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_depositToAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = depositToAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  rcases Blanc.Weth10.Exec.Frame.compiledDepositToAndCallChronology (frame := frame) context hselector
      hnonempty with
    ⟨callbackPre, hstorage, _hlogs, _hbalance, hcode, _houtput,
      inputSize, input, callPre, callPost, parent, child, xl, pc,
      retained, callback, _rawCommits, _occurrence, chronology⟩
  have installedCallback : some (callbackPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [hcode]
    exact context.installed.1
  rcases callback.storageSegmentEffect retained context.invocation.2.1
      installedCallback hdeeper with ⟨callbackEffect⟩
  have htarget : frame.sevm.currentTarget = ca :=
    context.invocation.2.1
  rw [htarget, normalizedAddressArg_eq_toAdr_toB256_local] at hstorage
  have increase : Increase (Sevm.argWord frame.sevm 0).toAdr
      frame.sevm.value (Stor.rest (Devm.getStor frame.pre ca))
      (Stor.rest (Devm.getStor callbackPre ca)) := by
    rw [hstorage]
    exact Stor.increase_set _ _ _
  have hatom : primaryFlowAtom frame.sevm = some
      (.ordinaryMint (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr frame.sevm.value.toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      depositToAndCallSelector_ne_depositSelector,
      depositToAndCallSelector_ne_depositToSelector]
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | none =>
      unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hatom] at haction
      simp at haction
  | some action =>
      have ledger :=
        Blanc.Weth10.Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some (frame := frame)
          context haction
      have actionEq := action_eq_of_primaryFlowAtom context hatom haction
      subst action
      apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.flow ledger
      apply RichStorageAccounting.tokenCallback
      · apply StorageSegmentDelta.ofOrdinaryMint
        exact LocalActionSegment.ordinaryMint
          (Sevm.argWord frame.sevm 0)
          (Sevm.argWord frame.sevm 0).toAdr frame.sevm.value
          rfl (by
            unfold FlowAction.ExactCredit
            simp only [FlowAtom.creditOccurrence]
            rw [toB256_toNat])
          (by simp [primaryDebitProvenance, hnonempty, hselector,
            depositToAndCallSelector_ne_transferSelector,
            depositToAndCallSelector_ne_transferAndCallSelector,
            depositToAndCallSelector_ne_transferFromSelector,
            depositToAndCallSelector_ne_withdrawSelector,
            depositToAndCallSelector_ne_withdrawToSelector,
            depositToAndCallSelector_ne_withdrawFromSelector,
            depositToAndCallSelector_ne_flashLoanSelector])
          increase
      · exact callbackEffect.delta
      · simpa only [List.nil_append] using chronology

/-- Exact proof-indexed accounting for `approveAndCall`.  The approval
prefix is WETH-balance silent, while the indexed callback supplies the exact
rollback-pruned descendant storage delta. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_approveAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = approveAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  rcases Blanc.Weth10.Exec.Frame.compiledApproveAndCallChronology (frame := frame) context hselector
      hnonempty with
    ⟨callbackPre, hsilent, _hlogs, _hbalance, hcode, _houtput,
      inputSize, input, callPre, callPost, parent, child, xl, pc,
      retained, callback, _rawCommits, _occurrence, chronology⟩
  have installedCallback : some (callbackPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [hcode]
    exact context.installed.1
  rcases callback.storageSegmentEffect retained context.invocation.2.1
      installedCallback hdeeper with ⟨callbackEffect⟩
  have htarget : frame.sevm.currentTarget = ca :=
    context.invocation.2.1
  rw [htarget] at hsilent
  have hnoPrimary : SelectsNoPrimaryFlow frame.sevm := by
    exact approveAndCallSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans approveAndCallSelector_word_eq)
  have hnone := Blanc.Weth10.Exec.Frame.flowAction_eq_none_of_selectsNoPrimaryFlow (frame := frame) context
    hnoPrimary hnonempty
  have own := Blanc.Weth10.Exec.Frame.hasNoWethBalanceOwnEffect_of_recognized (frame := frame) context hnone
    ⟨nonpayable Weth10.approveAndCall, by
      rw [hselector]
      simp [approveAndCallSelector, weth10Funcs]⟩
  apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.noFlow own
  exact NoFlowStorageAccounting.callback hsilent callbackEffect.delta (by
    simpa only [List.nil_append] using chronology)

/-- Premise-free exact proof-indexed storage accounting for `flashLoan`.
The credit, indexed retained callback, allowance bridge, and repayment all
come from one selector-level compiled chronology. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  rcases Blanc.Weth10.Exec.Frame.compiledFlashLoanChronology (frame := frame) context hselector hnonempty with
    ⟨callbackPre, callbackPost, settlePre, burnPre, parent, child, xl, pc,
      retained, callback, _rawCommits, _occurrence, hcredit, _hprefixBal,
      hprefixCode, hcallbackStor, _hcallbackBal, _hcallbackCode,
      _hcallbackLogs, _hcallbackOutput, _hwfSettle, _hreadsSettle,
      _hsettle, hsettleSilent, hcover, hdecrease, _hsettlePostBal,
      _hsettlePostCode, _hburn, chronology⟩
  have installedCallback : some (callbackPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← congrFun hprefixCode ca]
    exact context.installed.1
  rcases callback.storageSegmentEffect retained context.invocation.2.1
      installedCallback hdeeper with ⟨callbackEffect⟩
  have hreceiverNorm : (normalizedAddressArg frame.sevm 0).toAdr =
      (Sevm.argWord frame.sevm 0).toAdr := by
    rw [normalizedAddressArg_eq_toAdr_toB256_local, toAdr_toB256]
  rw [hreceiverNorm] at hcredit hcover hdecrease
  have hprimary : primaryFlowAtom frame.sevm = some
      (.flashPair (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 2).toNat) := by
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
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | none =>
      unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      have ledger :=
        Blanc.Weth10.Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some (frame := frame)
          context haction
      have actionEq := action_eq_of_primaryFlowAtom context hprimary haction
      subst action
      apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.flow ledger
      apply RichStorageAccounting.flash
      · exact LocalActionSegment.flashCredit
          (Sevm.argWord frame.sevm 0)
          (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 2) rfl
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
          hcredit
      · exact callbackEffect.delta
      · exact hcallbackStor
      · exact hsettleSilent
      · exact LocalActionSegment.flashRepayment
          (Sevm.argWord frame.sevm 0)
          (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 2)
          (Stor.rest (Devm.getStor frame.pre ca)
            (Sevm.argWord frame.sevm 0).toAdr)
          rfl
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
          hcover hdecrease
      · simpa only [List.nil_append] using chronology

/-- Internal adapter from one exact retained value-redemption chronology to
the proof-indexed storage package.  Public selector theorems below supply all
of these witnesses from the original compiled frame. -/
private theorem Exec.Frame.hasProofIndexedStorageAccounting_of_valueRedemption
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction} {rawSource : B256} {source ethRecipient : Adr}
    {amount target : B256} {callPre guardPost : Devm}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (classified : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action)
    (hatom : action.atom =
      .redemption rawSource source ethRecipient amount.toNat)
    (hcredit : action.credit = none)
    (hdebit : action.HasDebitSource rawSource source)
    (trace : AcceptedValueCallTrace frame.sevm target amount
      callPre guardPost)
    (burn : BurnCallPrefix frame.sevm frame.pre callPre guardPost
      source amount target)
    (hguardStor : Devm.getStor guardPost = Devm.getStor frame.post)
    (chronology : Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame =
      Blanc.Weth10.RetainedXlot.flowActions dp ca
        trace.retained.retained)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  have installedCall : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [burn.2.2.2.2.2.1]
    exact context.installed.1
  rcases trace.storageSegmentEffect context.invocation.2.1 installedCall
      hdeeper with ⟨childEffect⟩
  have hdecrease := burn.1
  have hamountLe := burn.2.1
  rw [context.invocation.2.1] at hdecrease hamountLe
  have segment : LocalActionSegment .redemption action
      (Stor.rest (Devm.getStor frame.pre ca))
      (Stor.rest (Devm.getStor callPre ca)) := by
    exact .redemption rawSource source ethRecipient amount hatom hcredit
      hdebit hamountLe hdecrease
  have ledger := Blanc.Weth10.Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some (frame := frame)
    context classified
  apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.flow ledger
  exact RichStorageAccounting.redemption segment childEffect.delta
    (Stor.Weth10Silent.of_eq (congrFun hguardStor ca)) chronology

/-- Internal adapter for a delegated redemption whose allowance wrapper may
write tagged allowance storage before the balance core.  Only the wrapper's
booked-balance and code observations are transported to the original frame
entry; the burn and accepted child remain rooted at their literal `ownPre`. -/
private theorem Exec.Frame.hasProofIndexedStorageAccounting_of_allowanceValueRedemption
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction} {rawSource : B256} {source ethRecipient : Adr}
    {amount target : B256} {ownPre callPre guardPost : Devm}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (classified : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action)
    (hatom : action.atom =
      .redemption rawSource source ethRecipient amount.toNat)
    (hcredit : action.credit = none)
    (hdebit : action.HasDebitSource rawSource source)
    (entry : AllowancePrefixObservations frame.sevm frame.pre ownPre)
    (trace : AcceptedValueCallTrace frame.sevm target amount
      callPre guardPost)
    (burn : BurnCallPrefix frame.sevm ownPre callPre guardPost
      source amount target)
    (hguardStor : Devm.getStor guardPost = Devm.getStor frame.post)
    (chronology : Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame =
      Blanc.Weth10.RetainedXlot.flowActions dp ca
        trace.retained.retained)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  have installedCall : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [burn.2.2.2.2.2.1, ← entry.code]
    exact context.installed.1
  rcases trace.storageSegmentEffect context.invocation.2.1 installedCall
      hdeeper with ⟨childEffect⟩
  have hdecrease := burn.1
  have hamountLe := burn.2.1
  have hentryRest := entry.storage.1
  rw [context.invocation.2.1] at hdecrease hamountLe hentryRest
  rw [← hentryRest] at hdecrease hamountLe
  have segment : LocalActionSegment .redemption action
      (Stor.rest (Devm.getStor frame.pre ca))
      (Stor.rest (Devm.getStor callPre ca)) := by
    exact .redemption rawSource source ethRecipient amount hatom hcredit
      hdebit hamountLe hdecrease
  have ledger := Blanc.Weth10.Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some (frame := frame)
    context classified
  apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.flow ledger
  exact RichStorageAccounting.redemption segment childEffect.delta
    (Stor.Weth10Silent.of_eq (congrFun hguardStor ca)) chronology

/-- Premise-free exact proof-indexed storage accounting for
`withdraw(uint256)`. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_withdraw
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  have hprimary : primaryFlowAtom frame.sevm = some
      (.redemption frame.sevm.caller.toB256 frame.sevm.caller
        frame.sevm.caller (Sevm.argWord frame.sevm 0).toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      withdrawSelector_ne_depositSelector,
      withdrawSelector_ne_depositToSelector,
      withdrawSelector_ne_depositToAndCallSelector,
      withdrawSelector_ne_transferSelector,
      withdrawSelector_ne_transferAndCallSelector,
      withdrawSelector_ne_transferFromSelector]
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | none =>
      unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      have actionEq := action_eq_of_primaryFlowAtom context hprimary haction
      subst action
      rcases Blanc.Weth10.Exec.Frame.compiledWithdrawChronology (frame := frame) context hselector hnonempty with
        ⟨callPre, guardPost, trace, burn, _hslot, _hcommits,
          _hoccurrence, hguardStor, _hguardBalance, _hguardCode,
          _hguardLogs, chronology⟩
      refine Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_valueRedemption (frame := frame)
        (rawSource := frame.sevm.caller.toB256)
        (source := frame.sevm.caller)
        (ethRecipient := frame.sevm.caller)
        (amount := Sevm.argWord frame.sevm 0)
        (target := frame.sevm.caller.toB256)
        (callPre := callPre) (guardPost := guardPost)
        context haction rfl rfl ?_ trace burn hguardStor ?_ hdeeper
      · unfold FlowAction.HasDebitSource
        simp [primaryDebitProvenance, hnonempty, hselector]
      · simpa only [List.nil_append] using chronology

/-- Premise-free exact proof-indexed storage accounting for
`withdrawTo(address,uint256)`. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_withdrawTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  have hprimary : primaryFlowAtom frame.sevm = some
      (.redemption frame.sevm.caller.toB256 frame.sevm.caller
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      withdrawToSelector_ne_depositSelector,
      withdrawToSelector_ne_depositToSelector,
      withdrawToSelector_ne_depositToAndCallSelector,
      withdrawToSelector_ne_transferSelector,
      withdrawToSelector_ne_transferAndCallSelector,
      withdrawToSelector_ne_transferFromSelector,
      withdrawToSelector_ne_withdrawSelector]
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | none =>
      unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      have actionEq := action_eq_of_primaryFlowAtom context hprimary haction
      subst action
      rcases Blanc.Weth10.Exec.Frame.compiledWithdrawToChronology (frame := frame) context hselector
          hnonempty with
        ⟨callPre, guardPost, trace, burn, _hslot, _hcommits,
          _hoccurrence, hguardStor, _hguardBalance, _hguardCode,
          _hguardLogs, chronology⟩
      refine Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_valueRedemption (frame := frame)
        (rawSource := frame.sevm.caller.toB256)
        (source := frame.sevm.caller)
        (ethRecipient := (Sevm.argWord frame.sevm 0).toAdr)
        (amount := Sevm.argWord frame.sevm 1)
        (target := Sevm.argWord frame.sevm 0)
        (callPre := callPre) (guardPost := guardPost)
        context haction rfl rfl ?_ trace burn hguardStor ?_ hdeeper
      · unfold FlowAction.HasDebitSource
        simp [primaryDebitProvenance, hnonempty, hselector]
      · simpa only [List.nil_append] using chronology

/-- Premise-free exact proof-indexed storage accounting for the zero-recipient
`transfer(address,uint256)` redemption arm. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_transferZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 0 = 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  have hprimary : primaryFlowAtom frame.sevm = some
      (.redemption frame.sevm.caller.toB256 frame.sevm.caller
        frame.sevm.caller (Sevm.argWord frame.sevm 1).toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      transferSelector_ne_depositSelector,
      transferSelector_ne_depositToSelector,
      transferSelector_ne_depositToAndCallSelector, hto]
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | none =>
      unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      have actionEq := action_eq_of_primaryFlowAtom context hprimary haction
      subst action
      rcases Blanc.Weth10.Exec.Frame.compiledTransferZeroChronology (frame := frame) context hselector
          hnonempty hto with
        ⟨callPre, guardPost, trace, burn, _hslot, _hcommits,
          _hoccurrence, hguardStor, _hguardBalance, _hguardCode,
          _hguardLogs, chronology⟩
      refine Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_valueRedemption (frame := frame)
        (rawSource := frame.sevm.caller.toB256)
        (source := frame.sevm.caller)
        (ethRecipient := frame.sevm.caller)
        (amount := Sevm.argWord frame.sevm 1)
        (target := frame.sevm.caller.toB256)
        (callPre := callPre) (guardPost := guardPost)
        context haction rfl rfl ?_ trace burn hguardStor ?_ hdeeper
      · unfold FlowAction.HasDebitSource
        simp [primaryDebitProvenance, hnonempty, hselector]
      · simpa only [List.nil_append] using chronology

/-- Premise-free exact proof-indexed storage accounting for the zero-recipient
delegated `transferFrom` redemption arm. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_transferFromZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 1 = 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  have hprimary : primaryFlowAtom frame.sevm = some
      (.redemption (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr frame.sevm.caller
        (Sevm.argWord frame.sevm 2).toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      transferFromSelector_ne_depositSelector,
      transferFromSelector_ne_depositToSelector,
      transferFromSelector_ne_depositToAndCallSelector,
      transferFromSelector_ne_transferSelector,
      transferFromSelector_ne_transferAndCallSelector, hto]
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | none =>
      unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      have actionEq := action_eq_of_primaryFlowAtom context hprimary haction
      subst action
      rcases Blanc.Weth10.Exec.Frame.compiledTransferFromZeroChronology (frame := frame) context hselector
          hnonempty hto with
        ⟨ownPre, entry, callPre, guardPost, trace, burn, _hslot,
          _hcommits, _hoccurrence, hguardStor, _hguardBalance,
          _hguardCode, _hguardLogs, chronology⟩
      have hsource : (normalizedAddressArg frame.sevm 0).toAdr =
          (Sevm.argWord frame.sevm 0).toAdr := by
        rw [normalizedAddressArg_eq_toAdr_toB256_local, toAdr_toB256]
      have burn' : BurnCallPrefix frame.sevm ownPre callPre guardPost
          (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 2) frame.sevm.caller.toB256 := by
        simpa only [hsource] using burn
      refine Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_allowanceValueRedemption (frame := frame)
        (rawSource := Sevm.argWord frame.sevm 0)
        (source := (Sevm.argWord frame.sevm 0).toAdr)
        (ethRecipient := frame.sevm.caller)
        (amount := Sevm.argWord frame.sevm 2)
        (target := frame.sevm.caller.toB256)
        (ownPre := ownPre) (callPre := callPre) (guardPost := guardPost)
        context haction rfl rfl ?_ entry trace burn' hguardStor ?_ hdeeper
      · unfold FlowAction.HasDebitSource
        simp [primaryDebitProvenance, hnonempty, hselector,
          transferFromSelector_ne_transferSelector,
          transferFromSelector_ne_transferAndCallSelector,
          transferFromSelector_ne_withdrawSelector,
          transferFromSelector_ne_withdrawToSelector]
      · simpa only [List.nil_append] using chronology

/-- Premise-free exact proof-indexed storage accounting for delegated
`withdrawFrom(address,address,uint256)`. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_withdrawFrom
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = withdrawFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  have hprimary : primaryFlowAtom frame.sevm = some
      (.redemption (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toAdr
        (Sevm.argWord frame.sevm 2).toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      withdrawFromSelector_ne_depositSelector,
      withdrawFromSelector_ne_depositToSelector,
      withdrawFromSelector_ne_depositToAndCallSelector,
      withdrawFromSelector_ne_transferSelector,
      withdrawFromSelector_ne_transferAndCallSelector,
      withdrawFromSelector_ne_transferFromSelector,
      withdrawFromSelector_ne_withdrawSelector,
      withdrawFromSelector_ne_withdrawToSelector]
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | none =>
      unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      have actionEq := action_eq_of_primaryFlowAtom context hprimary haction
      subst action
      rcases Blanc.Weth10.Exec.Frame.compiledWithdrawFromChronology (frame := frame) context hselector
          hnonempty with
        ⟨ownPre, entry, callPre, guardPost, trace, burn, _hslot,
          _hcommits, _hoccurrence, hguardStor, _hguardBalance,
          _hguardCode, _hguardLogs, chronology⟩
      have hsource : (normalizedAddressArg frame.sevm 0).toAdr =
          (Sevm.argWord frame.sevm 0).toAdr := by
        rw [normalizedAddressArg_eq_toAdr_toB256_local, toAdr_toB256]
      have burn' : BurnCallPrefix frame.sevm ownPre callPre guardPost
          (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 2) (Sevm.argWord frame.sevm 1) := by
        simpa only [hsource] using burn
      refine Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_allowanceValueRedemption (frame := frame)
        (rawSource := Sevm.argWord frame.sevm 0)
        (source := (Sevm.argWord frame.sevm 0).toAdr)
        (ethRecipient := (Sevm.argWord frame.sevm 1).toAdr)
        (amount := Sevm.argWord frame.sevm 2)
        (target := Sevm.argWord frame.sevm 1)
        (ownPre := ownPre) (callPre := callPre) (guardPost := guardPost)
        context haction rfl rfl ?_ entry trace burn' hguardStor ?_ hdeeper
      · unfold FlowAction.HasDebitSource
        simp [primaryDebitProvenance, hnonempty, hselector,
          withdrawFromSelector_ne_transferSelector,
          withdrawFromSelector_ne_transferAndCallSelector,
          withdrawFromSelector_ne_transferFromSelector,
          withdrawFromSelector_ne_withdrawSelector,
          withdrawFromSelector_ne_withdrawToSelector]
      · simpa only [List.nil_append] using chronology

/-- Premise-free exact proof-indexed storage accounting for both raw-recipient
arms of `transferAndCall`.  The zero arm retains the accepted value child
before the later ERC-677 callback; the nonzero arm retains only the callback
after the ordinary booked-balance transfer. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_transferAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  rcases Blanc.Weth10.Exec.Frame.compiledTransferAndCallChronology (frame := frame) context hselector
      hnonempty with hzero | hnonzero
  · rcases hzero with
      ⟨hraw, callPre, callbackPre, trace, burn, _hslot, _hcommits,
        _hoccurrence, tokenChronology⟩
    rcases tokenChronology with
      ⟨_inputSize, _input, callbackCallPre, callbackCallPost,
        _parent, _child, _xl, _pc, retained, callback, _callbackCommits,
        _callbackOccurrence, chronology⟩
    have installedCall : some (callPre.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      rw [burn.2.2.2.2.2.1]
      exact context.installed.1
    rcases trace.storageSegmentEffect context.invocation.2.1 installedCall
        hdeeper with ⟨valueEffect⟩
    have installedCallback : some (callbackPre.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      rw [← valueEffect.codeEq]
      exact installedCall
    rcases callback.storageSegmentEffect retained context.invocation.2.1
        installedCallback hdeeper with ⟨callbackEffect⟩
    have hprimary : primaryFlowAtom frame.sevm = some
        (.redemption frame.sevm.caller.toB256 frame.sevm.caller
          frame.sevm.caller (Sevm.argWord frame.sevm 1).toNat) := by
      simp [primaryFlowAtom, hnonempty, hselector,
        transferAndCallSelector_ne_depositSelector,
        transferAndCallSelector_ne_depositToSelector,
        transferAndCallSelector_ne_depositToAndCallSelector, hraw]
    cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
    | none =>
        unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation, hprimary] at haction
        simp at haction
    | some action =>
        have actionEq :=
          action_eq_of_primaryFlowAtom context hprimary haction
        subst action
        have hdecrease := burn.1
        have hamountLe := burn.2.1
        rw [context.invocation.2.1] at hdecrease hamountLe
        have segment : LocalActionSegment .redemption
            { atom := .redemption frame.sevm.caller.toB256
                frame.sevm.caller frame.sevm.caller
                (Sevm.argWord frame.sevm 1).toNat
              credit := FlowAtom.creditOccurrence frame.pre ca
                (.redemption frame.sevm.caller.toB256 frame.sevm.caller
                  frame.sevm.caller (Sevm.argWord frame.sevm 1).toNat)
              debit := primaryDebitProvenance frame.sevm frame.pre
                frame.post
              actualCaller := frame.sevm.caller
              currentTarget := frame.sevm.currentTarget
              codeAddress := frame.sevm.codeAddress
              depth := frame.sevm.depth }
            (Stor.rest (Devm.getStor frame.pre ca))
            (Stor.rest (Devm.getStor callPre ca)) := by
          apply LocalActionSegment.redemption
            frame.sevm.caller.toB256 frame.sevm.caller
            frame.sevm.caller (Sevm.argWord frame.sevm 1)
          · rfl
          · rfl
          · unfold FlowAction.HasDebitSource
            simp [primaryDebitProvenance, hnonempty, hselector]
          · exact hamountLe
          · exact hdecrease
        have ledger :=
          Blanc.Weth10.Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some (frame := frame)
            context haction
        apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.flow ledger
        exact RichStorageAccounting.redemptionThenTokenCallback segment
          valueEffect.delta callbackEffect.delta chronology
  · rcases hnonzero with
      ⟨hraw, recipient, callbackPre, hrecipient, htransfer,
        _hflash, _hlogs, _hbalance, hcode, _houtput, tokenChronology⟩
    rcases tokenChronology with
      ⟨_inputSize, _input, _callbackCallPre, _callbackCallPost,
        _parent, _child, _xl, _pc, retained, callback, _callbackCommits,
        _callbackOccurrence, chronology⟩
    have installedCallback : some (callbackPre.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      rw [hcode]
      exact context.installed.1
    rcases callback.storageSegmentEffect retained context.invocation.2.1
        installedCallback hdeeper with ⟨callbackEffect⟩
    have htarget : frame.sevm.currentTarget = ca :=
      context.invocation.2.1
    rw [htarget] at htransfer
    have hrecipient' : recipient =
        (Sevm.argWord frame.sevm 0).toAdr := by
      apply Adr.toB256_inj
      rw [hrecipient]
      exact normalizedAddressArg_eq_toAdr_toB256_local frame.sevm 0
    subst recipient
    have hprimary : primaryFlowAtom frame.sevm = some
        (.transfer frame.sevm.caller.toB256
          (Sevm.argWord frame.sevm 0) frame.sevm.caller
          (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 1).toNat) := by
      simp [primaryFlowAtom, hnonempty, hselector,
        transferAndCallSelector_ne_depositSelector,
        transferAndCallSelector_ne_depositToSelector,
        transferAndCallSelector_ne_depositToAndCallSelector, hraw]
    cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
    | none =>
        unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation, hprimary] at haction
        simp at haction
    | some action =>
        have actionEq :=
          action_eq_of_primaryFlowAtom context hprimary haction
        subst action
        have ledger :=
          Blanc.Weth10.Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some (frame := frame)
            context haction
        apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.flow ledger
        apply RichStorageAccounting.tokenCallback
        · apply StorageSegmentDelta.ofOrdinaryTransfer
          rcases htransfer with
            ⟨hle, intermediate, hdecrease, hincrease⟩
          have hbefore :
              intermediate (Sevm.argWord frame.sevm 0).toAdr =
                (if frame.sevm.caller =
                    (Sevm.argWord frame.sevm 0).toAdr then
                  (Stor.rest (Devm.getStor frame.pre ca))
                      frame.sevm.caller - Sevm.argWord frame.sevm 1
                 else
                  (Stor.rest (Devm.getStor frame.pre ca))
                    (Sevm.argWord frame.sevm 0).toAdr) := by
            by_cases hself : frame.sevm.caller =
                (Sevm.argWord frame.sevm 0).toAdr
            · rw [if_pos hself, hself]
              exact ((hdecrease
                (Sevm.argWord frame.sevm 0).toAdr).1 hself).symm
            · simpa [hself] using
                ((hdecrease
                  (Sevm.argWord frame.sevm 0).toAdr).2 hself).symm
          apply LocalActionSegment.ordinaryTransfer
            frame.sevm.caller.toB256 (Sevm.argWord frame.sevm 0)
            frame.sevm.caller (Sevm.argWord frame.sevm 0).toAdr
            (Sevm.argWord frame.sevm 1) rfl
            { amount_le := hle
              intermediate := intermediate
              decrease := hdecrease
              increase := hincrease }
          · unfold FlowAction.ExactCredit
            simp only [FlowAtom.creditOccurrence, hbefore]
            rw [toB256_toNat]
          · unfold FlowAction.HasDebitSource
            simp [primaryDebitProvenance, hnonempty, hselector]
        · exact callbackEffect.delta
        · simpa only [List.nil_append] using chronology

/-- Premise-free exact proof-indexed storage accounting for `permit`.  Empty
and rolled-back STATICCALL outcomes are WETH-silent; the committing outcome
uses the exact retained child and the same call boundary selected by compiled
chronology. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = permitSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  rcases Blanc.Weth10.Exec.Frame.compiledPermitChronology (frame := frame) context hselector hnonempty with
    ⟨callPre, callPost, slot, selected, _occurrence, _operands,
      outcome, ownPrefix, ownSuffix, chronology⟩
  have htarget : frame.sevm.currentTarget = ca :=
    context.invocation.2.1
  have prefixSilent : Stor.Weth10Silent
      (Devm.getStor frame.pre ca) (Devm.getStor callPre ca) := by
    simpa only [htarget] using ownPrefix.storage
  have suffixSilent : Stor.Weth10Silent
      (Devm.getStor callPost ca) (Devm.getStor frame.post ca) := by
    simpa only [htarget] using ownSuffix.storage
  have hnoPrimary : SelectsNoPrimaryFlow frame.sevm := by
    exact permitSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans permitSelector_word_eq)
  have classified := Blanc.Weth10.Exec.Frame.flowAction_eq_none_of_selectsNoPrimaryFlow (frame := frame)
    context hnoPrimary hnonempty
  have ownRoot := Blanc.Weth10.Exec.Frame.hasNoWethBalanceOwnEffect_of_recognized (frame := frame)
    context classified
    ⟨nonpayable (Weth10.permit dp), by
      rw [hselector]
      simp [permitSelector, weth10Funcs]⟩
  apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.noFlow ownRoot
  cases outcome with
  | none own =>
      have callSilent : Stor.Weth10Silent
          (Devm.getStor callPre ca) (Devm.getStor callPost ca) := by
        simpa only [htarget] using own.storage
      exact NoFlowStorageAccounting.silent
        (prefixSilent.trans (callSilent.trans suffixSilent)) chronology
  | rolledBack child trace rollsBack own =>
      have callSilent : Stor.Weth10Silent
          (Devm.getStor callPre ca) (Devm.getStor callPost ca) := by
        simpa only [htarget] using own.storage
      exact NoFlowStorageAccounting.silent
        (prefixSilent.trans (callSilent.trans suffixSilent)) chronology
  | committed child trace commits =>
      have installedCall : some (callPre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        rw [← ownPrefix.code]
        exact context.installed.1
      let childTrace : ProcessMessageTrace trace.msg (.ok trace.childPost) :=
        ⟨_, .some child, trace.process⟩
      have hparent : callPre.state = trace.msg.benv.state :=
        trace.parentState.symm.trans trace.benvState.symm
      have htargetCode : trace.msg.currentTarget = ca →
          some trace.msg.code.toList = Prog.compile (weth10 dp) := by
        intro hmsgTarget
        have htargetCa : (1 : B256).toAdr = ca :=
          trace.target.symm.trans hmsgTarget
        exact callbackCode_eq_compiled_of_target_eq installedCall
          htargetCa trace.delegationResolution
      have htargetDirect : trace.msg.currentTarget = ca →
          trace.msg.codeAddress = some ca := by
        intro hmsgTarget
        have htargetCa : (1 : B256).toAdr = ca :=
          trace.target.symm.trans hmsgTarget
        have hnodel :
            getDelegatedCodeAddress (callPre.getCode ca) = none := by
          dsimp only [getDelegatedCodeAddress]
          rw [if_neg (not_delegation_of_compile installedCall)]
        simp only [trace.codeAddress, htargetCa, hnodel, Option.getD_none]
      rcases childTrace.storageSegmentDelta_of_forallDeeperAt hparent
          trace.depth installedCall htargetCode htargetDirect hdeeper with
        ⟨childEffect⟩
      have hresumeState : callPost.state = trace.childPost.state :=
        Resume.call_state trace.resume
      have resumeEffect : StorageSegmentEffect ca trace.childPost
          callPost [] :=
        StorageSegmentEffect.of_getStorCode_eq
          (congrArg (fun state : State => state.getStor ca)
            hresumeState.symm)
          (congrArg (fun state : State => state.getCode ca)
            hresumeState.symm)
      have callEffect : StorageSegmentEffect ca callPre callPost
          (Exec.flowActions dp ca child) := by
        simpa only [childTrace, RetainedXlot.flowActions,
          List.append_nil] using
          childEffect.append resumeEffect
      exact NoFlowStorageAccounting.silentAround prefixSilent
        callEffect.delta suffixSilent chronology

/-- Exact proof-indexed accounting for the ordinary nonzero-recipient
`transfer` branch. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_transferNonzero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 0 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | none =>
      have hatom : primaryFlowAtom frame.sevm = some
          (.transfer frame.sevm.caller.toB256
            (Sevm.argWord frame.sevm 0) frame.sevm.caller
            (Sevm.argWord frame.sevm 0).toAdr
            (Sevm.argWord frame.sevm 1).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          transferSelector_ne_depositSelector,
          transferSelector_ne_depositToSelector,
          transferSelector_ne_depositToAndCallSelector, hto]
      unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hatom] at haction
      simp at haction
  | some action =>
      have ledger :=
        Blanc.Weth10.Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some (frame := frame)
          context haction
      have chronology :=
        Blanc.Weth10.Exec.Frame.descendantFlowActions_eq_nil_of_transferNonzero (frame := frame)
          context hselector hnonempty hto
      rcases frame with ⟨pc, e, pre, out, run, committed⟩
      cases out with
      | error err => simp [Execution.commits] at committed
      | ok post =>
          have hpc : pc = 0 := context.root.1
          subst pc
          have heffect := (weth10_transfer_successEffect dp
            context.memory_wf context.memory_reads_empty run
            context.invocation.2.2.2
            (by simpa only [transferSelector] using hselector)
            hnonempty).2
          have htarget : e.currentTarget = ca :=
            context.invocation.2.1
          rcases heffect with hzero | hnonzero
          · exact (hto hzero.1).elim
          · rcases hnonzero with
              ⟨hraw, recipient, hrecipient, htransfer, _⟩
            rw [htarget] at htransfer
            have hrecipient' :
                recipient = (Sevm.argWord e 0).toAdr := by
              apply Adr.toB256_inj
              rw [hrecipient]
              exact normalizedAddressArg_eq_toAdr_toB256_local e 0
            subst recipient
            have hatom : primaryFlowAtom e = some
                (.transfer e.caller.toB256 (Sevm.argWord e 0) e.caller
                  (Sevm.argWord e 0).toAdr
                  (Sevm.argWord e 1).toNat) := by
              simp [primaryFlowAtom, hnonempty, hselector,
                transferSelector_ne_depositSelector,
                transferSelector_ne_depositToSelector,
                transferSelector_ne_depositToAndCallSelector, hraw]
            have heq := action_eq_of_primaryFlowAtom context hatom haction
            subst action
            apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.flow ledger
            apply RichStorageAccounting.ordinaryTransfer
            · rcases htransfer with
                ⟨hle, intermediate, hdecrease, hincrease⟩
              have hbefore : intermediate (Sevm.argWord e 0).toAdr =
                  (if e.caller = (Sevm.argWord e 0).toAdr then
                    (Stor.rest (Devm.getStor pre ca)) e.caller -
                      Sevm.argWord e 1
                   else
                    (Stor.rest (Devm.getStor pre ca))
                      (Sevm.argWord e 0).toAdr) := by
                by_cases hself : e.caller = (Sevm.argWord e 0).toAdr
                · rw [if_pos hself, hself]
                  exact
                    ((hdecrease (Sevm.argWord e 0).toAdr).1 hself).symm
                · simpa [hself] using
                    ((hdecrease (Sevm.argWord e 0).toAdr).2 hself).symm
              apply LocalActionSegment.ordinaryTransfer
                e.caller.toB256 (Sevm.argWord e 0) e.caller
                (Sevm.argWord e 0).toAdr (Sevm.argWord e 1) rfl
                { amount_le := hle
                  intermediate := intermediate
                  decrease := hdecrease
                  increase := hincrease }
              · unfold FlowAction.ExactCredit
                simp only [FlowAtom.creditOccurrence, hbefore]
                rw [toB256_toNat]
              · unfold FlowAction.HasDebitSource
                simp [primaryDebitProvenance, hnonempty, hselector]
            · exact chronology

/-- Exact proof-indexed accounting for the childless ordinary `approve`
leaf.  The only storage write uses a runtime-tagged allowance key, so the
WETH balance region is silent and the descendant ledger is empty. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_approve
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm =
      selector "approve" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  apply Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_childlessNoFlow
    (frame := frame) context
  refine ⟨approve, hnonempty, ?_, approve_childlessTerminal, ?_, ?_, ?_⟩
  · rw [hselector]
    simp only [weth10Funcs, List.mem_cons]
    exact Or.inr (Or.inl True.intro)
  · exact approveSelector_noPrimaryFlow.selectsNoPrimaryFlow
      (hselector.trans approveSelector_word_eq)
  · rw [hselector, approveSelector_word_eq, approveAndCallSelector_word_eq]
    decide +kernel
  · rw [hselector, approveSelector_word_eq, permitSelector_word_eq]
    decide +kernel

private theorem rest_set_callerAllowanceRuntimeKey_accounting
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

private theorem callerAllowanceOutcome_rest_eq_accounting
    {e : Sevm} {pre corePre : Devm} {amountArg : B256}
    (h : CallerAllowanceOutcome e pre corePre amountArg) :
    Stor.rest (Devm.getStor corePre e.currentTarget) =
      Stor.rest (Devm.getStor pre e.currentTarget) := by
  rcases h.1 with hself | ⟨_, hspend⟩
  · exact congrArg Stor.rest hself.2.1
  · rcases hspend with hmax | hfinite
    · exact congrArg Stor.rest hmax.2.1
    · rcases hfinite with
        ⟨allowance, _hnotmax, _hle, _hget, hstor, _hlogs⟩
      rw [hstor, rest_set_callerAllowanceRuntimeKey_accounting]

/-- The delegated nonzero-recipient transfer core is locally call-free.
Once its original compiled-cursor chronology is known to be empty, the
functional allowance fork and transfer effect close exact storage accounting
without any callback or endpoint premise. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_transferFromNonzero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 1 ≠ 0)
    (chronology : Blanc.Weth10.Exec.Frame.descendantFlowActions dp ca frame = []) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  cases haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame with
  | none =>
      have hatom : primaryFlowAtom frame.sevm = some
          (.transfer (Sevm.argWord frame.sevm 0)
            (Sevm.argWord frame.sevm 1)
            (Sevm.argWord frame.sevm 0).toAdr
            (Sevm.argWord frame.sevm 1).toAdr
            (Sevm.argWord frame.sevm 2).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          transferFromSelector_ne_depositSelector,
          transferFromSelector_ne_depositToSelector,
          transferFromSelector_ne_depositToAndCallSelector,
          transferFromSelector_ne_transferSelector,
          transferFromSelector_ne_transferAndCallSelector, hto]
      unfold Blanc.Weth10.Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hatom] at haction
      simp at haction
  | some action =>
      have ledger :=
        Blanc.Weth10.Exec.Frame.hasClassifiedActionLedger_of_flowAction_eq_some (frame := frame)
          context haction
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
          have htarget : e.currentTarget = ca :=
            context.invocation.2.1
          have hrest :=
            callerAllowanceOutcome_rest_eq_accounting hallowance
          have hsource : (normalizedAddressArg e 0).toAdr =
              (Sevm.argWord e 0).toAdr := by
            rw [normalizedAddressArg_eq_toAdr_toB256_local,
              toAdr_toB256]
          rcases hcore with hzero | hnonzero
          · exact (hto hzero.1).elim
          · rcases hnonzero with
              ⟨_, recipient, hrecipient, htransfer, _, _, _, _, _⟩
            rw [htarget] at hrest
            rw [htarget, hrest, hsource] at htransfer
            have hrecipient' :
                recipient = (Sevm.argWord e 1).toAdr := by
              apply Adr.toB256_inj
              rw [hrecipient]
              exact normalizedAddressArg_eq_toAdr_toB256_local e 1
            subst recipient
            have hatom : primaryFlowAtom e = some
                (.transfer (Sevm.argWord e 0) (Sevm.argWord e 1)
                  (Sevm.argWord e 0).toAdr
                  (Sevm.argWord e 1).toAdr
                  (Sevm.argWord e 2).toNat) := by
              simp [primaryFlowAtom, hnonempty, hselector,
                transferFromSelector_ne_depositSelector,
                transferFromSelector_ne_depositToSelector,
                transferFromSelector_ne_depositToAndCallSelector,
                transferFromSelector_ne_transferSelector,
                transferFromSelector_ne_transferAndCallSelector,
                hto]
            have heq := action_eq_of_primaryFlowAtom context hatom haction
            subst action
            apply Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting.flow ledger
            apply RichStorageAccounting.ordinaryTransfer
            · rcases htransfer with
                ⟨hle, intermediate, hdecrease, hincrease⟩
              have hbefore : intermediate (Sevm.argWord e 1).toAdr =
                  (if (Sevm.argWord e 0).toAdr =
                        (Sevm.argWord e 1).toAdr then
                    (Stor.rest (Devm.getStor pre ca))
                        (Sevm.argWord e 0).toAdr - Sevm.argWord e 2
                   else
                    (Stor.rest (Devm.getStor pre ca))
                      (Sevm.argWord e 1).toAdr) := by
                by_cases hself : (Sevm.argWord e 0).toAdr =
                    (Sevm.argWord e 1).toAdr
                · rw [if_pos hself, hself]
                  exact
                    ((hdecrease (Sevm.argWord e 1).toAdr).1 hself).symm
                · simpa [hself] using
                    ((hdecrease (Sevm.argWord e 1).toAdr).2 hself).symm
              apply LocalActionSegment.ordinaryTransfer
                (Sevm.argWord e 0) (Sevm.argWord e 1)
                (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toAdr
                (Sevm.argWord e 2) rfl
                { amount_le := hle
                  intermediate := intermediate
                  decrease := hdecrease
                  increase := hincrease }
              · unfold FlowAction.ExactCredit
                simp only [FlowAtom.creditOccurrence, hbefore]
                rw [toB256_toNat]
              · unfold FlowAction.HasDebitSource
                simp [primaryDebitProvenance, hnonempty, hselector,
                  transferFromSelector_ne_transferSelector,
                  transferFromSelector_ne_transferAndCallSelector,
                  transferFromSelector_ne_withdrawSelector,
                  transferFromSelector_ne_withdrawToSelector]
            · exact chronology

/-- Every currently closed non-flow selector.  Each constructor records the
exact executable selector test and nonempty-calldata dispatch premise; no
endpoint equation is stored in this finite inventory. -/
inductive Exec.Frame.CallFreeNoFlowStorageBranch
    (frame : Exec.Frame) : Prop
  | name
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = selector "name" [])
  | approve
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm =
        selector "approve" [.address, .uint256])
  | totalSupply
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = selector "totalSupply" [])
  | permitTypehash
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm =
        selector "PERMIT_TYPEHASH" [])
  | decimals
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = selector "decimals" [])
  | domainSeparator
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm =
        selector "DOMAIN_SEPARATOR" [])
  | maxFlashLoan
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm =
        selector "maxFlashLoan" [.address])
  | balanceOf
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm =
        selector "balanceOf" [.address])
  | nonces
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm =
        selector "nonces" [.address])
  | callbackSuccess
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm =
        selector "CALLBACK_SUCCESS" [])
  | flashMinted
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = selector "flashMinted" [])
  | symbol
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = selector "symbol" [])
  | deploymentChainId
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm =
        selector "deploymentChainId" [])
  | flashFee
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm =
        selector "flashFee" [.address, .uint256])
  | allowance
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm =
        selector "allowance" [.address, .address])

/-- Every closed non-flow branch has nonempty calldata. -/
theorem Exec.Frame.CallFreeNoFlowStorageBranch.nonempty
    {frame : Exec.Frame}
    (branch : Blanc.Weth10.Exec.Frame.CallFreeNoFlowStorageBranch frame) :
    frame.sevm.data.length.toB256 ≠ 0 := by
  cases branch <;> assumption

/-- Every closed non-flow selector is disjoint from all ten primary-flow
selector families. -/
theorem Exec.Frame.CallFreeNoFlowStorageBranch.selectsNoPrimaryFlow
    {frame : Exec.Frame}
    (branch : Blanc.Weth10.Exec.Frame.CallFreeNoFlowStorageBranch frame) :
    SelectsNoPrimaryFlow frame.sevm := by
  cases branch with
  | name _ selected =>
      exact nameSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans nameSelector_word_eq)
  | approve _ selected =>
      exact approveSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans approveSelector_word_eq)
  | totalSupply _ selected =>
      exact totalSupplySelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans totalSupplySelector_word_eq)
  | permitTypehash _ selected =>
      exact permitTypehashSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans permitTypehashSelector_word_eq_local)
  | decimals _ selected =>
      exact decimalsSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans decimalsSelector_word_eq_local)
  | domainSeparator _ selected =>
      exact domainSeparatorSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans domainSeparatorSelector_word_eq)
  | maxFlashLoan _ selected =>
      exact maxFlashLoanSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans maxFlashLoanSelector_word_eq)
  | balanceOf _ selected =>
      exact balanceOfSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans balanceOfSelector_word_eq)
  | nonces _ selected =>
      exact noncesSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans noncesSelector_word_eq_local)
  | callbackSuccess _ selected =>
      exact callbackSuccessSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans callbackSuccessSelector_word_eq)
  | flashMinted _ selected =>
      exact flashMintedSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans flashMintedSelector_word_eq)
  | symbol _ selected =>
      exact symbolSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans symbolSelector_word_eq)
  | deploymentChainId _ selected =>
      exact deploymentChainIdSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans deploymentChainIdSelector_word_eq)
  | flashFee _ selected =>
      exact flashFeeSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans flashFeeSelector_word_eq_local)
  | allowance _ selected =>
      exact allowanceSelector_noPrimaryFlow.selectsNoPrimaryFlow
        (selected.trans allowanceSelector_word_eq_local)

/-- Exact storage dispatcher for all fifteen already-closed non-flow leaves. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_callFreeNoFlowBranch
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (branch : Blanc.Weth10.Exec.Frame.CallFreeNoFlowStorageBranch frame) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  cases branch with
  | name nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_name (frame := frame)
        context selected nonempty
  | approve nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_approve (frame := frame)
        context selected nonempty
  | totalSupply nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_totalSupply (frame := frame)
        context selected nonempty
  | permitTypehash nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_permitTypehash (frame := frame)
        context selected nonempty
  | decimals nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_decimals (frame := frame)
        context selected nonempty
  | domainSeparator nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_domainSeparator (frame := frame)
        context selected nonempty
  | maxFlashLoan nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_maxFlashLoan (frame := frame)
        context selected nonempty
  | balanceOf nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_balanceOf (frame := frame)
        context selected nonempty
  | nonces nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_nonces (frame := frame)
        context selected nonempty
  | callbackSuccess nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_callbackSuccess (frame := frame)
        context selected nonempty
  | flashMinted nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_flashMinted (frame := frame)
        context selected nonempty
  | symbol nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_symbol (frame := frame)
        context selected nonempty
  | deploymentChainId nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_deploymentChainId (frame := frame)
        context selected nonempty
  | flashFee nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_flashFee (frame := frame)
        context selected nonempty
  | allowance nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_allowance (frame := frame)
        context selected nonempty

/-- The currently closed call-free storage branches, expressed only by their
concrete invocation tests. -/
inductive Exec.Frame.CallFreeStorageBranch (frame : Exec.Frame) : Prop
  | receive
      (empty : frame.sevm.data.length.toB256 = 0)
  | deposit
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = depositSelector)
  | depositTo
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = depositToSelector)
  | transferNonzero
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = transferSelector)
      (recipient : Sevm.argWord frame.sevm 0 ≠ 0)
  | transferFromNonzero
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = transferFromSelector)
      (recipient : Sevm.argWord frame.sevm 1 ≠ 0)
  | noFlow (branch : Blanc.Weth10.Exec.Frame.CallFreeNoFlowStorageBranch frame)

/-- Incremental concrete dispatcher for every childless primary flow branch.
It is premise-free beyond the executable branch test itself and does not wait
on any callback chronology theorem. -/
theorem Exec.Frame.hasProofIndexedStorageAccounting_of_callFreeBranch
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (branch : Blanc.Weth10.Exec.Frame.CallFreeStorageBranch frame) :
    Blanc.Weth10.Exec.Frame.HasProofIndexedStorageAccounting dp ca frame := by
  cases branch with
  | receive empty =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_receive (frame := frame) context empty
  | deposit nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_deposit (frame := frame)
        context selected nonempty
  | depositTo nonempty selected =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_depositTo (frame := frame)
        context selected nonempty
  | transferNonzero nonempty selected recipient =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_transferNonzero (frame := frame)
        context selected nonempty recipient
  | transferFromNonzero nonempty selected recipient =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_transferFromNonzero (frame := frame)
        context selected nonempty recipient
        (Blanc.Weth10.Exec.Frame.descendantFlowActions_eq_nil_of_transferFromNonzero (frame := frame)
          context selected nonempty recipient)
  | noFlow noFlow =>
      exact Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_callFreeNoFlowBranch (frame := frame)
        context noFlow

/-- The exact selector branches still awaiting recursive storage chronology.
This finite sum deliberately separates value-redemption, ERC-677 callback,
flash, and permit work instead of hiding them behind a provider premise. -/
inductive Exec.Frame.RemainingStorageBranch (frame : Exec.Frame) : Prop
  | depositToAndCall
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = depositToAndCallSelector)
  | transferZero
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = transferSelector)
      (recipient : Sevm.argWord frame.sevm 0 = 0)
  | transferAndCall
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = transferAndCallSelector)
  | transferFromZero
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = transferFromSelector)
      (recipient : Sevm.argWord frame.sevm 1 = 0)
  | withdraw
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = withdrawSelector)
  | withdrawTo
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = withdrawToSelector)
  | withdrawFrom
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = withdrawFromSelector)
  | flashLoan
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = flashLoanSelector)
  | approveAndCall
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = approveAndCallSelector)
  | permit
      (nonempty : frame.sevm.data.length.toB256 ≠ 0)
      (selected : Sevm.selector frame.sevm = permitSelector)

/-- Reverse dispatch partitions every authentic successful frame into an
already-closed call-free case or one exact remaining recursive case. -/
theorem Exec.Frame.callFreeStorageBranch_or_remaining
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame) :
    Blanc.Weth10.Exec.Frame.CallFreeStorageBranch frame ∨ Blanc.Weth10.Exec.Frame.RemainingStorageBranch frame := by
  by_cases hempty : frame.sevm.data.length.toB256 = 0
  · exact Or.inl (.receive hempty)
  have hnonempty : frame.sevm.data.length.toB256 ≠ 0 := hempty
  rcases Blanc.Weth10.Exec.Frame.recognizedSelector_of_nonempty (frame := frame) context hnonempty with
    ⟨body, hmember⟩
  have hselector : Sevm.selector frame.sevm ∈
      (weth10Funcs dp).map Prod.fst :=
    List.mem_map.mpr ⟨(Sevm.selector frame.sevm, body), hmember, rfl⟩
  simp only [weth10Funcs, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hselector
  rcases hselector with
      hname | happrove | htotalSupply | hwithdrawTo |
      htransferFrom | hwithdraw | hpermitTypehash | hdecimals |
      hdomainSeparator | htransferCall | hflash | hdepositCall |
      hmaxFlashLoan | hbalanceOf | hnonces | hcallbackSuccess |
      hflashMinted | hwithdrawFrom | hsymbol | htransfer |
      hdepositTo | happroveCall | hdeploymentChainId | hdeposit |
      hpermit | hflashFee | hallowance
  · exact Or.inl (.noFlow (.name hnonempty hname))
  · exact Or.inl (.noFlow (.approve hnonempty happrove))
  · exact Or.inl (.noFlow (.totalSupply hnonempty htotalSupply))
  · exact Or.inr (.withdrawTo hnonempty (by
      simpa only [withdrawToSelector] using hwithdrawTo))
  · have selected : Sevm.selector frame.sevm = transferFromSelector := by
      simpa only [transferFromSelector] using htransferFrom
    by_cases hrecipient : Sevm.argWord frame.sevm 1 = 0
    · exact Or.inr (.transferFromZero hnonempty selected hrecipient)
    · exact Or.inl (.transferFromNonzero hnonempty selected hrecipient)
  · exact Or.inr (.withdraw hnonempty (by
      simpa only [withdrawSelector] using hwithdraw))
  · exact Or.inl (.noFlow (.permitTypehash hnonempty hpermitTypehash))
  · exact Or.inl (.noFlow (.decimals hnonempty hdecimals))
  · exact Or.inl (.noFlow (.domainSeparator hnonempty hdomainSeparator))
  · exact Or.inr (.transferAndCall hnonempty (by
      simpa only [transferAndCallSelector] using htransferCall))
  · exact Or.inr (.flashLoan hnonempty (by
      simpa only [flashLoanSelector] using hflash))
  · exact Or.inr (.depositToAndCall hnonempty (by
      simpa only [depositToAndCallSelector] using hdepositCall))
  · exact Or.inl (.noFlow (.maxFlashLoan hnonempty hmaxFlashLoan))
  · exact Or.inl (.noFlow (.balanceOf hnonempty hbalanceOf))
  · exact Or.inl (.noFlow (.nonces hnonempty hnonces))
  · exact Or.inl (.noFlow (.callbackSuccess hnonempty hcallbackSuccess))
  · exact Or.inl (.noFlow (.flashMinted hnonempty hflashMinted))
  · exact Or.inr (.withdrawFrom hnonempty (by
      simpa only [withdrawFromSelector] using hwithdrawFrom))
  · exact Or.inl (.noFlow (.symbol hnonempty hsymbol))
  · have selected : Sevm.selector frame.sevm = transferSelector := by
      simpa only [transferSelector] using htransfer
    by_cases hrecipient : Sevm.argWord frame.sevm 0 = 0
    · exact Or.inr (.transferZero hnonempty selected hrecipient)
    · exact Or.inl (.transferNonzero hnonempty selected hrecipient)
  · exact Or.inl (.depositTo hnonempty (by
      simpa only [depositToSelector] using hdepositTo))
  · exact Or.inr (.approveAndCall hnonempty (by
      simpa only [approveAndCallSelector] using happroveCall))
  · exact Or.inl (.noFlow
      (.deploymentChainId hnonempty hdeploymentChainId))
  · exact Or.inl (.deposit hnonempty (by
      simpa only [depositSelector] using hdeposit))
  · exact Or.inr (.permit hnonempty (by
      simpa only [permitSelector] using hpermit))
  · exact Or.inl (.noFlow (.flashFee hnonempty hflashFee))
  · exact Or.inl (.noFlow (.allowance hnonempty hallowance))

/-- Premise-free exact storage handler for every authentic compiled WETH10
frame.  Every selector arm is discharged by its concrete chronology. -/
theorem compiledFrameStorageHandler
    (dp : DeployParams) (ca : Adr) :
    CompiledFrameStorageHandler dp ca := by
  intro frame context hdeeper
  rcases Blanc.Weth10.Exec.Frame.callFreeStorageBranch_or_remaining (frame := frame) context with
      closed | openCase
  · exact (Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_callFreeBranch (frame := frame)
      context closed).storageSegmentEffect
  · cases openCase with
    | depositToAndCall nonempty selected =>
        exact (Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_depositToAndCall (frame := frame)
          context selected nonempty hdeeper).storageSegmentEffect
    | transferZero nonempty selected recipient =>
        exact (Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_transferZero (frame := frame)
          context selected nonempty recipient hdeeper).storageSegmentEffect
    | transferAndCall nonempty selected =>
        exact (Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_transferAndCall (frame := frame)
          context selected nonempty hdeeper).storageSegmentEffect
    | transferFromZero nonempty selected recipient =>
        exact (Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_transferFromZero (frame := frame)
          context selected nonempty recipient hdeeper).storageSegmentEffect
    | withdraw nonempty selected =>
        exact (Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_withdraw (frame := frame)
          context selected nonempty hdeeper).storageSegmentEffect
    | withdrawTo nonempty selected =>
        exact (Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_withdrawTo (frame := frame)
          context selected nonempty hdeeper).storageSegmentEffect
    | withdrawFrom nonempty selected =>
        exact (Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_withdrawFrom (frame := frame)
          context selected nonempty hdeeper).storageSegmentEffect
    | flashLoan nonempty selected =>
        exact (Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_flashLoan (frame := frame)
          context selected nonempty hdeeper).storageSegmentEffect
    | approveAndCall nonempty selected =>
        exact (Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_approveAndCall (frame := frame)
          context selected nonempty hdeeper).storageSegmentEffect
    | permit nonempty selected =>
        exact (Blanc.Weth10.Exec.Frame.hasProofIndexedStorageAccounting_of_permit (frame := frame)
          context selected nonempty hdeeper).storageSegmentEffect

/-- Premise-free compiled-program storage handler consumed by recursion. -/
theorem compiledBodyStorageHandler
    (dp : DeployParams) (ca : Adr) :
    CompiledBodyStorageHandler dp ca :=
  (compiledFrameStorageHandler dp ca).compiledBodyStorageHandler

/-- Failed raw executions cannot satisfy the committed premise. -/
theorem Exec.CoreStorageSound.error
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm}
    {error : EvmError × Devm} :
    Exec.CoreStorageSound dp ca pc sevm pre (.error error) := by
  intro run committed
  simp [Execution.commits] at committed

/-- Every successful nonrecursive instruction step in a foreign frame is an
empty storage segment at `ca`.  `SSTORE` is handled explicitly at the foreign
current target; CALL/CREATE no-slot behavior comes from the concrete
interpreter transport above. -/
theorem Ninst.foreignNoneStorageSegmentEffect
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (run : Ninst.StepRun pc sevm pre n .none (.ok post))
    (hforeign : sevm.currentTarget ≠ ca) :
    Nonempty (StorageSegmentEffect ca pre post []) := by
  cases n with
  | reg r =>
      simp only [Ninst.StepRun, Ninst.step_reg,
        Step.run_ofExecution] at run
      have hreg : Rinst.run ⟨pc, sevm, pre⟩ r = .ok post :=
        run.2.symm
      by_cases hsstore : r = .sstore
      · subst r
        have hframe := Rinst.sstore_run_stateWriteFrame pc pre sevm
        rw [hreg] at hframe
        exact ⟨StorageSegmentEffect.of_getStorCode_eq
          (sstore_preserves_getStor_ne hreg hforeign).symm
          (hframe.getCode_eq ca)⟩
      · exact ⟨StorageSegmentEffect.of_getStorCode_eq
          (congrFun (Rinst.preserves_stor hsstore hreg) ca)
          (Rinst.preserves_getCode hreg ca).symm⟩
  | exec x =>
      simp only [Ninst.StepRun, Ninst.step_exec] at run
      exact Xinst.storageSegmentEffect_none (XStep.run_toStep.mp run)
  | push xs hxs =>
      have hframe := Ninst.push_instructionFrame_effectRec
        (hxs := hxs) (xl := .none) trivial run
      exact ⟨StorageSegmentEffect.of_getStorCode_eq
        (hframe.getStor ca) (hframe.getCode ca)⟩

/-- Jump bookkeeping is an empty storage/code segment. -/
theorem Jinst.storageSegmentEffect
    {ca : Adr} {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {j : Jinst}
    (run : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', post⟩)) :
    Nonempty (StorageSegmentEffect ca pre post []) := by
  have hframe := Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ j
  rw [run] at hframe
  exact ⟨StorageSegmentEffect.of_getStorCode_eq
    (hframe.getStor ca) (hframe.getCode ca)⟩

/-- A successful terminal instruction in a foreign frame cannot change the
installed contract's storage or code.  The SELFDESTRUCT arm transfers only
balances and marks the foreign donor for deletion. -/
theorem Linst.foreignStorageSegmentEffect
    {ca : Adr} {sevm : Sevm} {pre post : Devm} {l : Linst}
    (run : Linst.Run sevm pre l (.ok post))
    (_hforeign : sevm.currentTarget ≠ ca) :
    Nonempty (StorageSegmentEffect ca pre post []) := by
  have hcodeFrame := Linst.run_codeFrame run
  have hcode : pre.getCode ca = post.getCode ca :=
    (hcodeFrame ca).symm
  cases l with
  | stop =>
      simp [Linst.Run, Linst.run] at run
      subst post
      exact ⟨StorageSegmentEffect.refl ca pre⟩
  | ret =>
      have hframe := Linst.run_instructionFrame sevm pre .ret (by decide)
      rw [run] at hframe
      exact ⟨StorageSegmentEffect.of_getStorCode_eq
        (hframe.getStor ca) hcode⟩
  | rev =>
      dsimp [Linst.Run, Linst.run] at run
      rcases Except.bind_eq_ok run with ⟨first, hfirst, hrest⟩
      rcases Except.bind_eq_ok hrest with ⟨second, hsecond, hrest⟩
      rcases Except.bind_eq_ok hrest with ⟨third, hthird, hrest⟩
      contradiction
  | dest =>
      dsimp [Linst.Run, Linst.run] at run
      rcases Except.bind_eq_ok run with
        ⟨⟨donee, devm1⟩, hpop, hrun1⟩
      rcases Except.bind_eq_ok hrun1 with
        ⟨devm2, hcharge, hrun2⟩
      rcases Except.bind_eq_ok hrun2 with
        ⟨_, hassert, hrun3⟩
      rcases Except.bind_eq_ok hrun3 with
        ⟨devm3, hsub, hrun4⟩
      have hsubSome : devm2.subBal sevm.currentTarget
          (devm1.getAcct sevm.currentTarget).bal = some devm3 := by
        cases heq : devm2.subBal sevm.currentTarget
            (devm1.getAcct sevm.currentTarget).bal
        · rw [heq] at hsub
          contradiction
        · rw [heq] at hsub
          injection hsub with h
          subst h
          rfl
      have hsubState : devm2.state.subBal sevm.currentTarget
          (devm1.getAcct sevm.currentTarget).bal = some devm3.state := by
        dsimp [Devm.subBal, Option.bind] at hsubSome
        cases heq : devm2.state.subBal sevm.currentTarget
            (devm1.getAcct sevm.currentTarget).bal
        · rw [heq] at hsubSome
          contradiction
        · rw [heq] at hsubSome
          injection hsubSome with h
          subst h
          rfl
      let transferred := devm3.addBal donee
        (devm1.getAcct sevm.currentTarget).bal
      have hpreToOne : Devm.getStor pre ca = Devm.getStor devm1 ca :=
        congrFun (Devm.popToAdr_getStor_eq hpop) ca
      have hchargeStor : Devm.getStor devm1 ca = Devm.getStor devm2 ca := by
        have hcharged := chargeGas_getStor_eq hcharge
        have hprefix : Devm.getStor
            (if donee ∉ devm1.accessedAddresses then
              (addAccessedAddress devm1 donee,
                gasSelfDestruct + gasColdAccountAccess)
            else (devm1, gasSelfDestruct)).1 ca =
              Devm.getStor devm1 ca := by
          split <;> rfl
        exact hprefix.symm.trans (congrFun hcharged ca)
      have htransferStor : Devm.getStor devm2 ca =
          Devm.getStor transferred ca := by
        exact (of_state_transfer_fields hsubState).1 ca |>.symm
      have hpostStor : Devm.getStor transferred ca = Devm.getStor post ca := by
        dsimp only [transferred] at hrun4 ⊢
        split at hrun4
        · have heq := Except.ok.inj hrun4
          rw [← heq]
          exact State.setBal_get_stor.symm
        · have heq := Except.ok.inj hrun4
          rw [← heq]
      exact ⟨StorageSegmentEffect.of_getStorCode_eq
        (hpreToOne.trans (hchargeStor.trans
          (htransferStor.trans hpostStor))) hcode⟩

/-- Foreign nonrecursive handler for `lift_core`. -/
theorem Exec.CoreStorageSound.nextNone
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {n : Ninst}
    {inter : Devm} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (hstep : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out)
    (hforeign : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreStorageSound dp ca
      (pc + n.size) sevm inter out) :
    Exec.CoreStorageSound dp ca pc sevm pre out := by
  intro run committed hatp _
  rcases Ninst.foreignNoneStorageSegmentEffect hstep hforeign with ⟨head⟩
  have hatpInter : Prog.At (weth10 dp) ca
      (pc + n.size) sevm inter := by
    refine ⟨?_, fun htarget => (hforeign htarget).elim⟩
    rw [← head.codeEq]
    exact hatp.1
  rcases ih next committed hatpInter
      (fun htarget => (hforeign htarget).elim) with ⟨tail⟩
  have combined : StorageSegmentEffect ca pre
      (Execution.committedPost out committed)
      (Exec.flowActions dp ca next) := by
    simpa only [List.nil_append] using head.append tail
  rw [Exec.flowActions_eq_descendantActions_of_currentTarget_ne
      next committed hforeign] at combined
  cases hs : Ninst.step ⟨pc, sevm, pre⟩ n with
  | halt execution =>
      simp only [Ninst.StepRun, hs, Step.Run] at hstep
      rcases hstep with ⟨_, heq⟩
      cases heq
      exact False.elim (Ninst.step_ne_halt_ok hs)
  | cont pc' actual =>
      simp only [Ninst.StepRun, hs, Step.Run] at hstep
      rcases hstep with ⟨_, heq⟩
      cases heq
      have hpc : pc' = pc + n.size := Ninst.step_cont_pc hs
      subst pc'
      have hevm : Evm.step ⟨pc, sevm, pre⟩ =
          .cont (pc + n.size) inter := by
        rw [Evm.step_next hat]
        exact hs
      have hcanonical : run = Exec.cont hevm next := Exec.unique _ _
      subst run
      rw [Exec.flowActions_eq_descendantActions_of_currentTarget_ne
          (Exec.cont hevm next) committed hforeign]
      unfold Exec.descendantActions at combined ⊢
      exact ⟨by simpa only [Exec.descendantFrames] using combined⟩
  | spawn frame resume pc' =>
      simp only [Ninst.StepRun, hs, Step.Run] at hstep
      rcases hstep with ⟨result, hframe, hresume⟩
      have hpc : pc' = pc + n.size := Ninst.step_spawn_pc hs
      subst pc'
      have hevm : Evm.step ⟨pc, sevm, pre⟩ =
          .spawn frame resume (pc + n.size) := by
        rw [Evm.step_next hat]
        exact hs
      have henter : ∃ result,
          frame.enter = .done result ∧
          resume.run result = .ok inter := by
        unfold RunFrame at hframe
        cases he : frame.enter with
        | done settled =>
            rw [he] at hframe
            exact ⟨settled, rfl, by rw [← hframe.2]; exact hresume.symm⟩
        | run child =>
            rw [he] at hframe
            rcases hframe with ⟨raw, hnone, -⟩
            cases hnone
      rcases henter with ⟨result, henter, hresume'⟩
      let canonical : Exec pc sevm pre out :=
        Exec.doneOk hevm henter hresume' next
      have hcanonical : run = canonical := Exec.unique _ _
      subst run
      rw [Exec.flowActions_eq_descendantActions_of_currentTarget_ne
          canonical committed hforeign]
      unfold Exec.descendantActions at combined ⊢
      exact ⟨by
        simpa only [canonical, Exec.descendantFrames] using combined⟩

/-- Foreign recursive-step handler.  It reconstructs the exact retained child
and continuation, proves that an installed child starts at a genuine fresh
frame root, transports that child's proof-indexed storage effect through the
actual settlement, and aligns the resulting labels with the canonical
settlement-pruned descendant traversal. -/
theorem Exec.CoreStorageSound.nextSome
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {n : Ninst}
    {cevm : Evm} {raw : Execution} {inter : Devm} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (hstep : Ninst.StepRun pc sevm pre n
      (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out)
    (hforeign : sevm.currentTarget ≠ ca)
    (ihChild : Exec.CoreStorageSound dp ca
      cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : Exec.CoreStorageSound dp ca
      (pc + n.size) sevm inter out) :
    Exec.CoreStorageSound dp ca pc sevm pre out := by
  cases n with
  | reg r =>
      simp [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hstep
  | push xs hxs =>
      simp [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hstep
  | exec x =>
      intro run committed hatp _
      have hxrun := XStep.run_toStep.mp hstep
      cases hs : Xinst.step sevm pre x with
      | done execution =>
          simp [hs, XStep.Run] at hxrun
      | spawn frame resume =>
          simp only [hs, XStep.Run] at hxrun
          obtain ⟨result, hframe, hresume⟩ := hxrun
          cases result with
          | error error =>
              cases resume <;>
                simp [Resume.run, liftToExecution] at hresume
          | ok settled =>
              have henter := (RunFrame.some_inv hframe).1
              have hsettle := (RunFrame.some_inv hframe).2
              have hevm : Evm.step ⟨pc, sevm, pre⟩ =
                  .spawn frame resume (pc + 1) := by
                rw [Evm.step_next hat]
                simp only [Ninst.step_exec, hs, XStep.toStep]
              have hr : resume.run (frame.settle raw) = .ok inter := by
                rw [← hsettle]
                exact hresume.symm
              let canonical : Exec pc sevm pre out :=
                Exec.runOk hevm henter child hr next
              have hcanonical : run = canonical := Exec.unique _ _
              subst run
              obtain ⟨hpc0, hgc, hsrc⟩ :=
                Evm.step_spawn_child hevm henter
              have hchildAt : Prog.At (weth10 dp) ca
                  cevm.pc cevm.sta cevm.dyna := by
                refine ⟨?_, fun htarget => ⟨?_, hpc0⟩⟩
                · rw [hgc ca]
                  exact hatp.1
                · have hne' :
                      sevm.currentTarget ≠ cevm.sta.currentTarget := by
                    rw [htarget]
                    exact hforeign
                  have hcode := hsrc hne'
                    (by rw [htarget]
                        exact not_empty_of_compile hatp.1)
                    (by rw [htarget]
                        exact not_delegation_of_compile hatp.1)
                  rw [hcode, htarget]
                  exact hatp.1
              rcases Frame.enter_run_inv henter with
                ⟨benv, htransfer, hinit⟩
              have hchildMemory : cevm.dyna.memory = Mem.empty := by
                rw [hinit]
                rfl
              have hchildDirect : cevm.sta.currentTarget = ca →
                  cevm.sta.codeAddress = some ca := by
                intro htarget
                have hinnerTarget :
                    frame.inner.currentTarget = ca := by
                  rw [← Frame.enter_run_currentTarget henter]
                  exact htarget
                have hparentNe :
                    sevm.currentTarget ≠ frame.inner.currentTarget := by
                  rw [hinnerTarget]
                  exact hforeign
                have hnonempty :
                    pre.getCode frame.inner.currentTarget ≠ .empty := by
                  rw [hinnerTarget]
                  exact not_empty_of_compile hatp.1
                have hcodeAddress :=
                  Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget
                    hs hparentNe hnonempty
                    (by rw [hinnerTarget]
                        dsimp only [getDelegatedCodeAddress]
                        rw [if_neg (not_delegation_of_compile hatp.1)])
                have hcodeAddressInit :=
                  congrArg (fun evm : Evm => evm.sta.codeAddress) hinit
                dsimp [initEvm, initSevm, Msg.withBenv] at hcodeAddressInit
                rw [hcodeAddressInit, hcodeAddress, hinnerTarget]
              have hbody : ∀
                  (rawCommitted : Execution.commits raw = true),
                  Nonempty (StorageSegmentEffect ca cevm.dyna
                    (Execution.committedPost raw rawCommitted)
                    (Exec.flowActions dp ca child)) := by
                intro rawCommitted
                exact ihChild child rawCommitted hchildAt
                  (fun htarget =>
                    ⟨⟨hpc0, hchildMemory⟩, hchildDirect htarget⟩)
              rcases Xinst.storageSegmentEffect_some_of_bodyEffect
                  hs hframe hresume.symm child hatp.1 hbody with ⟨head⟩
              have hatpInter : Prog.At (weth10 dp) ca
                  (pc + 1) sevm inter := by
                refine ⟨?_, fun htarget => (hforeign htarget).elim⟩
                rw [← head.codeEq]
                exact hatp.1
              rcases ihNext next committed hatpInter
                  (fun htarget => (hforeign htarget).elim) with ⟨tail⟩
              have combined := head.append tail
              rw [Exec.flowActions_eq_descendantActions_of_currentTarget_ne
                  next committed hforeign] at combined
              rw [Exec.flowActions_eq_descendantActions_of_currentTarget_ne
                  canonical committed hforeign]
              rw [Exec.descendantActions_runOk hevm henter child hr next]
              exact ⟨combined⟩

/-- Jump bookkeeping contributes an empty segment; the exact continuation
carries every retained descendant action. -/
theorem Exec.CoreStorageSound.jump
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {j : Jinst}
    {pc' : Nat} {inter : Devm} {out : Execution}
    (hat : Jinst.At sevm.code pc j)
    (hstep : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out)
    (hforeign : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreStorageSound dp ca pc' sevm inter out) :
    Exec.CoreStorageSound dp ca pc sevm pre out := by
  intro run committed hatp _
  have hevm : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' inter := by
    rw [Evm.step_jump hat]
    exact congrArg Step.ofJump hstep
  let canonical : Exec pc sevm pre out := Exec.cont hevm next
  have hcanonical : run = canonical := Exec.unique _ _
  subst run
  rcases Jinst.storageSegmentEffect hstep with ⟨head⟩
  have hatpInter : Prog.At (weth10 dp) ca pc' sevm inter := by
    refine ⟨?_, fun htarget => (hforeign htarget).elim⟩
    rw [← head.codeEq]
    exact hatp.1
  rcases ih next committed hatpInter
      (fun htarget => (hforeign htarget).elim) with ⟨tail⟩
  have combined : StorageSegmentEffect ca pre
      (Execution.committedPost out committed)
      (Exec.flowActions dp ca next) := by
    simpa only [List.nil_append] using head.append tail
  rw [Exec.flowActions_eq_descendantActions_of_currentTarget_ne
      next committed hforeign] at combined
  rw [Exec.flowActions_eq_descendantActions_of_currentTarget_ne
      canonical committed hforeign]
  unfold Exec.descendantActions at combined ⊢
  exact ⟨by simpa only [canonical, Exec.descendantFrames]
    using combined⟩

/-- A successful foreign terminal instruction closes the exact storage trace;
failed terminal outcomes cannot satisfy the committed premise. -/
theorem Exec.CoreStorageSound.last
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {l : Linst}
    {out : Execution}
    (hat : Linst.At sevm.code pc l)
    (hstep : Linst.Run sevm pre l out)
    (hforeign : sevm.currentTarget ≠ ca) :
    Exec.CoreStorageSound dp ca pc sevm pre out := by
  intro run committed _ _
  have hevm : Evm.step ⟨pc, sevm, pre⟩ = .halt out := by
    rw [Evm.step_last hat]
    exact congrArg Step.halt hstep
  let canonical : Exec pc sevm pre out := Exec.halt hevm
  have hcanonical : run = canonical := Exec.unique _ _
  subst run
  cases out with
  | error error =>
      simp [Execution.commits] at committed
  | ok post =>
      rcases Linst.foreignStorageSegmentEffect hstep hforeign with ⟨effect⟩
      rw [Exec.flowActions_eq_descendantActions_of_currentTarget_ne
          canonical committed hforeign]
      unfold Exec.descendantActions
      exact ⟨by
        simpa only [canonical, Exec.descendantFrames, List.filterMap_nil,
          Execution.committedPost] using effect⟩

/-- The generic interpreter recursion, with all foreign, failed, jump, and
terminal cases discharged.  The sole remaining input is the exact handler for
a root execution of the installed compiled WETH10 body. -/
theorem Exec.coreStorageSound_of_compiledBodyStorageHandler
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledBodyStorageHandler dp ca) :
    Exec.Fa (Exec.Wkn ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreStorageSound dp ca pc sevm pre out)) := by
  apply lift_core
    (ε := fun pc sevm pre out =>
      Exec.CoreStorageSound dp ca pc sevm pre out)
    (π := fun sevm pre post =>
      Exec.CoreStorageSound dp ca 0 sevm pre (.ok post))
    (analog := fun h => h)
    (ca := ca) (p := weth10 dp)
  · intro sevm pre post hrun htarget hdeeper
    exact handler hrun htarget hdeeper
  · intro pc sevm devm error devm' htarget
    exact Exec.CoreStorageSound.error
  · intro pc sevm devm hnone hforeign
    exact Exec.CoreStorageSound.error
  · intro pc sevm devm n error devm' hat hstep hforeign
    exact Exec.CoreStorageSound.error
  · intro pc sevm devm n evm_ execution error devm'
      hat hstep child hforeign ihChild
    exact Exec.CoreStorageSound.error
  · intro pc sevm devm n devm' execution
      hat hstep next hforeign ihNext
    exact Exec.CoreStorageSound.nextNone
      hat hstep next hforeign ihNext
  · intro pc sevm devm n evm_ execution devm' out
      hat hstep child next hforeign ihChild ihNext
    exact Exec.CoreStorageSound.nextSome
      hat hstep child next hforeign ihChild ihNext
  · intro pc sevm devm j error devm' hat hstep hforeign
    exact Exec.CoreStorageSound.error
  · intro pc sevm devm j pc' devm' execution
      hat hstep next hforeign ihNext
    exact Exec.CoreStorageSound.jump
      hat hstep next hforeign ihNext
  · intro pc sevm devm l execution hat hstep hforeign
    exact Exec.CoreStorageSound.last hat hstep hforeign

/-- The exact installed-execution theorem still required from the compiled
callback semantics.  This predicate does not assume an endpoint equation: it
asks for the operational segment trace itself for every actual committed
successful `Exec` proof at a location carrying the installed WETH10 program.
The commit premise is necessary because a raw `.ok` machine with a set error
flag is rolled back only by the enclosing message settlement. -/
def InstalledStorageSegmentTraceSound
    (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {pc : Nat} {sevm : Sevm} {pre post : Devm}
    (run : Exec pc sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true),
    Prog.At (weth10 dp) ca pc sevm pre →
      Exec.Frame.IsRoot (Exec.Frame.ofRun run committed) →
      sevm.codeAddress = some ca →
      Nonempty (Blanc.Weth10.Exec.StorageSegmentTrace dp ca run)

/-- The generic recursive lift turns a concrete compiled-body handler into the
public exact installed-execution trace theorem. -/
theorem CompiledBodyStorageHandler.installedStorageSegmentTraceSound
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledBodyStorageHandler dp ca) :
    InstalledStorageSegmentTraceSound dp ca := by
  intro pc sevm pre post run committed installed root direct
  have hfa := Exec.coreStorageSound_of_compiledBodyStorageHandler handler
  have hcore := hfa pc sevm pre (.ok post) run installed
  exact hcore run committed installed (fun _ => ⟨root, direct⟩)

/-- Discharging the exact operational trace seam yields the requested full
per-holder and aggregate accounting statement immediately. -/
theorem Exec.storageFlowAccounting_of_installedTraceSound
    {dp : DeployParams} {ca : Adr}
    (sound : InstalledStorageSegmentTraceSound dp ca)
    {pc : Nat} {sevm : Sevm} {pre post : Devm}
    (run : Exec pc sevm pre (.ok post))
    (installed : Prog.At (weth10 dp) ca pc sevm pre)
    (committed : Execution.commits (.ok post) = true)
    (root : Exec.Frame.IsRoot (Exec.Frame.ofRun run committed))
    (direct : sevm.codeAddress = some ca) :
    StorageFlowAccounting ca pre post (Exec.flowActions dp ca run) := by
  rcases sound run committed installed root direct with ⟨trace⟩
  exact trace.storageFlowAccounting

/-- Empty action segments account for an unchanged WETH10 storage map. -/
theorem StorageFlowAccounting.refl (ca : Adr) (state : Devm) :
    StorageFlowAccounting ca state state [] := by
  constructor <;>
    simp [holderFlowOfActions, HolderFlow.zero, supplyFlowOfActions,
      SupplyFlow.zero, holderCreditLossOfActions, creditLossOfActions]

/-- Equality of the public holder map is the empty-action accounting unit;
allowance and auxiliary-slot writes may still occur outside `Stor.rest`. -/
theorem StorageFlowAccounting.of_rest_eq
    {ca : Adr} {pre post : Devm}
    (h : Stor.rest (Devm.getStor pre ca) =
      Stor.rest (Devm.getStor post ca)) :
    StorageFlowAccounting ca pre post [] := by
  constructor <;>
    simp [holderFlowOfActions, HolderFlow.zero, supplyFlowOfActions,
      SupplyFlow.zero, holderCreditLossOfActions, creditLossOfActions,
      balSum, h]

/-- Full storage equality is a convenient specialization for foreign steps. -/
theorem StorageFlowAccounting.of_getStor_eq
    {ca : Adr} {pre post : Devm}
    (h : Devm.getStor pre ca = Devm.getStor post ca) :
    StorageFlowAccounting ca pre post [] :=
  StorageFlowAccounting.of_rest_eq (congrArg Stor.rest h)

/-- Sequential accounting composes by appending the exact action labels. -/
theorem StorageFlowAccounting.append
    {ca : Adr} {pre middle post : Devm}
    {left right : List FlowAction}
    (hleft : StorageFlowAccounting ca pre middle left)
    (hright : StorageFlowAccounting ca middle post right) :
    StorageFlowAccounting ca pre post (left ++ right) := by
  constructor
  · intro u
    have hl := hleft.holderEquation u
    have hr := hright.holderEquation u
    rw [holderFlowOfActions_append,
      holderCreditLossOfActions_append]
    simp only [HolderFlow.add]
    omega
  · have hl := hleft.supplyEquation
    have hr := hright.supplyEquation
    rw [supplyFlowOfActions_append, creditLossOfActions_append]
    simp only [SupplyFlow.add]
    omega

/-- Relation-style spelling of chronological append composition. -/
theorem StorageFlowAccounting.trans
    {ca : Adr} {pre middle post : Devm}
    {left right : List FlowAction}
    (hleft : StorageFlowAccounting ca pre middle left)
    (hright : StorageFlowAccounting ca middle post right) :
    StorageFlowAccounting ca pre post (left ++ right) :=
  hleft.append hright

end Weth10

end Blanc
