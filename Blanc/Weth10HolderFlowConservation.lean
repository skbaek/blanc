import Blanc.Weth10HolderFlowDeterminism
import Blanc.Weth10HolderFlowLocal

/-!
Arithmetic composition for the authentic WETH10 holder-flow ledger.

This file keeps the wrap-loss term explicit.  The semantic layers discharge
that term from the retained execution and stable-root hypotheses; none of the
definitions here admits a conservation equation as ledger input.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- Total modular credit loss attributed to one holder by the provenance-rich
action ledger. -/
def AccountedHistory.holderCreditLoss
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future)
    (u : Adr) : Nat :=
  holderCreditLossOfActions history.flowActions u

/-- The deterministic public observations are exactly the projection of the
provenance-rich action ledger retained by the same history. -/
theorem AccountedHistory.flowObservations_eq_map_flowActions
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) :
    history.flowObservations =
      history.flowActions.map FlowAction.observation := by
  induction history with
  | refl hcfg hctx hid => rfl
  | step prior accounted ih =>
      have hblock : accounted.observations =
          accounted.actions.map FlowAction.observation := by
        rw [accounted.observations_eq, accounted.actions_eq]
        rfl
      simp only [AccountedHistory.flowObservations,
        AccountedHistory.flowActions, List.map_append]
      rw [ih, hblock]

/-- The public executable fold and the provenance-rich action fold compute the
same holder totals. -/
theorem AccountedHistory.weth10Flow_eq_holderFlowOfActions
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future)
    (u : Adr) :
    history.weth10Flow u = holderFlowOfActions history.flowActions u := by
  unfold AccountedHistory.weth10Flow
  rw [history.flowObservations_eq_map_flowActions]
  exact holderFlowOfObservations_map_observation history.flowActions u

theorem FlowAction.holderCreditLoss_eq_zero_of_creditNof
    {action : FlowAction} (h : action.CreditNof) (u : Adr) :
    action.holderCreditLoss u = 0 := by
  unfold FlowAction.holderCreditLoss
  cases hcredit : action.credit with
  | none => rfl
  | some credit =>
      simp only
      by_cases hrecipient : credit.recipient = u
      · rw [if_pos hrecipient]
        exact credit.loss_eq_zero_iff.mpr (h credit hcredit)
      · rw [if_neg hrecipient]

theorem holderCreditLossOfActions_eq_zero_of_creditNof
    {actions : List FlowAction} (h : FlowActionsCreditNof actions)
    (u : Adr) :
    holderCreditLossOfActions actions u = 0 := by
  induction actions with
  | nil => rfl
  | cons action actions ih =>
      have haction : action.CreditNof := h action (by simp)
      have htail : FlowActionsCreditNof actions := by
        intro tail hmem
        exact h tail (by simp [hmem])
      simp only [holderCreditLossOfActions, List.map_cons, List.sum_cons]
      rw [action.holderCreditLoss_eq_zero_of_creditNof haction u]
      change 0 + holderCreditLossOfActions actions u = 0
      rw [ih htail]

/-! ## Pure cancellation and floor algebra -/

theorem holderFlow_conserved_of_loss_eq_zero
    {u : Adr} {initial final loss : Nat} (flow : HolderFlow u)
    (wrapAware :
      initial + flow.ordinaryIn + flow.selfTransfer + flow.flashCredit =
        final + flow.redeemed + flow.externalTransferredOut +
          flow.selfTransfer + flow.flashRepayment + loss)
    (lossZero : loss = 0) :
    initial + flow.ordinaryIn + flow.selfTransfer + flow.flashCredit =
      final + flow.redeemed + flow.externalTransferredOut +
        flow.selfTransfer + flow.flashRepayment := by
  omega

theorem holderFlow_flash_cancelled_of_conserved
    {u : Adr} {initial final : Nat} (flow : HolderFlow u)
    (flashPair : flow.flashCredit = flow.flashRepayment)
    (conserved :
      initial + flow.ordinaryIn + flow.selfTransfer + flow.flashCredit =
        final + flow.redeemed + flow.externalTransferredOut +
          flow.selfTransfer + flow.flashRepayment) :
    initial + flow.ordinaryIn =
      final + flow.redeemed + flow.externalTransferredOut := by
  omega

theorem holderFlow_residual_floor_of_cancelled
    {u : Adr} {initial final : Nat} (flow : HolderFlow u)
    (cancelled : initial + flow.ordinaryIn =
      final + flow.redeemed + flow.externalTransferredOut) :
    initial ≤ final + (flow.redeemed + flow.externalTransferredOut) := by
  omega

theorem holderFlow_truncated_floor_of_residual
    {u : Adr} {initial final : Nat} (flow : HolderFlow u)
    (floor : initial ≤
      final + (flow.redeemed + flow.externalTransferredOut)) :
    initial - (flow.redeemed + flow.externalTransferredOut) ≤ final := by
  omega

theorem holderFlow_withdrawal_floor_of_residual
    {u : Adr} {initial final : Nat} (flow : HolderFlow u)
    (floor : initial ≤
      final + (flow.redeemed + flow.externalTransferredOut))
    (noExternalTransfer : flow.externalTransferredOut = 0) :
    initial ≤ flow.redeemed + final := by
  omega

/-! ## Aggregate supply and wrap loss -/

/-- Aggregate quantities needed only for the no-wrap argument.  Ordinary
transfers disappear from this view; their possible recipient wrap remains in
`creditLossOfActions`. -/
structure SupplyFlow where
  ordinaryIn : Nat
  redeemed : Nat
  flashCredit : Nat
  flashRepayment : Nat
deriving DecidableEq

def SupplyFlow.zero : SupplyFlow := ⟨0, 0, 0, 0⟩

def SupplyFlow.add (left right : SupplyFlow) : SupplyFlow :=
  ⟨left.ordinaryIn + right.ordinaryIn,
    left.redeemed + right.redeemed,
    left.flashCredit + right.flashCredit,
    left.flashRepayment + right.flashRepayment⟩

def FlowAtom.supplyFlow : FlowAtom → SupplyFlow
  | .ordinaryMint _ _ amount => { SupplyFlow.zero with ordinaryIn := amount }
  | .transfer .. => SupplyFlow.zero
  | .redemption _ _ _ amount => { SupplyFlow.zero with redeemed := amount }
  | .flashPair _ _ amount =>
      { SupplyFlow.zero with flashCredit := amount, flashRepayment := amount }

def supplyFlowOfActions (actions : List FlowAction) : SupplyFlow :=
  actions.foldl (fun total action => total.add action.atom.supplyFlow)
    SupplyFlow.zero

theorem FlowAtom.supplyFlow_flash_eq (atom : FlowAtom) :
    atom.supplyFlow.flashCredit = atom.supplyFlow.flashRepayment := by
  cases atom <;> rfl

private theorem supplyFlowOfActions_flash_eq_from
    (actions : List FlowAction) (initial : SupplyFlow)
    (hinitial : initial.flashCredit = initial.flashRepayment) :
    (actions.foldl (fun total action =>
      total.add action.atom.supplyFlow) initial).flashCredit =
    (actions.foldl (fun total action =>
      total.add action.atom.supplyFlow) initial).flashRepayment := by
  induction actions generalizing initial with
  | nil => exact hinitial
  | cons action actions ih =>
      simp only [List.foldl_cons]
      apply ih
      simp only [SupplyFlow.add]
      rw [hinitial, action.atom.supplyFlow_flash_eq]

theorem supplyFlowOfActions_flash_eq (actions : List FlowAction) :
    (supplyFlowOfActions actions).flashCredit =
      (supplyFlowOfActions actions).flashRepayment := by
  apply supplyFlowOfActions_flash_eq_from
  rfl

def FlowAction.creditLossTotal (action : FlowAction) : Nat :=
  match action.credit with
  | some credit => credit.loss
  | none => 0

def creditLossOfActions (actions : List FlowAction) : Nat :=
  (actions.map FlowAction.creditLossTotal).sum

theorem CreditOccurrence.nof_of_loss_lt_modulus
    (credit : CreditOccurrence) (h : credit.loss < 2 ^ 256) :
    credit.Nof := by
  by_contra hnof
  have hloss : credit.loss = 2 ^ 256 := by
    exact creditLoss_eq_two_pow_of_not_nof credit.before credit.amountWord hnof
  omega

theorem FlowActionsCreditNof.of_creditLoss_lt_modulus
    {actions : List FlowAction}
    (h : creditLossOfActions actions < 2 ^ 256) :
    FlowActionsCreditNof actions := by
  induction actions with
  | nil => simp [FlowActionsCreditNof]
  | cons head tail ih =>
      have hhead : head.creditLossTotal < 2 ^ 256 := by
        simp only [creditLossOfActions, List.map_cons, List.sum_cons] at h
        omega
      have htail : creditLossOfActions tail < 2 ^ 256 := by
        exact lt_of_le_of_lt (Nat.le_add_left _ _) h
      intro action hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · intro credit hcredit
        unfold FlowAction.creditLossTotal at hhead
        rw [hcredit] at hhead
        exact credit.nof_of_loss_lt_modulus hhead
      · exact ih htail action hmem

/-- The arithmetic heart of committed no-wrap.  The first premise is the
wrap-aware booked-supply equation; the second is the independently proved ETH
movement inequality.  Exact flash pairing cancels temporary supply before the
modulus bound is used. -/
theorem creditLoss_lt_modulus_of_supply_eth
    {initialSupply finalSupply initialEth finalEth loss : Nat}
    (flow : SupplyFlow)
    (supplyEquation :
      initialSupply + flow.ordinaryIn + flow.flashCredit =
        finalSupply + flow.redeemed + flow.flashRepayment + loss)
    (flashPair : flow.flashCredit = flow.flashRepayment)
    (initialBacked : initialSupply ≤ initialEth)
    (ethMovement :
      initialEth + flow.ordinaryIn ≤ finalEth + flow.redeemed)
    (finalEthLt : finalEth < 2 ^ 256) :
    loss < 2 ^ 256 := by
  omega

theorem FlowActionsCreditNof.of_supply_eth
    {actions : List FlowAction}
    {initialSupply finalSupply initialEth finalEth : Nat}
    (supplyEquation :
      initialSupply + (supplyFlowOfActions actions).ordinaryIn +
          (supplyFlowOfActions actions).flashCredit =
        finalSupply + (supplyFlowOfActions actions).redeemed +
          (supplyFlowOfActions actions).flashRepayment +
            creditLossOfActions actions)
    (initialBacked : initialSupply ≤ initialEth)
    (ethMovement :
      initialEth + (supplyFlowOfActions actions).ordinaryIn ≤
        finalEth + (supplyFlowOfActions actions).redeemed)
    (finalEthLt : finalEth < 2 ^ 256) :
    FlowActionsCreditNof actions := by
  apply FlowActionsCreditNof.of_creditLoss_lt_modulus
  exact creditLoss_lt_modulus_of_supply_eth
    (supplyFlowOfActions actions) supplyEquation
    (supplyFlowOfActions_flash_eq actions) initialBacked ethMovement finalEthLt

end Weth10

end Blanc
