import Blanc.Weth10AnyOrder

/-!
Thin compatibility corollaries for the historical Prague-only WETH10 API.

The generic theorem remains the proof owner in every case.  This module is the
only public specialization layer that names `ChainConfig.pragueOnly`; current
mainnet clients should import `Blanc.Weth10Mainnet` instead.
-/

namespace Blanc

open Jaune

namespace Weth10

abbrev PragueDeploymentRoot
    (chainId : UInt64) (base deployed : BlockChain)
    (dp : DeployParams) (ca : Adr) : Prop :=
  DeploymentRoot (ChainConfig.pragueOnly chainId) base deployed dp ca

/-! ## Legacy fixed-Prague entry points -/

theorem stateTransition_preserves_stable
    (dp : DeployParams) (ca : Adr)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (hstable : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  stateTransitionWith_preserves_stable
    dp ca pragueRules ch ch' block h_run h_wds hstable

theorem chain_preserves_stable
    (dp : DeployParams) (ca : Adr) (ch ch' : BlockChain)
    (hreach : BlockChain.Reach ch ch')
    (hstable : Stable dp ca ch.state) :
    Stable dp ca ch'.state := by
  have hbacked : (backedSpec weth10 dp).StateInv ca ch.state :=
    ⟨hstable.code, hstable.sumNof, hstable.backed⟩
  have hflash : (flashExactSpec dp 0).StateInv ca ch.state :=
    ⟨hstable.code, trivial, hstable.flashZero⟩
  have hbacked' := ContractSpec.chain_preserves_inv ca
    (backedSpec_preserves dp ca) ch ch' hreach hbacked
  have hflash' := ContractSpec.chain_preserves_inv ca
    (flashExactSpec_preserves dp ca 0) ch ch' hreach hflash
  exact ⟨hbacked'.code, hbacked'.side, hbacked'.inv, hflash'.inv⟩

theorem addBlockToChain_preserves_stable
    (dp : DeployParams) (ca : Adr)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChain ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (hstable : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  addBlockToChainWith_preserves_stable
    dp ca pragueRules ch ch' rlp h_run h_wds hstable

/-! ## Named Prague-only corollaries -/

theorem chainUsing_preserves_stable_prague
    {chainId : UInt64} (dp : DeployParams) (ca : Adr)
    (ch ch' : BlockChain)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId) ch ch')
    (hstable : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  chainUsing_preserves_stable
    dp ca (ChainConfig.pragueOnly chainId) ch ch' hreach hstable

theorem chain_reachable_backed_and_flash_zero_prague
    {chainId : UInt64} (dp : DeployParams) (ca : Adr)
    (ch ch' : BlockChain)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId) ch ch')
    (hstable : Stable dp ca ch.state) :
    (ch'.state.getStor ca).get flashMintedSlot = 0 ∧
      balSum (ch'.state.getStor ca) ≤ (ch'.state.bal ca).toNat :=
  chain_reachable_backed_and_flash_zero
    dp ca (ChainConfig.pragueOnly chainId) ch ch' hreach hstable

theorem deployment_reachable_residual_messageRedemption_enabled_prague
    {chainId : UInt64} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future} {msg : Msg}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (henv : AdmissibleRedemptionMessage
      rules dp ca u recipient q future.state msg) :
    MessageRedemptionEnabled dp ca u recipient q future.state msg :=
  deployment_reachable_residual_messageRedemption_enabled
    hroot hcheckpoint hq henv

theorem deployment_reachable_residual_transactionRedemption_enabled_prague
    {chainId : UInt64} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (hentry : benv.state = future.state)
    (henv : AdmissibleRedemptionTx
      rules dp ca u recipient q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  deployment_reachable_residual_transactionRedemption_enabled
    hroot hcheckpoint hq hentry henv

theorem deployment_reachable_residual_selfMessageRedemption_enabled_prague
    {chainId : UInt64} {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future} {msg : Msg}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (henv : AdmissibleSelfRedemptionMessage rules dp ca u q future.state msg) :
    MessageRedemptionEnabled dp ca u u q future.state msg :=
  deployment_reachable_residual_selfMessageRedemption_enabled
    hroot hcheckpoint hq henv

theorem deployment_reachable_residual_selfTransactionRedemption_enabled_prague
    {chainId : UInt64} {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (hentry : benv.state = future.state)
    (henv : AdmissibleSelfRedemptionTx rules dp ca u q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u u q benv bout tx index :=
  deployment_reachable_residual_selfTransactionRedemption_enabled
    hroot hcheckpoint hq hentry henv

theorem deployment_reachable_booked_messageRedemption_enabled_prague
    {chainId : UInt64} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain} {msg : Msg}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed future)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleRedemptionMessage
      rules dp ca u recipient q future.state msg) :
    MessageRedemptionEnabled dp ca u recipient q future.state msg :=
  deployment_reachable_booked_messageRedemption_enabled
    hroot hfuture hq henv

theorem deployment_reachable_booked_transactionRedemption_enabled_prague
    {chainId : UInt64} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed future)
    (hentry : benv.state = future.state)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleRedemptionTx
      rules dp ca u recipient q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  deployment_reachable_booked_transactionRedemption_enabled
    hroot hfuture hentry hq henv

theorem deployment_reachable_booked_selfTransactionRedemption_enabled_prague
    {chainId : UInt64} {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed future)
    (hentry : benv.state = future.state)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleSelfRedemptionTx rules dp ca u q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u u q benv bout tx index :=
  deployment_reachable_booked_selfTransactionRedemption_enabled
    hroot hfuture hentry hq henv

theorem
    deployment_reachable_booked_transactionRedemption_enabled_of_recoveredSender_prague
    {chainId : UInt64} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {maxPriorityFee maxFee : Nat}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed future)
    (hentry : benv.state = future.state)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : NonSignatureRedemptionTxEnvelope
      rules dp ca u recipient q benv bout tx index maxPriorityFee maxFee)
    (hrecovered : recoverSender benv.stat.chainId tx = .ok u) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  deployment_reachable_booked_transactionRedemption_enabled_of_recoveredSender
    hroot hfuture hentry hq henv hrecovered

theorem deployment_reachable_future_redeemable_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed checkpoint)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) checkpoint future) :
    ∃ history, FutureRedemptionGuarantee
      (ChainConfig.pragueOnly chainId) dp ca u checkpoint future history :=
  deployment_reachable_future_redeemable hroot hcheckpoint hfuture

theorem deployment_reachable_future_dualSelector_redeemable_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed checkpoint)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) checkpoint future) :
    ∃ history, FutureDualSelectorRedemptionGuarantee
      (ChainConfig.pragueOnly chainId) dp ca u checkpoint future history :=
  deployment_reachable_future_dualSelector_redeemable
    hroot hcheckpoint hfuture

theorem deployment_reachable_future_redeemable_allHolders_prague
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed checkpoint)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) checkpoint future) :
    ∃ history, ∀ u : Adr, FutureRedemptionGuarantee
      (ChainConfig.pragueOnly chainId) dp ca u checkpoint future history :=
  deployment_reachable_future_redeemable_allHolders
    hroot hcheckpoint hfuture

theorem deploymentRoot_allowanceQuiescent_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {base deployed : BlockChain}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca) :
    AllowanceQuiescent ca u deployed.state :=
  deploymentRoot_allowanceQuiescent hroot

theorem deployment_fullWindow_future_redeemable_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed future) :
    AllowanceQuiescent ca u deployed.state ∧
      ∃ history, FutureRedemptionGuarantee
        (ChainConfig.pragueOnly chainId) dp ca u deployed future history :=
  deployment_fullWindow_future_redeemable hroot hfuture

theorem deployment_fullWindow_attributionRootAt_ne_checkpoint_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca deployed future)
    {earlier later : List CountedFrame} {record : CountedFrame}
    {action : FlowAction} {debit : DebitProvenance} {event : AllowanceEvent}
    (hsplit : history.attributionLedger = earlier ++ record :: later)
    (hout : record.permanentOutflow u ≠ 0)
    (haction : record.action = some action)
    (hdebit : action.debit = some debit)
    (hevent : record.allowance = some event)
    (hkey : delegatedKey? debit.branch = some event.key) :
    attributionRootAt earlier.reverse event.key ≠ .checkpoint :=
  deployment_fullWindow_attributionRootAt_ne_checkpoint
    hroot history hsplit hout haction hdebit hevent hkey

theorem deployment_fullWindow_permanentOutflowAuthorization_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca deployed future)
    (hnc : NoAllowanceKeyCollision history)
    {earlier later : List CountedFrame} {record : CountedFrame}
    (hsplit : history.attributionLedger = earlier ++ record :: later)
    (hout : record.permanentOutflow u ≠ 0) :
    PermanentOutflowAuthorization record earlier.reverse u :=
  deployment_fullWindow_permanentOutflowAuthorization
    hroot history hnc hsplit hout

theorem deployment_fullWindow_hardenedOutflow_only_authorizingRoots_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca deployed future)
    (hnc : NoAllowanceKeyCollision history) :
    ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut =
      hardenedOutflow history u) ∧
      ∀ earlier record later,
        history.attributionLedger = earlier ++ record :: later →
        record.permanentOutflow u ≠ 0 →
        PermanentOutflowAuthorization record earlier.reverse u :=
  deployment_fullWindow_hardenedOutflow_only_authorizingRoots
    hroot history hnc

theorem deployment_fullWindow_dormant_holder_balance_monotone_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca deployed future)
    (hnc : NoAllowanceKeyCollision history)
    (hdormant : NoAuthorizingActBy u history) :
    bookedBalanceNat deployed.state ca u ≤
      bookedBalanceNat future.state ca u :=
  deployment_fullWindow_dormant_holder_balance_monotone
    hroot history hnc hdormant

theorem deployment_reachable_dormant_holder_balance_monotone_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed future) :
    ∃ history : AccountedHistory (ChainConfig.pragueOnly chainId)
        dp ca deployed future,
      NoAllowanceKeyCollision history →
      NoAuthorizingActBy u history →
      bookedBalanceNat deployed.state ca u ≤
        bookedBalanceNat future.state ca u :=
  deployment_reachable_dormant_holder_balance_monotone hroot hfuture

theorem deployment_reachable_redeemClaims_anyOrder_prague
    {chainId : UInt64} {rules : ForkRules} {timestamp : Nat}
    {dp : DeployParams} {ca : Adr}
    {base deployed future : BlockChain} {cs ds : List RedemptionClaim}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed future)
    (hrules : (ChainConfig.pragueOnly chainId).rulesAt timestamp = .ok rules)
    (hadm : ClaimsAdmissible rules ca future.state cs)
    (hperm : cs.Perm ds) :
    ∃ post, RedemptionOutcome rules dp ca ds future.state post :=
  deployment_reachable_redeemClaims_anyOrder
    hroot hfuture hrules hadm hperm

theorem deployment_reachable_redeemEveryoneList_anyOrder_prague
    {chainId : UInt64} {rules : ForkRules} {timestamp : Nat}
    {dp : DeployParams} {ca : Adr}
    {base deployed future : BlockChain} {holders : List Adr}
    {recipient : Adr → Adr} {claims : List RedemptionClaim}
    (hroot : PragueDeploymentRoot chainId base deployed dp ca)
    (hfuture : BlockChain.ReachUsing
      (ChainConfig.pragueOnly chainId) deployed future)
    (hrules : (ChainConfig.pragueOnly chainId).rulesAt timestamp = .ok rules)
    (hnodup : holders.Nodup)
    (hrecipients : ∀ u ∈ holders,
      ClaimAdmissible rules ca future.state
        ⟨u, bookedBalanceNat future.state ca u, recipient u⟩)
    (hperm :
      (fullBalanceClaims ca future.state holders recipient).Perm claims) :
    ∃ post, RedemptionOutcome rules dp ca claims future.state post :=
  deployment_reachable_redeemEveryoneList_anyOrder
    hroot hfuture hrules hnodup hrecipients hperm

theorem AccountedHistory.flash_pair_totals_eq_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future) :
    (history.weth10Flow u).flashCredit =
      (history.weth10Flow u).flashRepayment :=
  history.flash_pair_totals_eq

theorem AccountedHistory.weth10Flow_eq_of_appliedBlocks_eq_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history₁ history₂ : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future)
    (hblocks : history₁.appliedBlocks = history₂.appliedBlocks) :
    history₁.weth10Flow u = history₂.weth10Flow u :=
  AccountedHistory.weth10Flow_eq_of_appliedBlocks_eq history₁ history₂ hblocks

theorem AccountedHistory.noCommittedCreditWrap_prague
    {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future) :
    FlowActionsCreditNof history.flowActions :=
  history.noCommittedCreditWrap hstable

theorem AccountedHistory.holderCreditLoss_eq_zero_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future) :
    holderCreditLossOfActions history.flowActions u = 0 :=
  history.holderCreditLoss_eq_zero hstable

theorem holderFlow_conserved_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u +
        (history.weth10Flow u).ordinaryIn +
        (history.weth10Flow u).selfTransfer +
        (history.weth10Flow u).flashCredit =
      bookedBalanceNat future.state ca u +
        (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut +
        (history.weth10Flow u).selfTransfer +
        (history.weth10Flow u).flashRepayment :=
  holderFlow_conserved hstable history

theorem holderFlow_flash_cancelled_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future) :
    (history.weth10Flow u).flashCredit =
        (history.weth10Flow u).flashRepayment ∧
      bookedBalanceNat checkpoint.state ca u +
          (history.weth10Flow u).ordinaryIn =
        bookedBalanceNat future.state ca u +
          (history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut :=
  holderFlow_flash_cancelled hstable history

theorem holderFlow_residual_floor_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u ≤
      bookedBalanceNat future.state ca u +
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) :=
  holderFlow_residual_floor hstable history

theorem holderFlow_truncated_floor_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u -
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) ≤
      bookedBalanceNat future.state ca u :=
  holderFlow_truncated_floor hstable history

theorem holderFlow_withdrawal_floor_prague
    {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory (ChainConfig.pragueOnly chainId)
      dp ca checkpoint future)
    (hnoExternalTransfer :
      (history.weth10Flow u).externalTransferredOut = 0) :
    bookedBalanceNat checkpoint.state ca u ≤
      (history.weth10Flow u).redeemed +
        bookedBalanceNat future.state ca u :=
  holderFlow_withdrawal_floor hstable history hnoExternalTransfer

end Weth10

end Blanc
