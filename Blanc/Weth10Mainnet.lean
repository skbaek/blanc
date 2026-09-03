import Blanc.Weth10AnyOrder

/-!
Ethereum-mainnet specializations of the schedule-parametric WETH10 results.

This is the only WETH10 proof module that names mainnet's configured fork
schedule or any of its four rule records.  The generic carrier, deployment,
redemption, and continuation results remain independent of named forks.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## Mainnet rule selection -/

/-- Every successful lookup in the currently modeled mainnet schedule selects
one of the four rule records named by that schedule. -/
theorem mainnet_rulesAt_eq_named
    {timestamp : Nat} {rules : ForkRules}
    (h : mainnetChainConfig.rulesAt timestamp = .ok rules) :
    rules = pragueRules ∨ rules = osakaRules ∨
      rules = bpo1Rules ∨ rules = bpo2Rules := by
  rw [ChainConfig.rulesAt] at h
  cases hf : mainnetChainConfig.forkAt timestamp with
  | error e => simp [hf] at h
  | ok f =>
    rw [hf] at h
    cases f <;> simp [Fork.rules, Fork.rules?] at h <;> simp_all

/-- At and after the final modeled mainnet activation, configured lookup
selects BPO2. -/
theorem mainnet_rulesAt_eq_bpo2_of_ge
    {timestamp : Nat} (h : mainnetBpo2Timestamp ≤ timestamp) :
    mainnetChainConfig.rulesAt timestamp = .ok bpo2Rules := by
  change 1_767_747_671 ≤ timestamp at h
  have hvalid : mainnetChainConfig.validate = .ok () := by decide
  rw [ChainConfig.rulesAt, ChainConfig.forkAt, hvalid]
  simp [ChainConfig.forkAt?, mainnetChainConfig, mainnetPragueTimestamp,
    mainnetOsakaTimestamp, mainnetBpo1Timestamp, mainnetBpo2Timestamp, h,
    Fork.rules, Fork.rules?]
  rfl

/-! ## Closed redemption ceiling under every mainnet rule set -/

theorem pragueRules_redemptionRuntimeCeiling_gasCap (q : Nat) :
    checkTransactionGasCap pragueRules.tx (redemptionRuntimeCeiling q) =
      .ok () := by
  rw [redemptionRuntimeCeiling_eq]
  decide

theorem osakaRules_redemptionRuntimeCeiling_gasCap (q : Nat) :
    checkTransactionGasCap osakaRules.tx (redemptionRuntimeCeiling q) =
      .ok () := by
  rw [redemptionRuntimeCeiling_eq]
  decide

theorem bpo1Rules_redemptionRuntimeCeiling_gasCap (q : Nat) :
    checkTransactionGasCap bpo1Rules.tx (redemptionRuntimeCeiling q) =
      .ok () := by
  rw [redemptionRuntimeCeiling_eq]
  decide

theorem bpo2Rules_redemptionRuntimeCeiling_gasCap (q : Nat) :
    checkTransactionGasCap bpo2Rules.tx (redemptionRuntimeCeiling q) =
      .ok () := by
  rw [redemptionRuntimeCeiling_eq]
  decide

/-- EIP-7825's ceiling, discharged for a *realizable* redemption transaction.

The four facts above bound `redemptionRuntimeCeiling`, which
`AdmissibleRedemptionTx.gas_bound` only places *below* `tx.gas`; on their own
they therefore never discharge `AdmissibleRedemptionTx.gas_cap`, whose
obligation is on `tx.gas` itself.  This does: every rule record the modeled
mainnet schedule can select admits any transaction gas limit up to EIP-7825's
`2 ^ 24`, so a caller holding `tx.gas ≤ 2 ^ 24` closes that obligation without
knowing which rules the block selects. -/
theorem mainnet_checkTransactionGasCap_of_le
    {timestamp gas : Nat} {rules : ForkRules}
    (hrules : mainnetChainConfig.rulesAt timestamp = .ok rules)
    (hgas : gas ≤ 2 ^ 24) :
    checkTransactionGasCap rules.tx gas = .ok () := by
  rcases mainnet_rulesAt_eq_named hrules with h | h | h | h <;> subst h <;>
    simp [checkTransactionGasCap, pragueRules, osakaRules, bpo1Rules,
      bpo2Rules, pragueTransactionLimits, osakaTransactionLimits] <;>
    omega

/-! ## BPO2 deployment root -/

/-- The exact creation-block timestamp committed by the executable WETH10
current-mainnet evidence lane: one 12-second slot after BPO2 activation. -/
def weth10CurrentMainnetCreationTimestamp : Nat := 1_767_747_683

/-- Kernel-decided synchronization pin between the Lean specialization and the
committed current-mainnet creation fixture. -/
theorem weth10CurrentMainnetCreation_rulesAt :
    mainnetChainConfig.rulesAt 1_767_747_683 = .ok bpo2Rules := by
  decide

/-- Current-mainnet specialization of the schedule-parametric deployment
root. -/
abbrev MainnetDeploymentRoot
    (base deployed : BlockChain) (dp : DeployParams) (ca : Adr) : Prop :=
  DeploymentRoot mainnetChainConfig base deployed dp ca

/-- A successful strict singleton deployment block in mainnet's BPO2 era
establishes the current-mainnet deployment root.  All fork-sensitive envelope
premises are stated against the selected `bpo2Rules` record. -/
theorem canonicalMainnetBpo2DeploymentStep_establishes_root
    (base deployed : BlockChain) (cb : CanonicalBlock)
    (deploymentTxBytes : Bytes) (deploymentTx : Tx) (sender ca : Adr)
    (htimestamp : mainnetBpo2Timestamp ≤ cb.block.header.timestamp)
    (hbase : CanonicalDeploymentBase mainnetChainConfig bpo2Rules
      base sender ca)
    (henv : CanonicalWeth10DeploymentBlock mainnetChainConfig bpo2Rules
      base cb deploymentTxBytes deploymentTx sender ca)
    (hstep : stateTransitionUsing mainnetChainConfig
      base cb.block = .ok deployed) :
    MainnetDeploymentRoot base deployed
      (freshDeployParams mainnetChainConfig.chainId.toB256 ca) ca := by
  have hselected :
      mainnetChainConfig.rulesAt cb.block.header.timestamp = .ok bpo2Rules :=
    mainnet_rulesAt_eq_bpo2_of_ge htimestamp
  rw [henv.rulesAt] at hselected
  exact canonicalDeploymentStep_establishes_root
    mainnetChainConfig bpo2Rules base deployed cb deploymentTxBytes
      deploymentTx sender ca hbase henv hstep

/-! ## Public current-mainnet instances

These declarations deliberately specialize the already-audited generic
theorems rather than replaying their proofs.  Rule-local arguments remain
explicit: callers may instantiate them with the result of `rulesAt`, while the
selection lemmas above show that a successful mainnet lookup is one of the
four named records. -/

theorem chainUsing_preserves_stable_mainnet
    (dp : DeployParams) (ca : Adr) (ch ch' : BlockChain)
    (hreach : BlockChain.ReachUsing mainnetChainConfig ch ch')
    (hstable : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  chainUsing_preserves_stable dp ca mainnetChainConfig ch ch' hreach hstable

theorem chain_reachable_backed_and_flash_zero_mainnet
    (dp : DeployParams) (ca : Adr) (ch ch' : BlockChain)
    (hreach : BlockChain.ReachUsing mainnetChainConfig ch ch')
    (hstable : Stable dp ca ch.state) :
    (ch'.state.getStor ca).get flashMintedSlot = 0 ∧
      balSum (ch'.state.getStor ca) ≤ (ch'.state.bal ca).toNat :=
  chain_reachable_backed_and_flash_zero
    dp ca mainnetChainConfig ch ch' hreach hstable

theorem deployment_reachable_residual_messageRedemption_enabled_mainnet
    {rules : ForkRules} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory mainnetChainConfig dp ca checkpoint future}
    {msg : Msg}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (henv : AdmissibleRedemptionMessage
      rules dp ca u recipient q future.state msg) :
    MessageRedemptionEnabled dp ca u recipient q future.state msg :=
  deployment_reachable_residual_messageRedemption_enabled
    hroot hcheckpoint hq henv

theorem deployment_reachable_residual_transactionRedemption_enabled_mainnet
    {rules : ForkRules} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory mainnetChainConfig dp ca checkpoint future}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (hentry : benv.state = future.state)
    (henv : AdmissibleRedemptionTx
      rules dp ca u recipient q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  deployment_reachable_residual_transactionRedemption_enabled
    hroot hcheckpoint hq hentry henv

theorem deployment_reachable_residual_selfMessageRedemption_enabled_mainnet
    {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory mainnetChainConfig dp ca checkpoint future}
    {msg : Msg}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (henv : AdmissibleSelfRedemptionMessage rules dp ca u q future.state msg) :
    MessageRedemptionEnabled dp ca u u q future.state msg :=
  deployment_reachable_residual_selfMessageRedemption_enabled
    hroot hcheckpoint hq henv

theorem
    deployment_reachable_residual_selfTransactionRedemption_enabled_mainnet
    {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory mainnetChainConfig dp ca checkpoint future}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (hentry : benv.state = future.state)
    (henv : AdmissibleSelfRedemptionTx rules dp ca u q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u u q benv bout tx index :=
  deployment_reachable_residual_selfTransactionRedemption_enabled
    hroot hcheckpoint hq hentry henv

theorem deployment_reachable_booked_messageRedemption_enabled_mainnet
    {rules : ForkRules} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain} {msg : Msg}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleRedemptionMessage
      rules dp ca u recipient q future.state msg) :
    MessageRedemptionEnabled dp ca u recipient q future.state msg :=
  deployment_reachable_booked_messageRedemption_enabled
    hroot hfuture hq henv

theorem deployment_reachable_booked_transactionRedemption_enabled_mainnet
    {rules : ForkRules} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hentry : benv.state = future.state)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleRedemptionTx
      rules dp ca u recipient q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  deployment_reachable_booked_transactionRedemption_enabled
    hroot hfuture hentry hq henv

theorem deployment_reachable_booked_selfTransactionRedemption_enabled_mainnet
    {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hentry : benv.state = future.state)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleSelfRedemptionTx rules dp ca u q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u u q benv bout tx index :=
  deployment_reachable_booked_selfTransactionRedemption_enabled
    hroot hfuture hentry hq henv

theorem
    deployment_reachable_booked_transactionRedemption_enabled_of_recoveredSender_mainnet
    {rules : ForkRules} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {maxPriorityFee maxFee : Nat}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hentry : benv.state = future.state)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : NonSignatureRedemptionTxEnvelope
      rules dp ca u recipient q benv bout tx index maxPriorityFee maxFee)
    (hrecovered : recoverSender benv.stat.chainId tx = .ok u) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  deployment_reachable_booked_transactionRedemption_enabled_of_recoveredSender
    hroot hfuture hentry hq henv hrecovered

theorem deployment_reachable_future_redeemable_mainnet
    {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig checkpoint future) :
    ∃ history, FutureRedemptionGuarantee
      mainnetChainConfig dp ca u checkpoint future history :=
  deployment_reachable_future_redeemable hroot hcheckpoint hfuture

theorem deployment_reachable_future_dualSelector_redeemable_mainnet
    {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig checkpoint future) :
    ∃ history, FutureDualSelectorRedemptionGuarantee
      mainnetChainConfig dp ca u checkpoint future history :=
  deployment_reachable_future_dualSelector_redeemable
    hroot hcheckpoint hfuture

theorem deployment_reachable_future_redeemable_allHolders_mainnet
    {dp : DeployParams} {ca : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig checkpoint future) :
    ∃ history, ∀ u : Adr, FutureRedemptionGuarantee
      mainnetChainConfig dp ca u checkpoint future history :=
  deployment_reachable_future_redeemable_allHolders
    hroot hcheckpoint hfuture

theorem deploymentRoot_allowanceQuiescent_mainnet
    {dp : DeployParams} {ca u : Adr} {base deployed : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca) :
    AllowanceQuiescent ca u deployed.state :=
  deploymentRoot_allowanceQuiescent hroot

theorem deployment_fullWindow_future_redeemable_mainnet
    {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future) :
    AllowanceQuiescent ca u deployed.state ∧
      ∃ history, FutureRedemptionGuarantee
        mainnetChainConfig dp ca u deployed future history :=
  deployment_fullWindow_future_redeemable hroot hfuture

theorem deployment_fullWindow_attributionRootAt_ne_checkpoint_mainnet
    {dp : DeployParams} {ca u : Adr} {base deployed future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (history : AccountedHistory mainnetChainConfig dp ca deployed future)
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

theorem deployment_fullWindow_permanentOutflowAuthorization_mainnet
    {dp : DeployParams} {ca u : Adr} {base deployed future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (history : AccountedHistory mainnetChainConfig dp ca deployed future)
    (hnc : NoAllowanceKeyCollision history)
    {earlier later : List CountedFrame} {record : CountedFrame}
    (hsplit : history.attributionLedger = earlier ++ record :: later)
    (hout : record.permanentOutflow u ≠ 0) :
    PermanentOutflowAuthorization record earlier.reverse u :=
  deployment_fullWindow_permanentOutflowAuthorization
    hroot history hnc hsplit hout

theorem
    deployment_fullWindow_hardenedOutflow_only_authorizingRoots_mainnet
    {dp : DeployParams} {ca u : Adr} {base deployed future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (history : AccountedHistory mainnetChainConfig dp ca deployed future)
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

theorem deployment_fullWindow_dormant_holder_balance_monotone_mainnet
    {dp : DeployParams} {ca u : Adr} {base deployed future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (history : AccountedHistory mainnetChainConfig dp ca deployed future)
    (hnc : NoAllowanceKeyCollision history)
    (hdormant : NoAuthorizingActBy u history) :
    bookedBalanceNat deployed.state ca u ≤
      bookedBalanceNat future.state ca u :=
  deployment_fullWindow_dormant_holder_balance_monotone
    hroot history hnc hdormant

theorem deployment_reachable_dormant_holder_balance_monotone_mainnet
    {dp : DeployParams} {ca u : Adr} {base deployed future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future) :
    ∃ history : AccountedHistory mainnetChainConfig dp ca deployed future,
      NoAllowanceKeyCollision history →
      NoAuthorizingActBy u history →
      bookedBalanceNat deployed.state ca u ≤
        bookedBalanceNat future.state ca u :=
  deployment_reachable_dormant_holder_balance_monotone hroot hfuture

theorem deployment_reachable_redeemClaims_anyOrder_mainnet
    {rules : ForkRules} {timestamp : Nat} {dp : DeployParams} {ca : Adr}
    {base deployed future : BlockChain} {cs ds : List RedemptionClaim}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hrules : mainnetChainConfig.rulesAt timestamp = .ok rules)
    (hadm : ClaimsAdmissible rules ca future.state cs)
    (hperm : cs.Perm ds) :
    ∃ post, RedemptionOutcome rules dp ca ds future.state post :=
  deployment_reachable_redeemClaims_anyOrder
    hroot hfuture hrules hadm hperm

theorem deployment_reachable_redeemEveryoneList_anyOrder_mainnet
    {rules : ForkRules} {timestamp : Nat} {dp : DeployParams} {ca : Adr}
    {base deployed future : BlockChain} {holders : List Adr}
    {recipient : Adr → Adr} {claims : List RedemptionClaim}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hrules : mainnetChainConfig.rulesAt timestamp = .ok rules)
    (hnodup : holders.Nodup)
    (hrecipients : ∀ u ∈ holders,
      ClaimAdmissible rules ca future.state
        ⟨u, bookedBalanceNat future.state ca u, recipient u⟩)
    (hperm :
      (fullBalanceClaims ca future.state holders recipient).Perm claims) :
    ∃ post, RedemptionOutcome rules dp ca claims future.state post :=
  deployment_reachable_redeemEveryoneList_anyOrder
    hroot hfuture hrules hnodup hrecipients hperm

/-! The schedule-indexed conservation, no-wrap, and determinism pins. -/

theorem AccountedHistory.flash_pair_totals_eq_mainnet
    {dp : DeployParams} {ca u : Adr} {checkpoint future : BlockChain}
    (history : AccountedHistory mainnetChainConfig dp ca checkpoint future) :
    (history.weth10Flow u).flashCredit =
      (history.weth10Flow u).flashRepayment :=
  history.flash_pair_totals_eq

theorem AccountedHistory.weth10Flow_eq_of_appliedBlocks_eq_mainnet
    {dp : DeployParams} {ca u : Adr} {checkpoint future : BlockChain}
    (history₁ history₂ :
      AccountedHistory mainnetChainConfig dp ca checkpoint future)
    (hblocks : history₁.appliedBlocks = history₂.appliedBlocks) :
    history₁.weth10Flow u = history₂.weth10Flow u :=
  AccountedHistory.weth10Flow_eq_of_appliedBlocks_eq history₁ history₂ hblocks

theorem AccountedHistory.noCommittedCreditWrap_mainnet
    {dp : DeployParams} {ca : Adr} {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory mainnetChainConfig dp ca checkpoint future) :
    FlowActionsCreditNof history.flowActions :=
  history.noCommittedCreditWrap hstable

theorem AccountedHistory.holderCreditLoss_eq_zero_mainnet
    {dp : DeployParams} {ca u : Adr} {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory mainnetChainConfig dp ca checkpoint future) :
    holderCreditLossOfActions history.flowActions u = 0 :=
  history.holderCreditLoss_eq_zero hstable

theorem holderFlow_conserved_mainnet
    {dp : DeployParams} {ca u : Adr} {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory mainnetChainConfig dp ca checkpoint future) :
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

theorem holderFlow_flash_cancelled_mainnet
    {dp : DeployParams} {ca u : Adr} {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory mainnetChainConfig dp ca checkpoint future) :
    (history.weth10Flow u).flashCredit =
        (history.weth10Flow u).flashRepayment ∧
      bookedBalanceNat checkpoint.state ca u +
          (history.weth10Flow u).ordinaryIn =
        bookedBalanceNat future.state ca u +
          (history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut :=
  holderFlow_flash_cancelled hstable history

theorem holderFlow_residual_floor_mainnet
    {dp : DeployParams} {ca u : Adr} {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory mainnetChainConfig dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u ≤
      bookedBalanceNat future.state ca u +
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) :=
  holderFlow_residual_floor hstable history

theorem holderFlow_truncated_floor_mainnet
    {dp : DeployParams} {ca u : Adr} {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory mainnetChainConfig dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u -
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) ≤
      bookedBalanceNat future.state ca u :=
  holderFlow_truncated_floor hstable history

theorem holderFlow_withdrawal_floor_mainnet
    {dp : DeployParams} {ca u : Adr} {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory mainnetChainConfig dp ca checkpoint future)
    (hnoExternalTransfer :
      (history.weth10Flow u).externalTransferredOut = 0) :
    bookedBalanceNat checkpoint.state ca u ≤
      (history.weth10Flow u).redeemed +
        bookedBalanceNat future.state ca u :=
  holderFlow_withdrawal_floor hstable history hnoExternalTransfer

end Weth10

end Blanc
