import Blanc.Weth10AnyOrder
import Blanc.LadderReached

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

/-- Every successful lookup in the currently modeled mainnet schedule at or
after Prague selects one of the four rule records named by that schedule. -/
theorem mainnet_rulesAt_eq_named
    {number timestamp : Nat} {rules : ForkRules}
    (hmodern : mainnetPragueTimestamp ≤ timestamp)
    (h : mainnetChainConfig.rulesAt number timestamp = .ok rules) :
    rules = pragueRules ∨ rules = osakaRules ∨
      rules = bpo1Rules ∨ rules = bpo2Rules := by
  rw [ChainConfig.rulesAt] at h
  cases hf : mainnetChainConfig.forkAt number timestamp with
  | error e => simp only [hf, Except.bind_error, reduceCtorEq] at h
  | ok f =>
    rw [hf] at h
    have hcov := mainnetChainConfig_covered number timestamp f hmodern hf
    unfold CoveredFork coveredForks at hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcov
    simp only [bind, Except.bind, Fork.rules, Except.mapError] at h
    rcases hcov with rfl | rfl | rfl | rfl <;>
      simp only [Fork.rules?, Except.ok.injEq] at h <;> subst h <;>
      simp only [true_or, or_true]

/-- At and after the final modeled mainnet activation, configured lookup
selects BPO2. -/
theorem mainnet_rulesAt_eq_bpo2_of_ge
    {number timestamp : Nat} (h : mainnetBpo2Timestamp ≤ timestamp) :
    mainnetChainConfig.rulesAt number timestamp = .ok bpo2Rules := by
  change 1_767_747_671 ≤ timestamp at h
  have hvalid : mainnetChainConfig.validate = .ok () := by decide
  rw [ChainConfig.rulesAt, ChainConfig.forkAt, hvalid]
  simp only [ChainConfig.forkAt?, mainnetChainConfig, mainnetPragueTimestamp, mainnetOsakaTimestamp,
    mainnetBpo1Timestamp, mainnetBpo2Timestamp, List.getLast?_filter, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, h, decide_true, List.find?_cons_of_pos,
    Option.map_some, Fork.rules, bind_assoc, Except.bind_ok]
  simp only [ForkActivation.atTime, ForkCriterion.reached, h, decide_true,
    List.find?_cons_of_pos, Option.map_some]
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
    {number timestamp gas : Nat} {rules : ForkRules}
    (hrules : mainnetChainConfig.rulesAt number timestamp = .ok rules)
    (hgas : gas ≤ 2 ^ 24) :
    checkTransactionGasCap rules.tx gas = .ok () := by
  rw [ChainConfig.rulesAt] at hrules
  cases hf : mainnetChainConfig.forkAt number timestamp with
  | error e => simp only [hf, Except.bind_error, reduceCtorEq] at hrules
  | ok f =>
    rw [hf] at hrules
    simp only [bind, Except.bind, Fork.rules, Except.mapError] at hrules
    cases f <;> simp only [Fork.rules?, Except.ok.injEq, reduceCtorEq] at hrules <;>
      subst hrules <;>
      first
        | rfl
        | (change (if gas > 16777216 then _ else .ok () : Except TxValidationError Unit) = .ok ()
           exact ite_eq_right (Nat.not_lt.mpr hgas))

/-! ## BPO2 deployment root -/

/-- The exact creation-block timestamp committed by the executable WETH10
current-mainnet evidence lane: one 12-second slot after BPO2 activation. -/
def weth10CurrentMainnetCreationTimestamp : Nat := 1_767_747_683

/-- Kernel-decided synchronization pin between the Lean specialization and the
committed current-mainnet creation fixture. -/
theorem weth10CurrentMainnetCreation_rulesAt (number : Nat) :
    mainnetChainConfig.rulesAt number 1_767_747_683 = .ok bpo2Rules :=
  mainnet_rulesAt_eq_bpo2_of_ge (by decide)

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
    (hbase : CanonicalDeploymentBase mainnetChainConfig .bpo2
      base sender ca)
    (henv : CanonicalWeth10DeploymentBlock mainnetChainConfig .bpo2
      base cb deploymentTxBytes deploymentTx sender ca)
    (hstep : stateTransitionUsing mainnetChainConfig
      base cb.block = .ok deployed) :
    MainnetDeploymentRoot base deployed
      (freshDeployParams mainnetChainConfig.chainId.toB256 ca) ca :=
  -- `htimestamp` is retained for the public statement; the envelope's
  -- `forkAt` field already pins the selected fork to `.bpo2`.
  have _ := htimestamp
  canonicalDeploymentStep_establishes_root
    mainnetChainConfig .bpo2 base deployed cb deploymentTxBytes
      deploymentTx sender ca hbase henv CoveredFork.bpo2 hstep

/-! ## Public current-mainnet instances

These declarations deliberately specialize the already-audited generic
theorems rather than replaying their proofs.  Rule-local arguments remain
explicit: callers may instantiate them with the result of `rulesAt`, while the
selection lemmas above show that a successful mainnet lookup is one of the
four named records. -/

theorem chainUsing_preserves_stable_mainnet
    (dp : DeployParams) (ca : Adr) (ch ch' : BlockChain)
    (hreach : BlockChain.ReachUsing mainnetChainConfig ch ch')
    (hstable : Stable dp ca ch.state)
    (hstart : ∃ parent, ch.blocks.getLast? = some parent ∧
      mainnetPragueTimestamp ≤ parent.header.timestamp) :
    Stable dp ca ch'.state :=
  chainUsing_preserves_stable_of_reached dp ca mainnetChainConfig mainnetPragueTimestamp
    mainnetChainConfig_covered ch ch' hreach hstable hstart

theorem chain_reachable_backed_and_flash_zero_mainnet
    (dp : DeployParams) (ca : Adr) (ch ch' : BlockChain)
    (hreach : BlockChain.ReachUsing mainnetChainConfig ch ch')
    (hstable : Stable dp ca ch.state)
    (hstart : ∃ parent, ch.blocks.getLast? = some parent ∧
      mainnetPragueTimestamp ≤ parent.header.timestamp) :
    (ch'.state.getStor ca).get flashMintedSlot = 0 ∧
      balSum (ch'.state.getStor ca) ≤ (ch'.state.bal ca).toNat :=
  have h := chainUsing_preserves_stable_mainnet dp ca ch ch' hreach hstable hstart
  ⟨h.flashZero, h.solvent⟩

/-- A current-mainnet deployment root's tip is at or past Prague's timestamp:
the deployment block ran a covered fork, and mainnet selects covered forks only
from Prague on. -/
theorem mainnetDeploymentRoot_pragueFloor
    {base deployed : BlockChain} {dp : DeployParams} {ca : Adr}
    (hroot : MainnetDeploymentRoot base deployed dp ca) :
    ∃ tip, deployed.blocks.getLast? = some tip ∧
      mainnetPragueTimestamp ≤ tip.header.timestamp :=
  DeploymentRoot.tip_floor hroot mainnetChainConfig_pragueTimestamp_le_of_covered

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
  deployment_reachable_residual_messageRedemption_enabled_of_reached
    hroot mainnetPragueTimestamp mainnetChainConfig_covered
    (mainnetDeploymentRoot_pragueFloor hroot) hcheckpoint hq henv

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
  deployment_reachable_residual_transactionRedemption_enabled_of_reached
    hroot mainnetPragueTimestamp mainnetChainConfig_covered
    (mainnetDeploymentRoot_pragueFloor hroot) hcheckpoint hq hentry henv

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
  deployment_reachable_residual_selfMessageRedemption_enabled_of_reached
    hroot mainnetPragueTimestamp mainnetChainConfig_covered
    (mainnetDeploymentRoot_pragueFloor hroot) hcheckpoint hq henv

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
  deployment_reachable_residual_selfTransactionRedemption_enabled_of_reached
    hroot mainnetPragueTimestamp mainnetChainConfig_covered
    (mainnetDeploymentRoot_pragueFloor hroot) hcheckpoint hq hentry henv

theorem deployment_reachable_booked_messageRedemption_enabled_mainnet
    {rules : ForkRules} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain} {msg : Msg}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleRedemptionMessage
      rules dp ca u recipient q future.state msg) :
    MessageRedemptionEnabled dp ca u recipient q future.state msg :=
  deployment_reachable_booked_messageRedemption_enabled_of_reached
    hroot mainnetPragueTimestamp mainnetChainConfig_covered
    (mainnetDeploymentRoot_pragueFloor hroot) hfuture hq henv

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
  deployment_reachable_booked_transactionRedemption_enabled_of_reached
    hroot mainnetPragueTimestamp mainnetChainConfig_covered
    (mainnetDeploymentRoot_pragueFloor hroot) hfuture hentry hq henv

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
  deployment_reachable_booked_selfTransactionRedemption_enabled_of_reached
    hroot mainnetPragueTimestamp mainnetChainConfig_covered
    (mainnetDeploymentRoot_pragueFloor hroot) hfuture hentry hq henv

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
  deployment_reachable_booked_transactionRedemption_enabled_of_recoveredSender_of_reached
    hroot mainnetPragueTimestamp mainnetChainConfig_covered
    (mainnetDeploymentRoot_pragueFloor hroot) hfuture hentry hq henv hrecovered

theorem deployment_reachable_future_redeemable_mainnet
    {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig checkpoint future) :
    ∃ history, FutureRedemptionGuarantee
      mainnetChainConfig dp ca u checkpoint future history :=
  deployment_reachable_future_redeemable_of_reached hroot mainnetPragueTimestamp
    mainnetChainConfig_covered (mainnetDeploymentRoot_pragueFloor hroot) hcheckpoint hfuture

theorem deployment_reachable_future_dualSelector_redeemable_mainnet
    {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig checkpoint future) :
    ∃ history, FutureDualSelectorRedemptionGuarantee
      mainnetChainConfig dp ca u checkpoint future history :=
  deployment_reachable_future_dualSelector_redeemable_of_reached
    hroot mainnetPragueTimestamp mainnetChainConfig_covered
    (mainnetDeploymentRoot_pragueFloor hroot) hcheckpoint hfuture

theorem deployment_reachable_future_redeemable_allHolders_mainnet
    {dp : DeployParams} {ca : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig checkpoint future) :
    ∃ history, ∀ u : Adr, FutureRedemptionGuarantee
      mainnetChainConfig dp ca u checkpoint future history :=
  deployment_reachable_future_redeemable_allHolders_of_reached
    hroot mainnetPragueTimestamp mainnetChainConfig_covered
    (mainnetDeploymentRoot_pragueFloor hroot) hcheckpoint hfuture

theorem deployment_fullWindow_future_redeemable_mainnet
    {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future) :
    AllowanceQuiescent ca u deployed.state ∧
      ∃ history, FutureRedemptionGuarantee
        mainnetChainConfig dp ca u deployed future history :=
  deployment_fullWindow_future_redeemable_of_reached hroot mainnetPragueTimestamp
    mainnetChainConfig_covered (mainnetDeploymentRoot_pragueFloor hroot) hfuture

theorem deployment_reachable_dormant_holder_balance_monotone_mainnet
    {dp : DeployParams} {ca u : Adr} {base deployed future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future) :
    ∃ history : AccountedHistory mainnetChainConfig dp ca deployed future,
      NoAllowanceKeyCollision history →
      NoAuthorizingActBy u history →
      bookedBalanceNat deployed.state ca u ≤
        bookedBalanceNat future.state ca u :=
  deployment_reachable_dormant_holder_balance_monotone_of_reached hroot mainnetPragueTimestamp
    mainnetChainConfig_covered (mainnetDeploymentRoot_pragueFloor hroot) hfuture

theorem deployment_reachable_redeemClaims_anyOrder_mainnet
    {rules : ForkRules} {number timestamp : Nat} {dp : DeployParams} {ca : Adr}
    {base deployed future : BlockChain} {cs ds : List RedemptionClaim}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hmodern : mainnetPragueTimestamp ≤ timestamp)
    (hrules : mainnetChainConfig.rulesAt number timestamp = .ok rules)
    (hadm : ClaimsAdmissible rules ca future.state cs)
    (hperm : cs.Perm ds) :
    ∃ post, RedemptionOutcome rules dp ca ds future.state post :=
  deployment_reachable_redeemClaims_anyOrder_of_reached
    hroot hfuture mainnetPragueTimestamp mainnetChainConfig_covered
    (mainnetDeploymentRoot_pragueFloor hroot) hmodern hrules hadm hperm

theorem deployment_reachable_redeemEveryoneList_anyOrder_mainnet
    {rules : ForkRules} {number timestamp : Nat} {dp : DeployParams} {ca : Adr}
    {base deployed future : BlockChain} {holders : List Adr}
    {recipient : Adr → Adr} {claims : List RedemptionClaim}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hmodern : mainnetPragueTimestamp ≤ timestamp)
    (hrules : mainnetChainConfig.rulesAt number timestamp = .ok rules)
    (hnodup : holders.Nodup)
    (hrecipients : ∀ u ∈ holders,
      ClaimAdmissible rules ca future.state
        ⟨u, bookedBalanceNat future.state ca u, recipient u⟩)
    (hperm :
      (fullBalanceClaims ca future.state holders recipient).Perm claims) :
    ∃ post, RedemptionOutcome rules dp ca claims future.state post :=
  deployment_reachable_redeemEveryoneList_anyOrder_of_reached
    hroot hfuture mainnetPragueTimestamp mainnetChainConfig_covered
    (mainnetDeploymentRoot_pragueFloor hroot) hmodern hrules hnodup hrecipients hperm

/-! The schedule-indexed conservation, no-wrap, and determinism pins. -/

end Weth10

end Blanc
