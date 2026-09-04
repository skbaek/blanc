import Blanc.BeaconDepositHistoryChain

/-!
Ethereum-mainnet specializations of the schedule-parametric BeaconDeposit
deployment root and its configured history rungs.

This is the only BeaconDeposit proof module that names mainnet's configured
fork schedule.  The generic deployment, transaction, block, and history results
remain independent of named forks; each declaration below deliberately
specializes an already-audited generic theorem rather than replaying its proof.

Rule-local arguments stay explicit.  A caller instantiates `rules` with the
record `mainnetChainConfig.rulesAt` actually selects at the creation block's
timestamp, and the envelope's own `rulesAt` field is what ties the two
together.  No lane witness is added here: these are statements over mainnet's
configured schedule, not executable evidence that a mainnet block was run.
-/

namespace Blanc

open Jaune

namespace BeaconDeposit

/-- Current-mainnet specialization of the schedule-parametric deployment
root. -/
abbrev MainnetDeploymentRoot (base deployed : BlockChain) (ca : Adr) : Prop :=
  DeploymentRoot mainnetChainConfig base deployed ca

/-- A successful configured step on mainnet's schedule establishes the
current-mainnet deployment root. -/
theorem canonicalDeploymentStep_establishes_root_mainnet
    (rules : ForkRules) (base deployed : BlockChain)
    (cb : CanonicalBlock) (txBytes : Bytes)
    (tx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase mainnetChainConfig rules base sender ca)
    (henv : CanonicalBeaconDepositDeploymentBlock mainnetChainConfig rules
      base cb txBytes tx sender ca)
    (hstep : stateTransitionUsing mainnetChainConfig
      base cb.block = .ok deployed) :
    MainnetDeploymentRoot base deployed ca :=
  canonicalDeploymentStep_establishes_root mainnetChainConfig rules base
    deployed cb txBytes tx sender ca hbase henv hstep

/-- Current-mainnet instance of the retained constructor-occurrence
projection. -/
theorem DeploymentRoot.constructorOccurrence_mainnet
    {base deployed : BlockChain} {ca : Adr}
    (hroot : MainnetDeploymentRoot base deployed ca) :
    ∃ (rules : ForkRules) (cb : CanonicalBlock) (txBytes : Bytes) (tx : Tx)
      (sender : Adr)
      (ctx : PreparedDeploymentContext mainnetChainConfig rules base cb tx
        sender ca)
      (post : State) (bout : BlockOutput) (messagePost : State)
      (out : MsgCallOutput) (createPost : Devm),
      CanonicalBeaconDepositDeploymentBlock mainnetChainConfig rules base cb
        txBytes tx sender ca ∧
      stateTransitionUsing mainnetChainConfig base cb.block = .ok deployed ∧
      DeploymentTransactionResult mainnetChainConfig rules ca ctx post bout ∧
      DirectConstructorMessageResult ca ctx.msg messagePost out ∧
      DirectCreateMessageResult ca ctx.msg createPost ∧
      DirectCreateMessageExecution ca ctx.msg createPost :=
  hroot.constructorOccurrence

/-- Current-mainnet instance of the deployment-rooted history rung. -/
theorem DeploymentRoot.future_history_extends_mainnet
    {base deployed future : BlockChain} {ca : Adr}
    (root : MainnetDeploymentRoot base deployed ca)
    (reach : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (native : ReachNativeShaAdmitted reach ca) :
    ∃ suffix, ArtifactInv (future.state.getStor ca) suffix :=
  root.future_history_extends reach native

/-- Current-mainnet instance of the deployment-rooted count/root headline. -/
theorem DeploymentRoot.future_count_root_mainnet
    {base deployed future : BlockChain} {ca : Adr}
    (root : MainnetDeploymentRoot base deployed ca)
    (reach : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (native : ReachNativeShaAdmitted reach ca) :
    ∃ suffix,
      ArtifactInv (future.state.getStor ca) suffix ∧
      ((future.state.getStor ca).get depositCountSlot).toNat =
        suffix.length ∧
      (0 < ((future.state.getStor ca).get depositCountSlot).toNat ↔
        suffix ≠ []) ∧
      Acc.root Bytes.sha256 (accOfStor (future.state.getStor ca)) =
        mixedRootOf Bytes.sha256 suffix :=
  root.future_count_root reach native

end BeaconDeposit

end Blanc
