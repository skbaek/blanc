import Blanc.BeaconDepositHistoryChain

/-!
Prague-only compatibility corollaries of the schedule-parametric BeaconDeposit
deployment root and history rungs.

Every declaration below is the `ChainConfig.pragueOnly` instance of an
already-audited generic theorem.  They exist so the fixed-Prague API this
contract published before its configured migration survives unchanged in
meaning; they say nothing that the generic statements do not already say.
-/

namespace Blanc

open Jaune

namespace BeaconDeposit

/-- Prague-only specialization of the schedule-parametric deployment root:
the fixed-fork API this contract published before its configured migration. -/
abbrev PragueDeploymentRoot
    (chainId : UInt64) (base deployed : BlockChain) (ca : Adr) : Prop :=
  DeploymentRoot (ChainConfig.pragueOnly chainId) base deployed ca

/-- A successful configured Prague-only step over the strict singleton,
zero-value type-2 envelope establishes the Prague-only deployment root. -/
theorem canonicalDeploymentStep_establishes_root_prague
    (chainId : UInt64) (base deployed : BlockChain)
    (cb : CanonicalBlock) (txBytes : Bytes)
    (tx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase (ChainConfig.pragueOnly chainId)
      pragueRules base sender ca)
    (henv : CanonicalBeaconDepositDeploymentBlock
      (ChainConfig.pragueOnly chainId) pragueRules base cb
      txBytes tx sender ca)
    (hstep : stateTransitionUsing (ChainConfig.pragueOnly chainId)
      base cb.block = .ok deployed) :
    PragueDeploymentRoot chainId base deployed ca :=
  canonicalDeploymentStep_establishes_root (ChainConfig.pragueOnly chainId)
    pragueRules base deployed cb txBytes tx sender ca hbase henv hstep

/-- Prague-only instance of the retained constructor-occurrence projection. -/
theorem DeploymentRoot.constructorOccurrence_prague
    {chainId : UInt64} {base deployed : BlockChain} {ca : Adr}
    (hroot : PragueDeploymentRoot chainId base deployed ca) :
    ∃ (rules : ForkRules) (cb : CanonicalBlock) (txBytes : Bytes) (tx : Tx)
      (sender : Adr)
      (ctx : PreparedDeploymentContext (ChainConfig.pragueOnly chainId) rules
        base cb tx sender ca)
      (post : State) (bout : BlockOutput) (messagePost : State)
      (out : MsgCallOutput) (createPost : Devm),
      CanonicalBeaconDepositDeploymentBlock (ChainConfig.pragueOnly chainId)
        rules base cb txBytes tx sender ca ∧
      stateTransitionUsing (ChainConfig.pragueOnly chainId)
        base cb.block = .ok deployed ∧
      DeploymentTransactionResult (ChainConfig.pragueOnly chainId) rules ca
        ctx post bout ∧
      DirectConstructorMessageResult ca ctx.msg messagePost out ∧
      DirectCreateMessageResult ca ctx.msg createPost ∧
      DirectCreateMessageExecution ca ctx.msg createPost :=
  hroot.constructorOccurrence

/-- Prague-only instance of the deployment-rooted history rung. -/
theorem DeploymentRoot.future_history_extends_prague
    {chainId : UInt64} {base deployed future : BlockChain} {ca : Adr}
    (root : PragueDeploymentRoot chainId base deployed ca)
    (reach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future)
    (native : ReachNativeShaAdmitted reach ca) :
    ∃ suffix, ArtifactInv (future.state.getStor ca) suffix :=
  root.future_history_extends reach native

/-- Prague-only instance of the deployment-rooted count/root headline. -/
theorem DeploymentRoot.future_count_root_prague
    {chainId : UInt64} {base deployed future : BlockChain} {ca : Adr}
    (root : PragueDeploymentRoot chainId base deployed ca)
    (reach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future)
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
