-- DripHistory.lean : configured-chain storage conservation for DRIP.

import Blanc.DripSound

namespace Blanc

open Jaune

namespace Drip

/-- The actual deployment root packages the installed runtime and full storage
accounting as the generic ladder's state invariant. -/
theorem DeploymentRoot.stateInv
    (root : DeploymentRoot cfg base deployed ca) :
    dripSpec.StateInv ca deployed.state := by
  refine ⟨?_, trivial, root.accountingInv⟩
  change some (deployed.state.getCode ca).toList = Prog.compile runtime
  rw [root.installed, ByteArray.toList_eq_toList_data, code_compile]

/-- Every genuine configured continuation preserves the DRIP storage invariant.
`ReachUsing` retains its validated configuration/context base and every step's
global balance-plus-withdrawal no-wrap bound and exact configured transition. -/
theorem DeploymentRoot.reachable_stateInv
    (root : DeploymentRoot cfg base deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed future)
    (hcov : ∀ timestamp fork,
      cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    dripSpec.StateInv ca future.state :=
  dripSpec.chainUsing_preserves_inv ca (dripSpec_preserves ca)
    cfg deployed future reach root.stateInv hcov

/-- The storage projection of configured DRIP continuation preservation. -/
theorem DeploymentRoot.reachable_accountingInv
    (root : DeploymentRoot cfg base deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed future)
    (hcov : ∀ timestamp fork,
      cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    AccountingInv (future.state.getStor ca) :=
  (root.reachable_stateInv reach hcov).inv

end Drip

end Blanc
