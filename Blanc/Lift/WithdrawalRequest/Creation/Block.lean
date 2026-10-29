import Blanc.Lift.WithdrawalRequest.Creation.Transaction
import Blanc.ExecutionMidHistoryIn

/-!
# Canonical deployment at an actual transaction cut

A deployment witness names one position in the decoded transaction fold of a retained
configured Cancun block. Its cut retains that transaction's preparation, execution and
committed state, together with the prefix and suffix of the same block. No initialized
storage or installed code is a witness field. The producer derives those facts exactly
at `cut.afterBenv`, the start of `MidHistoryTraceIn.tail block cut`.
-/

namespace Blanc.Lift.WithdrawalRequest.Creation

open Jaune Blanc.ExecutionTrace Blanc.WithdrawalRequest

/-- Input-only identification of canonical EIP-7002 deployment inside this retained block.
`position` is the decoded transaction position, and `cut.head` is its actual transaction
trace. `transaction_identity` relates the retained transaction index and decoded value to
that position. Constructor success and the committed code/storage are derived by `initial`. -/
structure DeploymentCut
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) where
  position : Nat
  cut : block.bodyTrace.transactions.TxSplit position
  input : CanonicalDeploymentInput cut.head.msg
  fork : block.fork = .cancun

/-- The witness's selected transaction really occupies its stated position in the block's
actual decoded transaction list; its retained transaction index is that same position. -/
theorem DeploymentCut.transaction_identity
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    {block : ConfiguredBlockTraceIn F cfg pre post} (deployment : DeploymentCut block) :
    deployment.cut.index = deployment.position ∧
      block.bodyTrace.decodedTxs[deployment.position]? = some deployment.cut.tx :=
  deployment.cut.putIndex_eq

/-- Canonical runtime and inhibitor initialization at this block's actual committed
post-deployment transaction boundary. The same boundary starts the deployment-block suffix
`MidHistoryTraceIn.tail block deployment.cut`; no unrelated checkpoint is substituted. -/
theorem DeploymentCut.initial
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    {block : ConfiguredBlockTraceIn F cfg pre post} (deployment : DeploymentCut block) :
    deployment.cut.afterBenv.state.getCode withdrawalRequestPredeployAddress =
        Blanc.withdrawalRequestCode ∧
      RepresentsStorage
        (deployment.cut.afterBenv.state.getStor withdrawalRequestPredeployAddress).get initial := by
  have hselected := congrArg BenvStat.fork (block.txSplit_stat deployment.cut)
  change deployment.cut.benv.stat.fork = block.fork at hselected
  have hfork : deployment.cut.benv.stat.fork = .cancun := hselected.trans deployment.fork
  exact transaction_initial_cancun deployment.cut.head deployment.input hfork

end Blanc.Lift.WithdrawalRequest.Creation
