import Blanc.Lift.Usdc.HistoryAnchorCSigningHash
import Blanc.Lift.Usdc.HistoryAnchorBody
import Blanc.Lift.Usdc.ProxyCreation.Transaction
import Blanc.TransactionForward

/-!
# Exact C signer and the original admitted sender

The computed recovery concerns the existing frozen signed transaction. The
cut adapters retain the supplied configured block and its original transaction
trace. Full-body identity remains an explicit obligation; these theorems do
not identify an observed header or prove receipt or execution success.
-/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune Blanc.ExecutionTrace

/-- Kernel-checked recovery of the exact C signature on mainnet chain id 1. -/
theorem c22_recoveredSender :
    recoverSender 1 c22Tx = .ok ProxyCreation.originalCreator := by
  rw [recoverSender, c22_signingHash]
  decide +kernel

/-- The original supplied C cut's admitted sender, using its configured
chain identity and the exact full-body equality. -/
theorem c_original_cut_sender {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post)
    (cut : block.bodyTrace.transactions.TxSplit 22)
    (body : block.block.txs = cBody) (chainId : cfg.chainId = 1) :
    cut.head.sender = ProxyCreation.originalCreator := by
  have stat : cut.benv.stat = (initBenv block.fork pre block.block.header).stat :=
    block.txSplit_stat cut
  have id : cut.benv.beginTransaction.stat.chainId = 1 := calc
    _ = pre.chainId := congrArg BenvStat.chainId stat
    _ = cfg.chainId := (stateTransitionUsing_success_chainId_eq block.transition).symm
    _ = 1 := chainId
  have recovered := checkTransaction_sender cut.head.checked
  rw [id] at recovered
  have original := congrArg (recoverSender 1) (c_original_cut block cut body).2
  rw [c22_recoveredSender] at original
  exact Except.ok.inj (recovered.symm.trans original)

/-- Mainnet supplies chain id 1 through the original successful configured
transition; no additional chain-id or desired-sender premise is needed. -/
theorem c_original_cut_sender_mainnet {F : Fork → Prop} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F mainnetChainConfig pre post)
    (cut : block.bodyTrace.transactions.TxSplit 22)
    (body : block.block.txs = cBody) :
    cut.head.sender = ProxyCreation.originalCreator :=
  c_original_cut_sender block cut body rfl

end Blanc.Lift.Usdc.HistoryAnchorBody
