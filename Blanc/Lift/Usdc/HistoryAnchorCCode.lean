import Blanc.Lift.Usdc.HistoryAnchorBody
import Blanc.Lift.Usdc.ProxyCreation.ForeignCode

/-!
# Existing implementation code at the original C22 cut

The frozen full-body identity selects the registered constructor within the
supplied actual block. Its clean execution preserves the initial implementation
account's nonempty prestate code through complete transaction settlement.
The equality ends at the transaction cut, before the remaining C transactions.
It neither supplies nor adopts an observation identifying that code with V1.
-/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune Blanc.ExecutionTrace

/-- At the original supplied C22 cut, the initial implementation keeps its
existing code. Full-body identity, actual success and pre-cut nonemptiness
remain explicit internal conditions; no desired post-cut code is assumed. -/
theorem c_original_cut_initialImplementation_code
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post)
    (cut : block.bodyTrace.transactions.TxSplit 22)
    (body : block.block.txs = cBody)
    (hsg : block.fork.ruleSet.stateGas = none)
    (clean : cut.head.messageOut.error = none)
    (nonempty :
      (cut.benv.state.getCode ProxyCreation.initialImplementation.toAdr).toList ≠ []) :
    cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr =
      cut.benv.state.getCode ProxyCreation.initialImplementation.toAdr := by
  obtain ⟨_, _, receiver, value, input, _⟩ := c_original_cut_fields block cut body
  have headSg : cut.benv.stat.rules.stateGas = none := by
    change cut.afterBenv.stat.rules.stateGas = none
    rw [block.txSplit_stat cut]
    exact hsg
  exact ProxyCreation.constructor_foreign_code_of_transactionTrace cut.head headSg
    receiver input value clean nonempty

end Blanc.Lift.Usdc.HistoryAnchorBody
