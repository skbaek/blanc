import Blanc.Composition.UniswapV2PairWeth9SigningData
import Blanc.Lift.Weth9.ClosedBlock

/-!
# The closed instance's configured BPO2 block

The block of the closed instance (goal C6(b)) reuses the configured chain envelope of the WETH9
closed witness (`Weth9.ClosedInstance`): the BPO2-from-genesis `config`, the checkpoint
`checkpoint st` carrying the supplied state `st` unchanged and committing to its root, and the
execution header template.  Its body is the two signed transactions `signedTx1`, `signedTx2`.  The
header's post-execution commitments (state root, gas used, receipts, requests) are those of the
supplied body result `(post, bout)`, so the block is a parameter of them.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.BlockForward Blanc.ExecutionTrace
open Blanc.Lift.Weth9.ClosedInstance (config config_forkAt checkpoint checkpointBlock
  executionHeader input depositBlock depositBlock_header depositBlock_input)

/-- The block body: `tx1`, then `tx2`. -/
def swapTxs : List (Bytes ⊕ Tx) := [.inr signedTx1, .inr signedTx2]

/-- **The closed instance's block** after `checkpoint st`, committing to the body result
`(post, bout)`. -/
def swapBlock (st post : Jaune.State) (bout : BlockOutput) : Block :=
  { header := commitHeader Fork.bpo2.ruleSet (checkpointBlock st) (executionHeader st) post bout
    txs := swapTxs
    wds := []
    ommers := [] }

/-- The chain after the block. -/
def swapChain (st post : Jaune.State) (bout : BlockOutput) : BlockChain :=
  ⟨appendBlock (checkpoint st).blocks (swapBlock st post bout), post, 1⟩

theorem swapBlock_input (st post : Jaune.State) (bout : BlockOutput) :
    initBenv .bpo2 (checkpoint st) (swapBlock st post bout).header = input st :=
  depositBlock_input st post bout

/-- **The block's state transition** succeeds from any successful body run within the gas limit. -/
theorem swapBlock_transition {st post : Jaune.State} {bout : BlockOutput}
    (hgas : bout.blockGasUsed ≤ 1000000)
    (hbody : applyBody (input st) swapTxs [] = .ok (post, bout)) :
    stateTransitionUsing config (checkpoint st) (swapBlock st post bout) =
      .ok (swapChain st post bout) := by
  have hbody' : applyBody
      (initBenv .bpo2 (checkpoint st) (swapBlock st post bout).header)
      (swapBlock st post bout).txs (swapBlock st post bout).wds = .ok (post, bout) := by
    rw [swapBlock_input]
    exact hbody
  exact stateTransitionUsing_forward rfl (config_forkAt _) CoveredFork.bpo2
    (depositBlock_header (post := post) hgas) rfl hbody' rfl rfl rfl rfl rfl rfl rfl rfl

end Blanc.Composition.UniswapV2PairWeth9Instance
