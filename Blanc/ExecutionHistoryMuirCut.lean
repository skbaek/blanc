import Blanc.ExecutionMidHistoryIn
import Blanc.ExecutionIndexedReceipts

/-!
# A transaction cut of a retained Muir Glacier block

A retained configured block whose header selects Muir Glacier gives each of its transaction cuts
Muir rules, no base fee, and the header's timestamp. Contract-neutral; the recorded historical
transactions read their fork, price and clock from here.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- **The cut's environment under a Muir Glacier selection.** -/
theorem ConfiguredBlockTraceIn.txSplit_muir {F : Fork → Prop} {cfg : ChainConfig}
    {pre D : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre D)
    (selected : cfg.forkAt block.block.header.number block.block.header.timestamp =
      .ok .muirGlacier) {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i) :
    block.fork = .muirGlacier ∧ cut.benv.stat.fork = .muirGlacier ∧
      cut.benv.stat.baseFeePerGas = 0 ∧
      cut.benv.stat.time = block.block.header.timestamp.toB256 := by
  have forkEq : block.fork = .muirGlacier := Except.ok.inj (block.forkAt.symm.trans selected)
  have stat : cut.benv.stat = (initBenv block.fork pre block.block.header).stat :=
    block.txSplit_stat cut
  have forkAtCut : cut.benv.stat.fork = .muirGlacier := by rw [stat]; exact forkEq
  have last : D.blocks.getLast? = some block.block :=
    (congrArg (fun chain : BlockChain => chain.blocks.getLast?) block.postEq).trans
      (appendBlock_getLast? _ _)
  obtain ⟨selectedFork, lookup, shape⟩ := stateTransitionUsing_shapeCoherent block.transition _ last
  have shapeFork : selectedFork = .muirGlacier := Except.ok.inj (lookup.symm.trans selected)
  have absent : block.block.header.baseFeePerGas = none := by
    have present := checkHeaderShape_baseFee shape
    rw [shapeFork] at present
    change block.block.header.baseFeePerGas.isSome = false at present
    exact Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp present)
  have baseFee : cut.benv.stat.baseFeePerGas = 0 := by
    rw [stat]
    change block.block.header.baseFeePerGas.getD 0 = 0
    rw [absent]
    rfl
  exact ⟨forkEq, forkAtCut, baseFee, by rw [stat]; rfl⟩

end Blanc.ExecutionTrace
