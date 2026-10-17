import Blanc.Composition.UniswapV2PairWeth9Checkpoint
import Blanc.Composition.Weth9TokenCore
import Blanc.Composition.PairTokenJointAt

/-!
# The joint checkpoint feeds the WETH9 token core

`JointCheckpoint.toCore` (Appendix A §7): a world satisfying the joint checkpoint, together with
WETH9's trace-local hash freshness over the history (HASH-T), gives the WETH9 core's trace-local
slot `Weth9Hist`, the Pair's answerable balance row, and the joint relation `JointAt` at the
checkpoint.  The booked ledger over the history's key universe is the ledger over the checkpoint's
own keys (`ledger_extend`: a fresh, untracked key reads zero), so the booked balance of the Pair is
its balance word and its booked allowances are its zero allowance rows.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token
  Blanc.Lift.UniswapV2Pair Blanc.Composition.Weth9Token Blanc.Composition.PairTokenJoint

/-- The joint checkpoint supplies the core's trace-local slot (with WETH9's HASH-T freshness), the
Pair's answerable row and the joint relation at the checkpoint. -/
theorem JointCheckpoint.toCore {pair weth : Adr} {K₀ : Key → Prop} {KP : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State} {side : TokenSide} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (h : JointCheckpoint pair weth K₀ KP st₀ side checkpoint.state)
    (fresh : KeysFresh K₀ (historyTouchedKeys weth trace)) :
    (weth9Core weth K₀).Hist trace ∧ (weth9Core weth K₀).Answerable trace pair ∧
      JointAt (weth9Core weth K₀) trace pair side st₀ checkpoint.state := by
  refine ⟨⟨h.wethCode, h.sumNof, h.wethFoot, fresh⟩, Or.inl h.tracked, ?_, ?_⟩
  · change st₀.reserveOn side ≤
      ((ledger (historyKeyUniverse weth trace K₀) (checkpoint.state.getStor weth)).bal pair).toNat
    rw [historyKeyUniverse, ledger_extend h.wethFoot fresh]
    change st₀.reserveOn side ≤ (Weth9.tracked K₀ (checkpoint.state.getStor weth) pair).toNat
    rw [tracked_self h.tracked]
    exact h.reserve
  · intro g
    change ((ledger (historyKeyUniverse weth trace K₀) (checkpoint.state.getStor weth)).allow
      pair g).toNat = 0
    rw [historyKeyUniverse, ledger_extend h.wethFoot fresh]
    change (trackedAllow K₀ (checkpoint.state.getStor weth) pair g).toNat = 0
    by_cases row : K₀ (.allow pair g)
    · rw [trackedAllow_self row, h.noAllowance g row]
      rfl
    · rw [trackedAllow_of_not row]
      rfl

end Blanc.Composition.UniswapV2PairWeth9Joint
