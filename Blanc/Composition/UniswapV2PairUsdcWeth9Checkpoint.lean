import Blanc.Composition.UniswapV2PairWeth9Checkpoint
import Blanc.Composition.UsdcToken
import Blanc.Composition.PairTokenJointAt
import Blanc.Composition.UsdcNeverSigner

/-!
# The two-token joint checkpoint of the USDC/WETH9 Pair (C6/C7, U8b)

`JointCheckpoint2` (Appendix A §10) is a predicate on one world state: the predecessor's WETH9 joint
checkpoint on side `.one`, USDC's three runtimes installed with its footprint invariant at
`token0`, the Pair's USDC balance row tracked, unflagged and covering `reserve0`, and no tracked
USDC allowance granted by the Pair.  `allowance_control` and `frozen_control` are the C7 statement
controls.

`JointCheckpoint2.toUsdcCore`: the checkpoint, USDC's governance premise F2 and HASH-T over the keys
the history touches give the USDC core's trace-local slot `UsdcHist`, the Pair's answerable balance
row, the joint relation `JointAtW` at the checkpoint and the holder laws for the Pair; the Pair
never signs a USDC entry by `usdc_neverSigner_pair` (its installed code, `pair ≠ usdc` and the
checkpoint's `pairNotPrecompile`).  The booked ledger over the history's key universe is the ledger
over the checkpoint's own keys (`ledger_extend`: a fresh, untracked key reads zero), so the Pair's
booked balance is the balance bits of its word and its booked allowances are its zero allowance
rows.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken

/-- **The two-token joint checkpoint** (C7's predicate on one world): the predecessor's WETH9
joint checkpoint on side `.one`, USDC installed with its footprint invariant at `token0`, the Pair's
USDC balance row tracked, unflagged and covering `reserve0`, and no tracked USDC allowance granted
by the Pair. -/
structure JointCheckpoint2 (pair usdc weth : Adr) (KU : Usdc.Key → Prop) (KW : Weth9.Key → Prop)
    (KP : WriterKey → Prop) (st₀ : UniswapV2Pair.State) (w : Jaune.State) : Prop where
  weth9 : JointCheckpoint pair weth KW KP st₀ .one w
  usdcInstalled : Usdc.UsdcInstalled usdc w
  usdcFoot : Usdc.FootInv KU (w.getStor usdc)
  token0 : st₀.token0 = usdc
  tracked : KU (.bal pair)
  notFrozen : Usdc.frozenBit ((w.getStor usdc).get (Usdc.balSlot pair)) = false
  noAllowance : ∀ g, KU (.allow pair g) → (w.getStor usdc).get (Usdc.allowSlot pair g) = 0
  reserve : st₀.reserve0.val ≤ Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot pair))
  apart : pair ≠ usdc
  usdcNotPrecompile : ∀ s : BenvStat, CoveredFork s.fork → ¬ s.rules.isPrecomp usdc
  pairNotPrecompile : ∀ s : BenvStat, CoveredFork s.fork → ¬ s.rules.isPrecomp pair

/-- **C7 controls**: a tracked nonzero USDC allowance row of the Pair, or a flagged Pair balance
word, fails the predicate. -/
theorem JointCheckpoint2.allowance_control {pair usdc weth : Adr} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State} {w : Jaune.State}
    {g : Adr} (row : KU (.allow pair g)) (granted : (w.getStor usdc).get (Usdc.allowSlot pair g) ≠ 0) :
    ¬ JointCheckpoint2 pair usdc weth KU KW KP st₀ w := fun h => granted (h.noAllowance g row)

theorem JointCheckpoint2.frozen_control {pair usdc weth : Adr} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State} {w : Jaune.State}
    (flag : Usdc.frozenBit ((w.getStor usdc).get (Usdc.balSlot pair)) = true) :
    ¬ JointCheckpoint2 pair usdc weth KU KW KP st₀ w := fun h => by
  rw [h.notFrozen] at flag
  cases flag

/-- The checkpoint and the trace-local premises supply USDC's core slot, the Pair's answerable row,
the joint relation and the holder laws (from the signature laws and `usdc_neverSigner_pair`). -/
theorem JointCheckpoint2.toUsdcCore {pair usdc weth : Adr} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (h : JointCheckpoint2 pair usdc weth KU KW KP st₀ checkpoint.state)
    (governance : Usdc.UsdcGovernance usdc trace)
    (fresh : Usdc.KeysFresh KU (Usdc.historyTouchedKeys usdc trace)) :
    (usdcCore usdc KU).Hist trace ∧ (usdcCore usdc KU).Answerable trace pair ∧
      JointAtW (usdcCore usdc KU) trace pair .zero st₀ checkpoint.state ∧
      HolderLaws usdc (Usdc.usdcBookS usdc).toBook trace pair := by
  have hist : Usdc.UsdcHist usdc KU trace := ⟨h.usdcInstalled, governance, h.usdcFoot, fresh⟩
  refine ⟨hist, Or.inl h.tracked, ⟨?_, ?_⟩, (Usdc.usdcBook_lawsS usdc).holderLaws usdc
    (usdc_neverSigner_pair trace hist h.weth9.pairCode h.apart h.pairNotPrecompile)⟩
  · change st₀.reserve0.val ≤
      (Usdc.ledger (Usdc.historyKeyUniverse usdc trace KU) (checkpoint.state.getStor usdc)).bal pair
    rw [Usdc.historyKeyUniverse, Usdc.ledger_extend h.usdcFoot.support fresh,
      Usdc.ledger_bal h.tracked]
    exact h.reserve
  · intro g
    change (Usdc.ledger (Usdc.historyKeyUniverse usdc trace KU)
      (checkpoint.state.getStor usdc)).allow pair g = 0
    rw [Usdc.historyKeyUniverse, Usdc.ledger_extend h.usdcFoot.support fresh]
    by_cases row : KU (.allow pair g)
    · rw [Usdc.ledger_allow row, h.noAllowance g row]
      rfl
    · change (SlotFootprint.trackedWord Usdc.Key.slot KU (checkpoint.state.getStor usdc)
        (.allow pair g)).toNat = 0
      rw [SlotFootprint.trackedWord_of_not row]
      rfl

end Blanc.Composition.UniswapV2PairUsdcWeth9
