import Blanc.Composition.UniswapV2PairUsdcWeth9Checkpoint
import Blanc.Composition.UsdcTokenF
import Blanc.Lift.UniswapV2Pair.StaticSilent

/-!
# The support-free two-token joint checkpoint of the USDC/WETH9 Pair

`JointCheckpoint2F` is `JointCheckpoint2` (`UniswapV2PairUsdcWeth9Checkpoint.lean`)
with `usdcFoot : Usdc.FootInv KU …` replaced by `usdcFoot : Usdc.FootCoreL KU …`;
every other field stays verbatim.  `PairUsdcAllowQuiet` is the trace-local allowance
premise the support-free bridge needs in place of support: every touched allowance row
of the Pair reads zero at the checkpoint.  `JointCheckpoint2.allowQuiet` derives it
from the full checkpoint's support together with `noAllowance`, and
`JointCheckpoint2F.toUsdcCoreF` is the twin of `toUsdcCore` taking it as an extra
premise (`quiet` in place of support; `.bal pair` is tracked, so `Usdc.ledger_bal`
replaces `Usdc.ledger_extend` on the reserve leg).
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken

/-- **The Pair's touched USDC allowance rows read zero at the checkpoint.** -/
def PairUsdcAllowQuiet (pair usdc : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  ∀ g, (.allow pair g) ∈ Usdc.historyTouchedKeys usdc trace →
    (checkpoint.state.getStor usdc).get (Usdc.allowSlot pair g) = 0

/-- **The support-free two-token joint checkpoint**: `JointCheckpoint2` with the
support-free footprint at `token0`. -/
structure JointCheckpoint2F (pair usdc weth : Adr) (KU : Usdc.Key → Prop) (KW : Weth9.Key → Prop)
    (KP : WriterKey → Prop) (st₀ : UniswapV2Pair.State) (w : Jaune.State) : Prop where
  weth9 : JointCheckpoint pair weth KW KP st₀ .one w
  usdcInstalled : Usdc.UsdcInstalled usdc w
  usdcFoot : Usdc.FootCoreL KU (w.getStor usdc)
  token0 : st₀.token0 = usdc
  tracked : KU (.bal pair)
  notFrozen : Usdc.frozenBit ((w.getStor usdc).get (Usdc.balSlot pair)) = false
  noAllowance : ∀ g, KU (.allow pair g) → (w.getStor usdc).get (Usdc.allowSlot pair g) = 0
  reserve : st₀.reserve0.val ≤ Usdc.balanceBits ((w.getStor usdc).get (Usdc.balSlot pair))
  apart : pair ≠ usdc
  usdcNotPrecompile : ∀ s : BenvStat, CoveredFork s.fork → ¬ s.rules.isPrecomp usdc
  pairNotPrecompile : ∀ s : BenvStat, CoveredFork s.fork → ¬ s.rules.isPrecomp pair

/-- Every full joint checkpoint is a support-free one: the twin proof reads only
`inj`/`apart`/`good` of the checkpoint `FootInv`. -/
theorem JointCheckpoint2.toF {pair usdc weth : Adr} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    {w : Jaune.State} (h : JointCheckpoint2 pair usdc weth KU KW KP st₀ w) :
    JointCheckpoint2F pair usdc weth KU KW KP st₀ w :=
  ⟨h.weth9, h.usdcInstalled, ⟨h.usdcFoot.inj, h.usdcFoot.apart, h.usdcFoot.good⟩,
    h.token0, h.tracked, h.notFrozen, h.noAllowance, h.reserve, h.apart,
    h.usdcNotPrecompile, h.pairNotPrecompile⟩

/-- **The full checkpoint's support and `noAllowance` give the quiet premise**: a
touched allowance row is tracked (then `noAllowance` applies) or fresh (then support
reads zero at its slot). -/
theorem JointCheckpoint2.allowQuiet {pair usdc weth : Adr} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {trace : ConfiguredHistoryTrace cfg checkpoint future}
    (h : JointCheckpoint2 pair usdc weth KU KW KP st₀ checkpoint.state)
    (fresh : Usdc.KeysFresh KU (Usdc.historyTouchedKeys usdc trace)) :
    PairUsdcAllowQuiet pair usdc trace := by
  intro g hmem
  by_cases row : KU (.allow pair g)
  · exact h.noAllowance g row
  · exact h.usdcFoot.support.get_eq_zero (fresh.1 _ hmem) row

/-- **C7 controls, support-free**: a tracked nonzero USDC allowance row of the Pair, or a
flagged Pair balance word, fails the predicate. -/
theorem JointCheckpoint2F.allowance_control {pair usdc weth : Adr} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State} {w : Jaune.State}
    {g : Adr} (row : KU (.allow pair g)) (granted : (w.getStor usdc).get (Usdc.allowSlot pair g) ≠ 0) :
    ¬ JointCheckpoint2F pair usdc weth KU KW KP st₀ w := fun h => granted (h.noAllowance g row)

theorem JointCheckpoint2F.frozen_control {pair usdc weth : Adr} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State} {w : Jaune.State}
    (flag : Usdc.frozenBit ((w.getStor usdc).get (Usdc.balSlot pair)) = true) :
    ¬ JointCheckpoint2F pair usdc weth KU KW KP st₀ w := fun h => by
  rw [h.notFrozen] at flag
  cases flag

/-- The support-free checkpoint and the trace-local premises supply USDC's support-free
core slot, the Pair's answerable row, the joint relation and the holder laws (twin of
`JointCheckpoint2.toUsdcCore`; the Pair never signs by `Usdc.usdc_neverSigner_pairCode` at
`pairSem`, from the support-free `UsdcHistF`). -/
theorem JointCheckpoint2F.toUsdcCoreF {pair usdc weth : Adr} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (h : JointCheckpoint2F pair usdc weth KU KW KP st₀ checkpoint.state)
    (governance : Usdc.UsdcGovernance usdc trace)
    (quiet : PairUsdcAllowQuiet pair usdc trace)
    (fresh : Usdc.KeysFresh KU (Usdc.historyTouchedKeys usdc trace)) :
    (usdcCoreF usdc KU).Hist trace ∧ (usdcCoreF usdc KU).Answerable trace pair ∧
      JointAtW (usdcCoreF usdc KU) trace pair .zero st₀ checkpoint.state ∧
      HolderLaws usdc (Usdc.usdcBookS usdc).toBook trace pair := by
  have hist : Usdc.UsdcHistF usdc KU trace := ⟨h.usdcInstalled, governance, h.usdcFoot, fresh⟩
  refine ⟨hist, Or.inl h.tracked, ⟨?_, ?_⟩, (Usdc.usdcBook_lawsS usdc).holderLaws usdc
    (Usdc.usdc_neverSigner_pairCode trace hist rfl h.weth9.pairCode h.pairNotPrecompile
      not_staticAnswered_pair)⟩
  · change st₀.reserve0.val ≤
      (Usdc.ledger (Usdc.historyKeyUniverse usdc trace KU) (checkpoint.state.getStor usdc)).bal pair
    rw [Usdc.historyKeyUniverse, Usdc.ledger_bal (Or.inl h.tracked)]
    exact h.reserve
  · intro g
    change (Usdc.ledger (Usdc.historyKeyUniverse usdc trace KU)
      (checkpoint.state.getStor usdc)).allow pair g = 0
    rw [Usdc.historyKeyUniverse]
    by_cases row : KU (.allow pair g)
    · rw [Usdc.ledger_allow (Or.inl row), h.noAllowance g row]
      rfl
    · by_cases mem : Usdc.Key.allow pair g ∈ Usdc.historyTouchedKeys usdc trace
      · rw [Usdc.ledger_allow (Or.inr mem), quiet g mem]
        rfl
      · have hnot : ¬ SlotFootprint.extendBy KU (Usdc.historyTouchedKeys usdc trace)
            (.allow pair g) :=
          fun hh => hh.elim row mem
        change (SlotFootprint.trackedWord Usdc.Key.slot
          (SlotFootprint.extendBy KU (Usdc.historyTouchedKeys usdc trace))
          (checkpoint.state.getStor usdc) (.allow pair g)).toNat = 0
        rw [SlotFootprint.trackedWord_of_not hnot]
        rfl

end Blanc.Composition.UniswapV2PairUsdcWeth9
