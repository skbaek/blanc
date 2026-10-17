import Blanc.Composition.PairTokenShareValue
import Blanc.Composition.UniswapV2PairWeth9Joint

/-!
# C4(a) for WETH9 (Appendix A §8 as amended by A4/A10/A11/A14)

`pair_weth9_history_feeOff_product` / `pair_weth9_history_feeOn_product`: the generic C4(a) rows
(`pair_token_feeOff_product` / `pair_token_feeOn_product`) at the WETH9 core, for WETH9 on either
`side`.  The token hypotheses are discharged exactly as `pair_weth9_joint` discharges C3's:
`weth9Core`, `weth9Book_laws`, `weth9Book_erc20Abi`, `weth9SelfCaller`; `hist`, `answerable` and the
joint relation from `JointCheckpoint.toCore`; `distinct`, `notSystem` from the checkpoint; H1 from
the factory lift (`pair_history_factoryQuiet`); `tokenEntered` from `weth9_tokenEntered`.

Premises: the joint checkpoint, both HASH-T premises and the two factory premises.  No premise
mentions WETH9's answers (the C4 statement-pin control): the WETH9 half of the per-side answer
condition is a theorem, and only the other token's half stays as the conclusion's antecedent.
-/

namespace Blanc.Composition.UniswapV2PairWeth9ShareValue

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token
  Blanc.Lift.UniswapV2Pair Blanc.Composition.Weth9Token Blanc.Composition.PairTokenJoint
  Blanc.Composition.PairTokenShareValue Blanc.Composition.UniswapV2PairWeth9Joint

/-- **C4(a) for WETH9, fee off** (either side): every V2 pair whose `side` token is WETH9, from the
joint checkpoint, with only the other token's half kept.  No hypothesis mentions WETH9's answers. -/
theorem pair_weth9_history_feeOff_product {pair weth : Adr} (side : TokenSide)
    {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ side checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayAnswersSide side.other st₀ (steps.map PairStep.source) →
          ∀ before after, (before, after) ∈ sourceReplayEdges st₀ (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
              after.reserve0.val * after.reserve1.val * before.totalSupply.toNat ^ 2) := by
  obtain ⟨hist, answerable, start⟩ := JointCheckpoint.toCore trace joint wethFresh
  exact pair_token_feeOff_product (weth9Core weth K₀) weth9Book_laws weth9Book_erc20Abi
    (weth9SelfCaller weth K₀) side trace joint.pairCode joint.pairRep pairFresh hist joint.token
    joint.unlocked joint.apart answerable joint.distinct joint.notSystem
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.pairCode factoryInstalled
      joint.pairNonzero factoryNotSystem)
    (weth9_tokenEntered trace joint) start

/-- **C4(a) for WETH9, fee on** (either side). -/
theorem pair_weth9_history_feeOn_product {pair weth : Adr} (side : TokenSide)
    {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ side checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumes st₀ steps finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayNoShrinkSide side.other st₀ (steps.map PairStep.source) →
          ∀ before inv after, (before, inv, after) ∈ sourceReplaySteps st₀ (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
              after.reserve0.val * after.reserve1.val *
                (before.totalSupply.toNat + entryFeeAmount before inv.entry inv.transcript) ^ 2) := by
  obtain ⟨hist, answerable, start⟩ := JointCheckpoint.toCore trace joint wethFresh
  exact pair_token_feeOn_product (weth9Core weth K₀) weth9Book_laws weth9Book_erc20Abi
    (weth9SelfCaller weth K₀) side trace joint.pairCode joint.pairRep pairFresh hist joint.token
    joint.unlocked joint.apart answerable joint.distinct joint.notSystem
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.pairCode factoryInstalled
      joint.pairNonzero factoryNotSystem)
    (weth9_tokenEntered trace joint) start

end Blanc.Composition.UniswapV2PairWeth9ShareValue
