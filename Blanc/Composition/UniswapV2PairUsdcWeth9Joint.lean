import Blanc.Composition.PairTwoToken
import Blanc.Composition.UniswapV2PairUsdcWeth9Checkpoint
import Blanc.Composition.UniswapV2PairUsdcWeth9JointF
import Blanc.Composition.UniswapV2PairWeth9Joint
import Blanc.MachineDataFacts

/-!
# C6(a) for the USDC/WETH9 Pair (Appendix A §10, U8b)

The headline is a corollary of its support-free twin `pair_usdc_weth9_joint_finite`
(`UniswapV2PairUsdcWeth9JointF.lean`), which instantiates the generic two-core headline
`pair_two_token_joint` at `C0 := usdcCoreF`, `C1 := (weth9Core weth KW).weak`: the checkpoint gives
`JointCheckpoint2F` (`JointCheckpoint2.toF`) and the trace-local premise `PairUsdcAllowQuiet`
(`JointCheckpoint2.allowQuiet`, from the storage-wide support).

The generic `JointAtW` conclusions are read back as the concrete ledger forms at every position and
as the stored balance words and zero allowance rows at the end.  No hypothesis mentions either
token's answers.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.PairTwoToken Blanc.Composition.Weth9Token

/-- **C6(a), the exhibit composition**: every V2 pair whose `token0` is USDC and `token1` is WETH9,
from the two-token joint checkpoint, with HASH-T for the Pair, USDC and WETH9, USDC's governance
premise F2 and the factory premises (the Pair never signs a USDC entry: `usdc_neverSigner_pair`,
through the checkpoint's `pairNotPrecompile`).  At every settled frame
outside the Pair's non-static frames and not shadowed in USDC (`Usdc.UsdcShadowed`: a frame running
USDC's implementation or library code at the proxy's storage, static or not, or any frame inside
the block of an earlier library frame, such as an EIP-1271 wallet's `isValidSignature` check after
a signed call has written its nonce or authorization state), both joint relations hold; at
the end, over the Pair's full replay, both reserves are covered by the stored balance words and
every tracked allowance row of the Pair is zero.  No hypothesis mentions either token's answers. -/
theorem pair_usdc_weth9_joint {pair usdc weth : Adr}
    {cfg : ChainConfig} {checkpoint future : BlockChain} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2 pair usdc weth KU KW KP st₀ checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (usdcFresh : Usdc.KeysFresh KU (Usdc.historyTouchedKeys usdc trace))
    (wethFresh : Weth9.KeysFresh KW (Weth9.historyTouchedKeys weth trace))
    (governance : Usdc.UsdcGovernance usdc trace)
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress) :
    (∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ¬ Usdc.UsdcShadowed usdc trace before f →
      ∃ (st : UniswapV2Pair.State) (K : WriterKey → Prop),
        WriterRep K (f.pre.state.getStor pair) st ∧ st.unlocked = 1 ∧ st.token0 = usdc ∧
          st.token1 = weth ∧
          st.reserve0.val ≤
            (Usdc.ledger (Usdc.historyKeyUniverse usdc trace KU) (f.pre.state.getStor usdc)).bal pair ∧
          (∀ g, (Usdc.ledger (Usdc.historyKeyUniverse usdc trace KU)
            (f.pre.state.getStor usdc)).allow pair g = 0) ∧
          st.reserve1.val ≤
            ((Weth9.ledger (Weth9.historyKeyUniverse weth trace KW) (f.pre.state.getStor weth)).bal
              pair).toNat ∧
          ∀ g, (Weth9.ledger (Weth9.historyKeyUniverse weth trace KW)
            (f.pre.state.getStor weth)).allow pair g = 0) ∧
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
        finish.reserve0.val ≤ Usdc.balanceBits ((future.state.getStor usdc).get (Usdc.balSlot pair)) ∧
        (∀ g, Usdc.historyKeyUniverse usdc trace KU (.allow pair g) →
          (future.state.getStor usdc).get (Usdc.allowSlot pair g) = 0) ∧
        finish.reserve1.val ≤ ((future.state.getStor weth).get (Weth9.balSlot pair)).toNat ∧
        ∀ g, Weth9.historyKeyUniverse weth trace KW (.allow pair g) →
          (future.state.getStor weth).get (Weth9.allowSlot pair g) = 0 := by
  exact pair_usdc_weth9_joint_finite trace joint.toF pairFresh usdcFresh wethFresh
    governance (joint.allowQuiet usdcFresh) factoryInstalled factoryNotSystem

end Blanc.Composition.UniswapV2PairUsdcWeth9
