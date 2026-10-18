import Blanc.Composition.UniswapV2PairUsdcWeth9SwapLiveFacts
import Blanc.Composition.UniswapV2PairUsdcWeth9SwapLiveF

/-!
# C6(c): the swap liveness row with both tokens' records discharged (USDC = token0, WETH9 = token1)

`pair_usdc_weth9_history_swap_live` restates `pair_history_swap_live` from the two-token joint
checkpoint with all four token callee records removed: USDC's `transfer` and post-callback
`balanceOf` are pinned (`_leg0`, `callee.read0`) to `swapUsdcLeg0`/`swapUsdcRead0`, the runs USDC's
deployed code determines (`swapUsdcLeg0_spec`, `swapUsdcRead0_spec`), and WETH9's (`_leg1`,
`callee.read1`) to `swapWethLeg1`/`swapWethRead1`.  The pins follow A17: WETH9's read USDC's results
only through their gas-free skeletons; `swapWethLeg1_withGasLeft0` and `swapWethRead1_withGasLeft0`
carry them to the real results.

Why USDC can pay: `pair_usdc_weth9_joint`'s end conjunct bounds `reserve0` by the Pair's USDC
balance bits at the history's end, the model guard gives `amount0Out < reserve0`, and the prefix
world changes only the Pair's storage.  USDC's facts at the history's end are
`usdc_history_end_core` (installed, the history's key universe injective and apart, a good ledger),
extended by the recipient's row under `recipientFresh`.  WETH9's facts after USDC's transfer are
read off USDC's explicit post (`usdcTransferCall_keeps`): no HASH-T over USDC's child.  USDC at the
post-callback join world: its runtimes by code identity, its implementation slot and admin word
kept by both explicit transfers (`usdcTransferCall_tokenStor`, `wethTransferCall_keepsStor`) or,
after a callback, `_callbackGovernance`: the implementation slot unchanged and the Pair not the
admin word (decision usdc-u9b-a6-weaken).
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.UsdcLive

/-- **C6(c), the swap liveness row with both tokens' records discharged** (USDC = token0, WETH9 =
token1, both outputs allowed).  §10c amended to U9a's legs: the never-signer fact, now derived from
the checkpoint (`usdc_neverSigner_pair`; C6(a) bounds reserve0 by the Pair's USDC balance, which
covers `amount0Out`), two levels of call depth, the Pair not USDC's admin word, HASH-T for the
recipient's USDC row and `usdcLive` over that extended universe, the USDC transfer leg's 63/64
sentry, and the callback's governance (the callback leaves USDC's implementation slot, and does not
make the Pair USDC's admin; frame-level F2).  WETH9's records after USDC's transfer are discharged
from USDC's explicit post, with no HASH-T over USDC's child. -/
theorem pair_usdc_weth9_history_swap_live {pair usdc weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {KU : Usdc.Key → Prop} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2 pair usdc weth KU KW KP st₀ checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (usdcFresh : Usdc.KeysFresh KU (Usdc.historyTouchedKeys usdc trace))
    (wethFresh : Weth9.KeysFresh KW (Weth9.historyTouchedKeys weth trace))
    (governance : Usdc.UsdcGovernance usdc trace)
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress)
    {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) (guards : SwapAbiGuards sevm)
    (depth : 2 ≤ sevm.depth)
    (notAdmin : pair ≠ Usdc.adminOf pre.state usdc)
    (recipientFresh : swapAmount0Out sevm ≠ 0 →
      Usdc.KeysFresh (Usdc.historyKeyUniverse usdc trace KU) [.bal (swapRecipient sevm)])
    (usdcLive : swapAmount0Out sevm ≠ 0 →
      UsdcTransferOk (Usdc.ledger (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc trace KU)
        [.bal (swapRecipient sevm)]) (pre.state.getStor usdc))
        pair (swapRecipient sevm) (swapAmount0Out sevm).toNat) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
      ∀ {dC : Devm} {cgC g : Nat}
        (callee : SwapBackCalleeEnvUW sevm
          (swapFrontCutWorld sevm pre (usdcLeg0Skel sevm pre finish)
            (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC)
          (swapFrontCutMem sevm (usdcLeg0Skel sevm pre finish)
            (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC)
          (swapFrontCutMem sevm (usdcLeg0Skel sevm pre finish)
            (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC).size
          (swapFrontPtr sevm (usdcLeg0Skel sevm pre finish)
            (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)))
          (swapCutWords sevm finish) 0x257 [0x022c0d9f] (g + 1))
        {d0 d1 : Devm} {cg0 cg1 : Nat}
        (_leg1 : (d1, cg1) = swapWethLeg1 sevm pre finish (usdcLeg0Skel sevm pre finish) cgC callee.gas)
        (_leg0 : (d0, cg0) = swapUsdcLeg0 sevm pre finish cg1 cgC callee.gas)
        (_front : SwapFrontEnvUW sevm pre finish d0 d1 dC cg0 cg1 cgC callee.gas)
        (_frameGas : swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
          swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166 < 2 ^ 256)
        (_callbackRoom : 3200 ≤ swapFrontCallbackGas sevm pre d0 d1 cgC callee.gas)
        (_readGas : callee.callGas0 < 2 ^ 256 ∧ callee.callGas1 < 2 ^ 256)
        (_transferGas : cg0 < 2 ^ 256 ∧ cg1 < 2 ^ 256)
        (_leg0Room : swapAmount0Out sevm ≠ 0 → usdcLeg0Budget sevm pre finish ≤
          except64th (usdcLeg0Need sevm pre finish cg1 cgC callee.gas + usdcLeg0Used sevm pre finish))
        (_callbackGovernance : swapDataLength sevm ≠ 0 →
          ((swapFrontCutWorld sevm pre d0 d1 dC).state.getStor usdc).get Usdc.implSlot =
              Usdc.usdcImpl.toB256 ∧
            pair ≠ Usdc.adminOf (swapFrontCutWorld sevm pre d0 d1 dC).state usdc),
        SwapContextConditions (writerContext sevm []) →
        SwapModelConditions finish (swapAmount0Out sevm) (swapAmount1Out sevm) (swapRecipient sevm)
          (swapBalanceWord callee.d0.returnData) (swapBalanceWord callee.d1.returnData) →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty
            (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
              swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166))
            (.ok (St callee.post [0x022c0d9f] callee.memory g)),
          (WriterFreshKeys (pairHistoryUniverse pair trace KP)
              (pairDerivKeys ⟨0, sevm, _, .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace KP)
                (pairDerivKeys ⟨0, sevm, _, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, _, .ok _, run⟩
              (St callee.post [0x022c0d9f] callee.memory g)) := by
  exact pair_usdc_weth9_history_swap_live_finite trace joint.toF pairFresh usdcFresh wethFresh
    governance (joint.allowQuiet usdcFresh) factoryInstalled factoryNotSystem target
    state codeEq fork output representable value size selector guards depth notAdmin recipientFresh
    usdcLive

end Blanc.Composition.UniswapV2PairUsdcWeth9
