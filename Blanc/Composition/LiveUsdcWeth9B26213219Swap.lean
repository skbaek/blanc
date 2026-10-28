import Blanc.Composition.LiveUsdcWeth9B26213219P1
import Blanc.Composition.LiveUsdcWeth9B26213219Sync
import Blanc.Composition.UniswapV2PairUsdcWeth9SwapLiveF

/-!
# Concrete live swap from original histories

The same-B checkpoint and touched-row P1 are derived from original history
inputs. The source swap theorem's complete callback, gas, acceptance, context,
model and outcome conditions remain. Proxy-admin exclusion follows from the
finite read and future governance. Historical evidence remains unadopted.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.UsdcLive
  Blanc.Composition.UniswapV2PairUsdcWeth9

/-- The complete attainable-swap conclusion on the bound original future trace.
The checkpoint, USDC quietness and proxy-admin exclusion are all derived. -/
theorem swap_from_original_history
    {checkpoint future : BlockChain}
    (anchor : ObservedCheckpoint checkpoint)
    (wd : WethDeploymentTo checkpoint) (pd : PairDeploymentTo checkpoint)
    (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (wethSenderExcluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (avoid : ∀ root ∈ link.beforePairFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ pair)
    (initialPair : wd.cut.afterBenv.state.getCode pair = ByteArray.empty)
    (continuation : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    (usdcHistory : OriginalUsdcHistory (anchor.futureTrace continuation))
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation))
    {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) (guards : SwapAbiGuards sevm)
    (depth : 2 ≤ sevm.depth)
    (recipientFresh : swapAmount0Out sevm ≠ 0 →
      Usdc.KeysFresh (Usdc.historyKeyUniverse usdc (anchor.futureTrace continuation) (FiniteCheckpoint.rowKeys usdcRows)) [.bal (swapRecipient sevm)])
    (usdcLive : swapAmount0Out sevm ≠ 0 →
      UsdcTransferOk (Usdc.ledger (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc (anchor.futureTrace continuation) (FiniteCheckpoint.rowKeys usdcRows))
        [.bal (swapRecipient sevm)]) (pre.state.getStor usdc))
        pair (swapRecipient sevm) (swapAmount0Out sevm).toNat) :
    let trace := anchor.futureTrace continuation
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace pd.keys pd.model finish K' ∧
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
          (WriterFreshKeys (pairHistoryUniverse pair trace pd.keys)
              (pairDerivKeys ⟨0, sevm, _, .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace pd.keys)
                (pairDerivKeys ⟨0, sevm, _, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, _, .ok _, run⟩
              (St callee.post [0x022c0d9f] callee.memory g)) := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model anchor wd pd link holderFresh
    wethSenderExcluded avoid initialPair
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact anchor.reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_swap_live_finite trace joint pairFresh usdcFresh wethFresh
    governance usdcHistory.quiet factoryInstalled factoryNotSystem target state codeEq fork
    output representable value size selector guards depth notAdmin recipientFresh usdcLive

/-- Receipt-premise variant: the same conclusion and remaining hypotheses,
using absence of Pair-owned WETH approvals in the original pre-deployment receipts.
The receipt premise is explicit and no external observation is adopted. -/
theorem swap_from_original_receipts
    {checkpoint future : BlockChain}
    (anchor : ObservedCheckpoint checkpoint)
    (wd : WethDeploymentTo checkpoint) (pd : PairDeploymentTo checkpoint)
    (link : DeploymentHistoryLink wd pd)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (wethSenderExcluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (logs : ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉
        link.beforePairReceiptLogs)
    (continuation : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    (usdcHistory : OriginalUsdcHistory (anchor.futureTrace continuation))
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation))
    {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) (guards : SwapAbiGuards sevm)
    (depth : 2 ≤ sevm.depth)
    (recipientFresh : swapAmount0Out sevm ≠ 0 →
      Usdc.KeysFresh (Usdc.historyKeyUniverse usdc (anchor.futureTrace continuation) (FiniteCheckpoint.rowKeys usdcRows)) [.bal (swapRecipient sevm)])
    (usdcLive : swapAmount0Out sevm ≠ 0 →
      UsdcTransferOk (Usdc.ledger (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc (anchor.futureTrace continuation) (FiniteCheckpoint.rowKeys usdcRows))
        [.bal (swapRecipient sevm)]) (pre.state.getStor usdc))
        pair (swapRecipient sevm) (swapAmount0Out sevm).toNat) :
    let trace := anchor.futureTrace continuation
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace pd.keys pd.model finish K' ∧
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
          (WriterFreshKeys (pairHistoryUniverse pair trace pd.keys)
              (pairDerivKeys ⟨0, sevm, _, .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace pd.keys)
                (pairDerivKeys ⟨0, sevm, _, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, _, .ok _, run⟩
              (St callee.post [0x022c0d9f] callee.memory g)) := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model_of_receipts anchor wd pd link holderFresh
    wethSenderExcluded logs
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact anchor.reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_swap_live_finite trace joint pairFresh usdcFresh wethFresh
    governance usdcHistory.quiet factoryInstalled factoryNotSystem target state codeEq fork
    output representable value size selector guards depth notAdmin recipientFresh usdcLive

end Blanc.Composition.LiveUsdcWeth9B26213219
