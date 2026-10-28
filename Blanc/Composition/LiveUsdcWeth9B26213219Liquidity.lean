import Blanc.Composition.LiveUsdcWeth9B26213219Anchor
import Blanc.Composition.LiveUsdcWeth9B26213219Sync
import Blanc.Composition.LiveUsdcWeth9B26213219Mint
import Blanc.Composition.LiveUsdcWeth9B26213219Burn
import Blanc.Composition.LiveUsdcWeth9B26213219Skim

/-!
# Remaining live operations at the bound B checkpoint

The bound observation and original retained-lifetime histories construct the
checkpoint. Each operation keeps its existing attainable-call conclusion and
all gas, context, model, recipient and outcome conditions. These four operations
do not require USDC P1; no unnecessary historical allowance assumption is added.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.UsdcLive
  Blanc.Composition.UniswapV2PairUsdcWeth9

/-- The existing sync conclusion from observations bound to the original B tip. -/
theorem sync_from_bound_history
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
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation))
    {sevm : Sevm} {pre d0 d1 : Devm} {callGas0 callGas1 G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9) (static : sevm.isStatic = false)
    (depth : 2 ≤ sevm.depth)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm pre)
        (syncFirstToken sevm pre).toAdr) + sloadCost sevm (syncLockedWorld sevm pre) 6 + 119 +
      sstoreCost sevm (afterSload sevm pre 12) 12 0)
    (_read1 : (d1, callGas1) = syncWethRead1 sevm (syncUsdcRead0Skel sevm pre) G)
    (_read0 : (d0, callGas0) = syncUsdcRead0 sevm pre callGas1)
    (fits0 : callGas0 < 2 ^ 256) (fits1 : callGas1 < 2 ^ 256)
    (room0 : usdcBalNeed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128
        (syncFirstToken sevm pre) ≤
      except64th (syncRead0Need sevm callGas1 (syncUsdcRead0Skel sevm pre) +
        usdcBalUsed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128
          (syncFirstToken sevm pre)))
    (room1 : balUsed sevm (afterSload sevm d0 7) (syncTail1 d0)
        (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0) ≤
      except64th (syncRead1Need sevm d0 G (wethBalanceSkel sevm (afterSload sevm d0 7)
          (syncTail1 d0) (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
          128 (syncToken1 sevm d0)) +
        balUsed sevm (afterSload sevm d0 7) (syncTail1 d0)
          (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0))) :
    let trace := anchor.futureTrace continuation
    SyncLiveOutcome pair trace pd.keys pd.model sevm pre d0 d1 callGas0 G := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model anchor wd pd link holderFresh
    wethSenderExcluded avoid initialPair
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact anchor.reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_sync_live_finite trace joint pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size selector static depth notAdmin sentry _read1 _read0 fits0 fits1 room0 room1

/-- The existing mint conclusion from observations bound to the original B tip. -/
theorem mint_from_bound_history
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
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation))
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842) (depth : 2 ≤ sevm.depth)
    (callee : MintCalleeRest sevm pre [0x6a627842] getterInitMemory
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b (G + 43))
    (_read1 : (callee.d1, callee.callGas1) = mintWethRead1 sevm
      (mintUsdcRead0Skel sevm (mintCacheWorld sevm pre) [0x6a627842] getterInitMemory
        (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
      [0x6a627842] getterInitMemory (mintR1 sevm pre) (mintR0 sevm pre)
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b callee.factoryGas)
    (_read0 : (callee.d0, callee.callGas0) = mintUsdcRead0 sevm (mintCacheWorld sevm pre)
      [0x6a627842] getterInitMemory (mintR1 sevm pre) (mintR0 sevm pre)
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b callee.callGas1)
    (fits0 : callee.callGas0 < 2 ^ 256) (fits1 : callee.callGas1 < 2 ^ 256)
    (room0 : usdcBalNeed sevm (afterSload sevm (mintCacheWorld sevm pre) 6)
        (mintTail0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
          (Sevm.dataWord sevm 4).toAdr.toB256 0x039b) getterInitMemory 128
        (mintToken0 sevm (mintCacheWorld sevm pre)) ≤
      except64th (mintRead0Need sevm callee.callGas1
          (mintUsdcRead0Skel sevm (mintCacheWorld sevm pre) [0x6a627842] getterInitMemory
            (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b) +
        usdcBalUsed sevm (afterSload sevm (mintCacheWorld sevm pre) 6)
          (mintTail0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b) getterInitMemory 128
          (mintToken0 sevm (mintCacheWorld sevm pre))))
    (room1 : balUsed sevm (afterSload sevm callee.d0 7)
        (mintTail1 callee.d0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
          (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
        (balanceReplyMemory getterInitMemory sevm.currentTarget callee.d0.returnData) 128
        (syncToken1 sevm callee.d0) ≤
      except64th (mintRead1Need sevm callee.factoryGas (wethBalanceSkel sevm
          (afterSload sevm callee.d0 7)
          (mintTail1 callee.d0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
          (balanceReplyMemory getterInitMemory sevm.currentTarget callee.d0.returnData) 128
          (syncToken1 sevm callee.d0)) +
        balUsed sevm (afterSload sevm callee.d0 7)
          (mintTail1 callee.d0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
          (balanceReplyMemory getterInitMemory sevm.currentTarget callee.d0.returnData) 128
          (syncToken1 sevm callee.d0)))
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair (anchor.futureTrace continuation) pd.keys)
      (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord sevm 4).toAdr ++
        lpMintTouched callee.feeTo)) :
    let trace := anchor.futureTrace continuation
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace pd.keys pd.model finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        (runTyped finish (writerContext sevm []) (.mint (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ (liquidity : B256)
          (run : Exec 0 sevm (St pre [] Mem.empty (callee.gas + 228))
            (.ok (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G))),
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).gasLeft = G ∧
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).output =
            liquidity.toBytes ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace pd.keys)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace pd.keys)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩
              (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G)) := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model anchor wd pd link holderFresh
    wethSenderExcluded avoid initialPair
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact anchor.reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_mint_live_finite trace joint pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size guard selector depth notAdmin callee _read1 _read0 fits0 fits1 room0 room1 rowsFresh

/-- The existing burn conclusion from observations bound to the original B tip. -/
theorem burn_from_bound_history
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
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation))
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44) (depth : 2 ≤ sevm.depth)
    (callee : BurnEnvUW sevm pre g) (usdcSentries : callee.UsdcSentries)
    (wethSentries : callee.WethSentries)
    (recipientFresh : Usdc.KeysFresh (Usdc.historyKeyUniverse usdc (anchor.futureTrace continuation) (FiniteCheckpoint.rowKeys usdcRows))
      [.bal (Sevm.dataWord sevm 4).toAdr])
    (usdcLive : UsdcTransferOk
      (Usdc.ledger (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc (anchor.futureTrace continuation) (FiniteCheckpoint.rowKeys usdcRows))
        [.bal (Sevm.dataWord sevm 4).toAdr]) (pre.state.getStor usdc))
      pair (Sevm.dataWord sevm 4).toAdr callee.words.amount0.toNat)
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair (anchor.futureTrace continuation) pd.keys)
      (lpMintTouched sevm.currentTarget ++ lpMintTouched callee.feeTo)) :
    let trace := anchor.futureTrace continuation
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace pd.keys pd.model finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final0 →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final1 →
        (runTyped finish (writerContext sevm []) (.burn (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace pd.keys)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace pd.keys)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model anchor wd pd link holderFresh
    wethSenderExcluded avoid initialPair
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact anchor.reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_burn_live_finite trace joint pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size guard selector depth notAdmin callee usdcSentries wethSentries recipientFresh usdcLive rowsFresh

/-- The existing skim conclusion from observations bound to the original B tip. -/
theorem skim_from_bound_history
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
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation))
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (static : sevm.isStatic = false) (depth : 2 ≤ sevm.depth)
    (callee : SkimCalleeUW sevm pre g) (usdcSentries : callee.UsdcSentries)
    (wethSentries : callee.WethSentries)
    (recipientFresh : Usdc.KeysFresh (Usdc.historyKeyUniverse usdc (anchor.futureTrace continuation) (FiniteCheckpoint.rowKeys usdcRows))
      [.bal (Sevm.dataWord sevm 4).toAdr])
    (usdcLive : UsdcTransferOk
      (Usdc.ledger (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc (anchor.futureTrace continuation) (FiniteCheckpoint.rowKeys usdcRows))
        [.bal (Sevm.dataWord sevm 4).toAdr]) (pre.state.getStor usdc))
      pair (Sevm.dataWord sevm 4).toAdr (callee.balance0 - skimReserve0 sevm pre).toNat) :
    let trace := anchor.futureTrace continuation
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace pd.keys pd.model finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 →
        transcript.ownTail.ownTail.firstWord = callee.balance1 →
        (runTyped finish (writerContext sevm []) (.skim (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace pd.keys)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace pd.keys)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model anchor wd pd link holderFresh
    wethSenderExcluded avoid initialPair
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact anchor.reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_skim_live_finite trace joint pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size abi selector static depth notAdmin callee usdcSentries wethSentries recipientFresh usdcLive

/-- Receipt-premise variant: the same conclusion and remaining hypotheses,
using absence of Pair-owned WETH approvals in the original pre-deployment receipts.
The receipt premise is explicit and no external observation is adopted. -/
theorem sync_from_bound_receipts
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
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation))
    {sevm : Sevm} {pre d0 d1 : Devm} {callGas0 callGas1 G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9) (static : sevm.isStatic = false)
    (depth : 2 ≤ sevm.depth)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm pre)
        (syncFirstToken sevm pre).toAdr) + sloadCost sevm (syncLockedWorld sevm pre) 6 + 119 +
      sstoreCost sevm (afterSload sevm pre 12) 12 0)
    (_read1 : (d1, callGas1) = syncWethRead1 sevm (syncUsdcRead0Skel sevm pre) G)
    (_read0 : (d0, callGas0) = syncUsdcRead0 sevm pre callGas1)
    (fits0 : callGas0 < 2 ^ 256) (fits1 : callGas1 < 2 ^ 256)
    (room0 : usdcBalNeed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128
        (syncFirstToken sevm pre) ≤
      except64th (syncRead0Need sevm callGas1 (syncUsdcRead0Skel sevm pre) +
        usdcBalUsed sevm (syncFirstWorld sevm pre) syncTail getterInitMemory 128
          (syncFirstToken sevm pre)))
    (room1 : balUsed sevm (afterSload sevm d0 7) (syncTail1 d0)
        (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0) ≤
      except64th (syncRead1Need sevm d0 G (wethBalanceSkel sevm (afterSload sevm d0 7)
          (syncTail1 d0) (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
          128 (syncToken1 sevm d0)) +
        balUsed sevm (afterSload sevm d0 7) (syncTail1 d0)
          (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData) 128
          (syncToken1 sevm d0))) :
    let trace := anchor.futureTrace continuation
    SyncLiveOutcome pair trace pd.keys pd.model sevm pre d0 d1 callGas0 G := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model_of_receipts anchor wd pd link holderFresh
    wethSenderExcluded logs
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact anchor.reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_sync_live_finite trace joint pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size selector static depth notAdmin sentry _read1 _read0 fits0 fits1 room0 room1

/-- Receipt-premise variant: the same conclusion and remaining hypotheses,
using absence of Pair-owned WETH approvals in the original pre-deployment receipts.
The receipt premise is explicit and no external observation is adopted. -/
theorem mint_from_bound_receipts
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
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation))
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842) (depth : 2 ≤ sevm.depth)
    (callee : MintCalleeRest sevm pre [0x6a627842] getterInitMemory
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b (G + 43))
    (_read1 : (callee.d1, callee.callGas1) = mintWethRead1 sevm
      (mintUsdcRead0Skel sevm (mintCacheWorld sevm pre) [0x6a627842] getterInitMemory
        (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
      [0x6a627842] getterInitMemory (mintR1 sevm pre) (mintR0 sevm pre)
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b callee.factoryGas)
    (_read0 : (callee.d0, callee.callGas0) = mintUsdcRead0 sevm (mintCacheWorld sevm pre)
      [0x6a627842] getterInitMemory (mintR1 sevm pre) (mintR0 sevm pre)
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b callee.callGas1)
    (fits0 : callee.callGas0 < 2 ^ 256) (fits1 : callee.callGas1 < 2 ^ 256)
    (room0 : usdcBalNeed sevm (afterSload sevm (mintCacheWorld sevm pre) 6)
        (mintTail0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
          (Sevm.dataWord sevm 4).toAdr.toB256 0x039b) getterInitMemory 128
        (mintToken0 sevm (mintCacheWorld sevm pre)) ≤
      except64th (mintRead0Need sevm callee.callGas1
          (mintUsdcRead0Skel sevm (mintCacheWorld sevm pre) [0x6a627842] getterInitMemory
            (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b) +
        usdcBalUsed sevm (afterSload sevm (mintCacheWorld sevm pre) 6)
          (mintTail0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b) getterInitMemory 128
          (mintToken0 sevm (mintCacheWorld sevm pre))))
    (room1 : balUsed sevm (afterSload sevm callee.d0 7)
        (mintTail1 callee.d0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
          (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
        (balanceReplyMemory getterInitMemory sevm.currentTarget callee.d0.returnData) 128
        (syncToken1 sevm callee.d0) ≤
      except64th (mintRead1Need sevm callee.factoryGas (wethBalanceSkel sevm
          (afterSload sevm callee.d0 7)
          (mintTail1 callee.d0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
          (balanceReplyMemory getterInitMemory sevm.currentTarget callee.d0.returnData) 128
          (syncToken1 sevm callee.d0)) +
        balUsed sevm (afterSload sevm callee.d0 7)
          (mintTail1 callee.d0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
          (balanceReplyMemory getterInitMemory sevm.currentTarget callee.d0.returnData) 128
          (syncToken1 sevm callee.d0)))
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair (anchor.futureTrace continuation) pd.keys)
      (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord sevm 4).toAdr ++
        lpMintTouched callee.feeTo)) :
    let trace := anchor.futureTrace continuation
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace pd.keys pd.model finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        (runTyped finish (writerContext sevm []) (.mint (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ (liquidity : B256)
          (run : Exec 0 sevm (St pre [] Mem.empty (callee.gas + 228))
            (.ok (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G))),
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).gasLeft = G ∧
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).output =
            liquidity.toBytes ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace pd.keys)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace pd.keys)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩
              (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G)) := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model_of_receipts anchor wd pd link holderFresh
    wethSenderExcluded logs
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact anchor.reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_mint_live_finite trace joint pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size guard selector depth notAdmin callee _read1 _read0 fits0 fits1 room0 room1 rowsFresh

/-- Receipt-premise variant: the same conclusion and remaining hypotheses,
using absence of Pair-owned WETH approvals in the original pre-deployment receipts.
The receipt premise is explicit and no external observation is adopted. -/
theorem burn_from_bound_receipts
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
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation))
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44) (depth : 2 ≤ sevm.depth)
    (callee : BurnEnvUW sevm pre g) (usdcSentries : callee.UsdcSentries)
    (wethSentries : callee.WethSentries)
    (recipientFresh : Usdc.KeysFresh (Usdc.historyKeyUniverse usdc (anchor.futureTrace continuation) (FiniteCheckpoint.rowKeys usdcRows))
      [.bal (Sevm.dataWord sevm 4).toAdr])
    (usdcLive : UsdcTransferOk
      (Usdc.ledger (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc (anchor.futureTrace continuation) (FiniteCheckpoint.rowKeys usdcRows))
        [.bal (Sevm.dataWord sevm 4).toAdr]) (pre.state.getStor usdc))
      pair (Sevm.dataWord sevm 4).toAdr callee.words.amount0.toNat)
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair (anchor.futureTrace continuation) pd.keys)
      (lpMintTouched sevm.currentTarget ++ lpMintTouched callee.feeTo)) :
    let trace := anchor.futureTrace continuation
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace pd.keys pd.model finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final0 →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final1 →
        (runTyped finish (writerContext sevm []) (.burn (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace pd.keys)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace pd.keys)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model_of_receipts anchor wd pd link holderFresh
    wethSenderExcluded logs
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact anchor.reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_burn_live_finite trace joint pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size guard selector depth notAdmin callee usdcSentries wethSentries recipientFresh usdcLive rowsFresh

/-- Receipt-premise variant: the same conclusion and remaining hypotheses,
using absence of Pair-owned WETH approvals in the original pre-deployment receipts.
The receipt premise is explicit and no external observation is adopted. -/
theorem skim_from_bound_receipts
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
    (pairFresh : WriterFreshKeys pd.keys
      (pairHistoryTouchedKeys pair (anchor.futureTrace continuation)))
    (usdcFresh : Usdc.KeysFresh (FiniteCheckpoint.rowKeys usdcRows)
      (Usdc.historyTouchedKeys usdc (anchor.futureTrace continuation)))
    (wethFresh : Weth9.KeysFresh wd.keys
      (Weth9.historyTouchedKeys weth (anchor.futureTrace continuation)))
    (governance : Usdc.UsdcGovernance usdc (anchor.futureTrace continuation))
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (static : sevm.isStatic = false) (depth : 2 ≤ sevm.depth)
    (callee : SkimCalleeUW sevm pre g) (usdcSentries : callee.UsdcSentries)
    (wethSentries : callee.WethSentries)
    (recipientFresh : Usdc.KeysFresh (Usdc.historyKeyUniverse usdc (anchor.futureTrace continuation) (FiniteCheckpoint.rowKeys usdcRows))
      [.bal (Sevm.dataWord sevm 4).toAdr])
    (usdcLive : UsdcTransferOk
      (Usdc.ledger (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc (anchor.futureTrace continuation) (FiniteCheckpoint.rowKeys usdcRows))
        [.bal (Sevm.dataWord sevm 4).toAdr]) (pre.state.getStor usdc))
      pair (Sevm.dataWord sevm 4).toAdr (callee.balance0 - skimReserve0 sevm pre).toNat) :
    let trace := anchor.futureTrace continuation
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace pd.keys pd.model finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 →
        transcript.ownTail.ownTail.firstWord = callee.balance1 →
        (runTyped finish (writerContext sevm []) (.skim (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace pd.keys)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace pd.keys)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) := by
  let trace := anchor.futureTrace continuation
  have joint := checkpoint_at_bound_deployment_model_of_receipts anchor wd pd link holderFresh
    wethSenderExcluded logs
  obtain ⟨factoryInstalled, factoryNotSystem⟩ := anchor.reads.factory_facts pd.rep
  have notAdmin : pair ≠ Usdc.adminOf pre.state usdc := by
    rw [state]
    exact anchor.reads.future_pair_not_admin trace
      ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  exact pair_usdc_weth9_history_skim_live_finite trace joint pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size abi selector static depth notAdmin callee usdcSentries wethSentries recipientFresh usdcLive

end Blanc.Composition.LiveUsdcWeth9B26213219
