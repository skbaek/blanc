import Blanc.Composition.UniswapV2PairUsdcWeth9LegsMint
import Blanc.Composition.UniswapV2PairUsdcWeth9MintLiveF
import Blanc.Composition.UniswapV2PairUsdcWeth9SyncLive

/-!
# C6(c): the mint liveness row with both tokens' queries discharged (U9c)

USDC = `token0`, WETH9 = `token1`.  The predecessor's `pair_weth9_history_mint_live_one` takes
token0's half of `MintBalanceForward` as a premise; here it is USDC's own run, pinned (`_read0`) to
`mintUsdcRead0` at the call gas WETH9's pin fixes, and WETH9's pin (`_read1`) reads USDC's result only
through its gas-free skeleton (`mintWethRead1_withGasLeft`).  USDC's facts at the frame come from
`pair_usdc_frame`.  No never-signer premise.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcLive

/-- **C6(c), the mint liveness row with both tokens' queries discharged** (USDC = token0, WETH9 =
token1).  As `pair_history_mint_live`, from the two-token joint checkpoint: WETH9's query is pinned
(`_read1`) to `mintWethRead1` over USDC's gas-free skeleton, USDC's to `mintUsdcRead0` at the call
gas WETH9's pin fixes.  What stays is the factory `feeTo` record and the Pair's charges and sentries
(`callee`), the frame's call depth, the Pair not USDC's admin word, the legs' gas sentries and the LP
rows' HASH-T.  No never-signer premise. -/
theorem pair_usdc_weth9_history_mint_live {pair usdc weth : Adr} {cfg : ChainConfig}
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
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842) (depth : 2 ≤ sevm.depth)
    (notAdmin : pair ≠ Usdc.adminOf pre.state usdc)
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
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace KP)
      (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord sevm 4).toAdr ++
        lpMintTouched callee.feeTo)) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
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
          (WriterFreshKeys (pairHistoryUniverse pair trace KP)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace KP)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩
              (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G)) := by
  exact pair_usdc_weth9_history_mint_live_finite trace joint.toF pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size guard selector depth notAdmin callee _read1 _read0 fits0 fits1 room0 room1 rowsFresh

end Blanc.Composition.UniswapV2PairUsdcWeth9
