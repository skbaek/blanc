import Blanc.Composition.UniswapV2PairUsdcWeth9LegsMint
import Blanc.Composition.UniswapV2PairUsdcWeth9SyncLiveF

/-!
# C6(c): the mint liveness row over the support-free checkpoint (finite twin)

Twin of `UniswapV2PairUsdcWeth9MintLive.lean`: `pair_usdc_weth9_history_mint_live_finite`
is the mint row with `joint : JointCheckpoint2F …` and no quiet premise (the proof never
uses USDC's joint relation). The frame facts come from `pair_usdc_frameF` and the small
world helpers in `UniswapV2PairUsdcWeth9SyncLiveF`; only the mint-stage code lemma is
restated here.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcLive

theorem mintStageWorld_getCodeF (sevm : Sevm) (pre : Devm) (a : Adr) :
    (afterSload sevm (mintCacheWorld sevm pre) 6).getCode a = pre.getCode a := by
  unfold mintCacheWorld mintLockedWorld
  rw [afterSload_getCode, afterSload_getCode, afterSstore_getCode, afterSload_getCode]

/-- **C6(c), the mint liveness row, support-free** (USDC = token0, WETH9 = token1).
Twin of `pair_usdc_weth9_history_mint_live` with `joint : JointCheckpoint2F …` and no
quiet premise: the proof never uses USDC's joint relation. -/
theorem pair_usdc_weth9_history_mint_live_finite {pair usdc weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {KU : Usdc.Key → Prop} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2F pair usdc weth KU KW KP st₀ checkpoint.state)
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
  have h0 : (mintUsdcRead0 sevm (mintCacheWorld sevm pre) [0x6a627842] getterInitMemory
      (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b
      callee.callGas1).1 = callee.d0 := (congrArg Prod.fst _read0).symm
  have hg : (mintUsdcRead0 sevm (mintCacheWorld sevm pre) [0x6a627842] getterInitMemory
      (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b
      callee.callGas1).2 = callee.callGas0 := (congrArg Prod.snd _read0).symm
  obtain ⟨token0, inst, -⟩ := pair_usdc_frameF trace joint pairFresh usdcFresh wethFresh governance
    factoryInstalled factoryNotSystem state
  have tok : ((mintCacheWorld sevm pre).getStorVal sevm.currentTarget 6).toAdr = usdc := by
    rw [mintLockedWorld_slot (by decide), target]
    exact token0
  have keeps := mintCacheWorld_keeps sevm pre (w := usdc) (target ▸ joint.apart)
  obtain ⟨winst, wadmin⟩ := usdc_world_congrF (P := usdc) (w := pre.state)
    (w' := (afterSload sevm (mintCacheWorld sevm pre) 6).state) (mintStageWorld_getCodeF sevm pre)
    keeps.2
  have spec := mintUsdcRead0_spec (callGas1 := callee.callGas1) fork depth
    (by rw [tok]; exact winst inst) (by rw [tok]; exact notPrecompile_usdcF joint fork)
    (by rw [tok, wadmin, target]; exact notAdmin) (by decide) getterInitMemory_ptr.wf
    (by rw [hg]; exact fits0) room0
  rw [h0, hg] at spec
  obtain ⟨half0, -, skel⟩ := spec
  have read1 : (callee.d1, callee.callGas1) = mintWethRead1 sevm callee.d0 [0x6a627842]
      getterInitMemory (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256
      0x039b callee.factoryGas := by
    rw [_read1, skel, mintWethRead1_withGasLeft]
  exact pair_weth9_history_mint_live_one trace joint.weth9 pairFresh wethFresh factoryInstalled
    factoryNotSystem target state codeEq fork output representable value size guard selector
    (by omega) callee half0 read1 fits1 room1 rowsFresh

end Blanc.Composition.UniswapV2PairUsdcWeth9
