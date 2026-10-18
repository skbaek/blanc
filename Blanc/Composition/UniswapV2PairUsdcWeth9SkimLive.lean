import Blanc.Composition.UniswapV2PairUsdcWeth9SkimEnv
import Blanc.Composition.UniswapV2PairUsdcWeth9Joint
import Blanc.Composition.UniswapV2PairWeth9SkimLiveOne
import Blanc.Lift.Usdc.HistoryEnd
import Blanc.Lift.UniswapV2Pair.SkimForwardKept

/-!
# C6(c): the skim liveness row with both tokens' records discharged (U9e)

USDC = `token0`, WETH9 = `token1`.  `pair_history_skim_live` takes `SkimForwardEnv`; all four token
records are pinned in `SkimCalleeUW` and discharged here:

* USDC's query (`skimUsdcRead0_spec`) and transfer (`skimUsdcLeg0_spec`) at the world facts the
  history's end gives (`usdc_history_end_core`: installed, admin unchanged, the footprint facts),
  carried across Skim's own prefix (Pair storage only) and the query (a view: `usdcBalanceCall_state`).
  The transfer amount `answer − reserve0` does not wrap because C6(a) bounds the Pair's reserve0 by
  its stored USDC balance at the history's end (`pair_usdc_weth9_joint`), and the answer is that
  balance.  The recipient's row joins the universe by `recipientFresh`.
* WETH9's query and transfer (`skimWethLeg1_of_kept`): USDC's transfer is an explicit post that
  keeps every other account's storage and every code (`usdcTransferCall_keeps`), so WETH9's code and
  the Pair's reserve1 word and WETH9 balance at the transfer's result are the frame's, where the
  WETH9 joint bounds reserve1 (`pair_weth9_frame`).
* The same keeps fact gives the forward run's reserve1 re-read after USDC's transfer
  (`SkimForwardEnv.run_of_kept`), so the generic row's trace-local HASH-T for the first transfer
  (`FirstCallFresh`) is not needed.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.UsdcLive

/-- **C6(c), the skim liveness row with both tokens' records discharged** (USDC = token0, WETH9 =
token1).  As `pair_history_skim_live`, from the two-token joint checkpoint, with both queries and
both transfers pinned in `callee`.  USDC's transfer amount is the queried balance less the cached
reserve0; it does not wrap because the model's acceptance of skim at the replayed state bounds
reserve0 by the queried balance (decision usdc-u9e-premise-trim: no never-signer premise).  What
stays is the lock sentries, the frame's call depth and
mutability, the Pair not USDC's admin word, HASH-T for the recipient's USDC row, USDC's state
conditions at the frame, and the legs' gas sentries. -/
theorem pair_usdc_weth9_history_skim_live {pair usdc weth : Adr} {cfg : ChainConfig}
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
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (static : sevm.isStatic = false) (depth : 2 ≤ sevm.depth)
    (notAdmin : pair ≠ Usdc.adminOf pre.state usdc)
    (callee : SkimCalleeUW sevm pre g) (usdcSentries : callee.UsdcSentries)
    (wethSentries : callee.WethSentries)
    (recipientFresh : Usdc.KeysFresh (Usdc.historyKeyUniverse usdc trace KU)
      [.bal (Sevm.dataWord sevm 4).toAdr])
    (usdcLive : UsdcTransferOk
      (Usdc.ledger (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc trace KU)
        [.bal (Sevm.dataWord sevm 4).toAdr]) (pre.state.getStor usdc))
      pair (Sevm.dataWord sevm 4).toAdr (callee.balance0 - skimReserve0 sevm pre).toNat) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 →
        transcript.ownTail.ownTail.firstWord = callee.balance1 →
        (runTyped finish (writerContext sevm []) (.skim (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace KP)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace KP)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) := by
  obtain ⟨futureCode, finish, K', replayed⟩ := pair_history_replayed trace joint.weth9.pairCode
    joint.weth9.pairRep pairFresh
  refine ⟨finish, K', replayed, fun transcript returndata answer0 answer1 accepted => ?_⟩
  have conditions := runTyped_skim_conditions accepted
  rw [answer0, answer1] at conditions
  obtain ⟨rep, -⟩ := replayed.at_frame target state
  obtain ⟨-, tokens⟩ := replayed.fixed joint.weth9.unlocked
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.weth9.pairCode factoryInstalled
      joint.weth9.pairNonzero factoryNotSystem)
  obtain ⟨code, token, -, reserve⟩ := pair_weth9_frame .one trace joint.weth9 pairFresh wethFresh
    factoryInstalled factoryNotSystem state
  obtain ⟨instEnd, -, injEnd, apartEnd, goodEnd⟩ := Usdc.usdc_history_end_core trace
    (⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩ : Usdc.UsdcHist usdc KU trace)
  have neW : sevm.currentTarget ≠ weth := target ▸ joint.weth9.apart
  have neU : sevm.currentTarget ≠ usdc := target ▸ joint.apart
  have uw : usdc ≠ weth := by
    have d := joint.weth9.distinct
    have t1 : st₀.token1 = weth := joint.weth9.token
    rw [joint.token0, t1] at d
    exact d
  have npW : sevm.benvStat.rules.isPrecomp weth = false :=
    propext ⟨fun h => absurd h (joint.weth9.wethNotPrecompile _ fork), fun h => absurd h Bool.false_ne_true⟩
  have npU : sevm.benvStat.rules.isPrecomp usdc = false :=
    propext ⟨fun h => absurd h (joint.usdcNotPrecompile _ fork), fun h => absurd h Bool.false_ne_true⟩
  have tok1 : (skimToken1 sevm pre).toAdr = weth := by
    unfold skimToken1
    rw [toAdr_toB256]
    change ((Devm.getStor (afterSload sevm (syncLockedWorld sevm pre) 6)
      sevm.currentTarget).get 7).toAdr = weth
    rw [afterSload_getStor]
    change ((syncLockedWorld sevm pre).getStorVal sevm.currentTarget 7).toAdr = weth
    rw [syncLockedWorld_slot (by decide), target]
    exact token
  have source := skimCache_source (current := ⟨finish, [], []⟩) (sevm := sevm) (b := pre)
    ⟨rep.fixed.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.2.1⟩
    rep.fixed.2.2.2.1 rep.fixed.2.2.2.2.1
  have tok0 : (skimToken0 sevm pre).toAdr = usdc := by
    rw [source.1, toAdr_toB256]
    exact tokens.1.trans joint.token0
  -- Skim's prefix and USDC's query touch only the Pair's storage
  have keepsCU := skimCachedWorld_keeps sevm pre neU
  have keepsCW := skimCachedWorld_keeps sevm pre neW
  have balC := skimCachedWorld_bal sevm pre
  have r0f : (skimUsdcRead0 sevm pre callee.callGasT0).1 = callee.qd0 :=
    (congrArg Prod.fst callee.read0).symm
  have r0s : (skimUsdcRead0 sevm pre callee.callGasT0).2 = callee.callGasQ0 :=
    (congrArg Prod.snd callee.read0).symm
  have qState : callee.qd0.state = (skimCachedWorld sevm pre).state := by
    rw [← r0f]
    exact usdcBalanceCall_state _ _ _ _ _ _ _
  have storC : (skimCachedWorld sevm pre).state.getStor usdc = future.state.getStor usdc := by
    rw [← state]
    exact keepsCU.2
  have codeC : ∀ a, (skimCachedWorld sevm pre).state.getCode a = future.state.getCode a :=
    fun a => (balC.2 a).trans (by rw [state])
  have storQ : callee.qd0.state.getStor usdc = future.state.getStor usdc := by
    rw [qState]
    exact storC
  have codeQ : ∀ a, callee.qd0.state.getCode a = future.state.getCode a := fun a => by
    rw [qState]
    exact codeC a
  have instAt : ∀ w : Jaune.State, (∀ a, w.getCode a = future.state.getCode a) →
      w.getStor usdc = future.state.getStor usdc → Usdc.UsdcInstalled usdc w := fun w hc hs =>
    ⟨by rw [hc]; exact instEnd.proxy, by rw [hc]; exact instEnd.impl, by rw [hc]; exact instEnd.lib,
      by rw [hs]; exact instEnd.slot, instEnd.implApart, instEnd.libApart⟩
  have adminAt : ∀ w : Jaune.State, w.getStor usdc = future.state.getStor usdc →
      Usdc.adminOf w usdc = Usdc.adminOf pre.state usdc := fun w hs => by
    unfold Usdc.adminOf
    rw [hs, state]
  -- USDC's query
  obtain ⟨code0, qenv0, reply, skelQ⟩ := skimUsdcRead0_spec (callGasT0 := callee.callGasT0) fork depth
    (by rw [tok0]; exact instAt _ codeC storC) (by rw [tok0]; exact npU)
    (by rw [tok0, adminAt _ storC, target]; exact notAdmin)
    (by rw [r0s]; exact usdcSentries.fitsRead) usdcSentries.roomRead
  rw [r0f, r0s] at qenv0
  rw [r0f] at reply skelQ
  -- USDC's transfer
  let U := SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc trace KU)
    [.bal (Sevm.dataWord sevm 4).toAdr]
  have toEq : (skimToWord sevm).toAdr = (Sevm.dataWord sevm 4).toAdr := by
    unfold skimToWord
    rw [toAdr_toB256]
  have kPair : U (.bal sevm.currentTarget) := Or.inl (by rw [target]; exact Or.inl joint.tracked)
  have kTo : U (.bal (skimToWord sevm).toAdr) := Or.inr (by rw [toEq]; exact List.mem_singleton_self _)
  have bal0 : callee.balance0 =
      Nat.toB256 (Usdc.balanceBits ((future.state.getStor usdc).get (Usdc.balSlot pair))) := by
    change Bytes.toB256 (callee.qd0.returnData.take 32) = _
    rw [reply, toB256_take_toBytes, tok0, storC, target]
  have bitsLt : Usdc.balanceBits ((future.state.getStor usdc).get (Usdc.balSlot pair)) < 2 ^ 256 :=
    lt_trans (Nat.mod_lt _ (Nat.two_pow_pos 255)) (by decide)
  have cover0 : skimReserve0 sevm pre ≤ callee.balance0 := by
    rw [source.2.2, B256.le_iff_toNat_le_toNat,
      B256.toNat_toB256_of_lt (lt_trans finish.reserve0.isLt (by decide))]
    exact conditions.2.2.2.1
  have amount : (skimLegAmount sevm pre callee.qd0).toNat ≤
      Usdc.balanceBits ((future.state.getStor usdc).get (Usdc.balSlot pair)) := by
    change (callee.balance0 - skimReserve0 sevm pre).toNat ≤ _
    rw [B256.toNat_sub_eq_of_le _ _ cover0, bal0, B256.toNat_toB256_of_lt bitsLt]
    exact Nat.sub_le _ _
  have l0s : (skimUsdcLeg0 sevm pre callee.qd0 callee.callGasQ1).2 = callee.callGasT0 := by
    rw [callee.gasT0, skelQ, skimUsdcLeg0_withGasLeft]
    rfl
  have tenv0 := skimUsdcLeg0_spec (callGasQ1 := callee.callGasQ1) (U := U) fork static depth
    (by rw [tok0]; exact instAt _ codeQ storQ)
    (by
      rw [tok0, storQ]
      exact ⟨injEnd.extend recipientFresh, apartEnd.extend recipientFresh,
        Usdc.ledger_good_congr goodEnd rfl rfl⟩)
    (by rw [tok0]; exact npU) kPair kTo (by rw [tok0, adminAt _ storQ, target]; exact notAdmin)
    (by
      have live := usdcLive
      rw [state] at live
      rw [tok0, storQ, toEq, target]
      exact live)
    (by
      rw [tok0, storQ, Usdc.ledger_bal kPair, target]
      exact amount)
    (by rw [l0s]; exact usdcSentries.fitsLeg) usdcSentries.roomLeg
  rw [l0s, ← callee.leg0] at tenv0
  -- what USDC's transfer keeps
  obtain ⟨keepS, keepC, -⟩ := usdcTransferCall_keeps sevm callee.qd0 (skimLegStack sevm pre)
    (skimLegMem sevm callee.qd0) 128 (skimLegAmount sevm pre callee.qd0) (skimToWord sevm)
    (skimToken0 sevm pre) 0x1a2b
    (skimUsdcLeg0Need sevm pre callee.qd0 callee.callGasQ1 + skimUsdcLeg0Charge sevm pre callee.qd0)
  have mask : (tokenMask (skimToken0 sevm pre)).toAdr = usdc := by rw [skimToken0_mask, tok0]
  have storT : ∀ a, a ≠ usdc → callee.dt0.state.getStor a = callee.qd0.state.getStor a :=
    fun a ha => by
      rw [callee.leg0]
      exact keepS a (by rw [mask]; exact ha)
  have codeDt0 : callee.dt0.state.getCode weth = Weth9.code := by
    rw [callee.leg0]
    exact (keepC weth).trans (by rw [qState]; exact (balC.2 weth).trans code)
  have valT : ∀ a k, a ≠ usdc → callee.dt0.getStorVal a k = (skimCachedWorld sevm pre).getStorVal a k :=
    fun a k ha => by
      change (callee.dt0.state.getStor a).get k = ((skimCachedWorld sevm pre).state.getStor a).get k
      rw [storT a ha, qState]
  have cover1 : skimReserve1Word (callee.dt0.getStorVal sevm.currentTarget 8) ≤
      callee.dt0.getStorVal weth (Weth9.balSlot sevm.currentTarget) := by
    rw [valT _ _ neU, valT _ _ (Ne.symm uw), keepsCW.getStorVal, skimReserve1Word_eq]
    change reserve1Read ((Devm.getStor (skimCachedWorld sevm pre) sevm.currentTarget).get 8) ≤ _
    unfold skimCachedWorld
    rw [afterSload_getStor, afterSload_getStor, afterSload_getStor]
    change reserve1Read ((syncLockedWorld sevm pre).getStorVal sevm.currentTarget 8) ≤ _
    rw [syncLockedWorld_slot (by decide), B256.le_iff_toNat_le_toNat, target]
    exact reserve
  -- WETH9's pins over USDC's skeletons are the legs over USDC's results
  obtain ⟨xd, hxd⟩ := skimUsdcLeg0_skel sevm pre callee.qd0 callee.callGasQ1
  rw [← callee.leg0] at hxd
  have R : ∀ c, skimWethRead1 sevm pre callee.qd0 callee.dt0 c =
      skimWethRead1 sevm pre (skimUsdcRead0Skel sevm pre)
        (skimUsdcLeg0Skel sevm pre (skimUsdcRead0Skel sevm pre)) c := by
    intro c
    rw [hxd, skelQ, skimUsdcLeg0Skel_withGasLeft, skimWethRead1_gasFree]
  have L : ∀ X, skimWethLeg1 sevm pre callee.qd0 callee.dt0 X g =
      skimWethLeg1 sevm pre (skimUsdcRead0Skel sevm pre)
        (skimUsdcLeg0Skel sevm pre (skimUsdcRead0Skel sevm pre)) X g := by
    intro X
    rw [hxd, skelQ, skimUsdcLeg0Skel_withGasLeft, skimWethLeg1_gasFree]
  have readFst : (skimWethRead1 sevm pre callee.qd0 callee.dt0 callee.callGasT1).1 = callee.qd1 := by
    rw [R]
    exact (congrArg Prod.fst callee.read1).symm
  have readSnd : (skimWethRead1 sevm pre callee.qd0 callee.dt0 callee.callGasT1).2 =
      callee.callGasQ1 := by
    rw [R]
    exact (congrArg Prod.snd callee.read1).symm
  have legSnd : (skimWethLeg1 sevm pre callee.qd0 callee.dt0
      (skimWethRead1 sevm pre callee.qd0 callee.dt0 callee.callGasT1).1 g).2 = callee.callGasT1 := by
    rw [L, R, skimWethLeg1_read, callee.gasT1]
    rfl
  have legFst : (skimWethLeg1 sevm pre callee.qd0 callee.dt0 callee.qd1 g).1 = callee.dt1 := by
    rw [L]
    exact callee.leg1.symm
  have legs := skimWethLeg1_of_kept (callGasT1 := callee.callGasT1) (g := g) fork static
    (by omega) tenv0 tok1 codeDt0 cover1 npW (by rw [readSnd]; exact wethSentries.fitsRead)
    wethSentries.roomRead (by rw [legSnd]; exact wethSentries.fitsLeg)
    (by rw [readFst]; exact wethSentries.roomLeg)
  rw [legSnd, readFst, readSnd, legFst] at legs
  obtain ⟨⟨code1, qenv1⟩, tenv1⟩ := legs
  -- the forward environment and the run
  let env : SkimForwardEnv sevm pre g :=
    { qd0 := callee.qd0, dt0 := callee.dt0, qd1 := callee.qd1, dt1 := callee.dt1,
      callGasQ0 := callee.callGasQ0, callGasT0 := callee.callGasT0, callGasQ1 := callee.callGasQ1,
      callGasT1 := callee.callGasT1, code0 := code0, sentry := callee.sentry,
      sentryU := callee.sentryU, qenv0 := qenv0, tenv0 := tenv0, code1 := code1, qenv1 := qenv1,
      tenv1 := tenv1 }
  have installedPre : some (pre.getCode sevm.currentTarget).toList = pairSem.image := by
    rw [target]
    change some (pre.state.getCode pair).toList = pairSem.image
    rw [state, futureCode]
    rfl
  have kept : reserve1Read (env.dt0.getStorVal sevm.currentTarget 8) =
      reserve1Read (env.qd0.getStorVal sevm.currentTarget 8) := by
    change reserve1Read ((callee.dt0.state.getStor _).get 8) =
      reserve1Read ((callee.qd0.state.getStor _).get 8)
    rw [storT _ neU]
  obtain ⟨run⟩ := env.run_of_kept (current := { state := finish, logs := [], updates := [] })
    [] rep pairSem pairSem_image installedPre output codeEq fork value size selector abi kept
    conditions
  exact ⟨run, rfl, fun newFresh => pair_live_outcome joint.weth9.pairRep pairFresh futureCode
    replayed run target state codeEq fork output representable newFresh⟩

end Blanc.Composition.UniswapV2PairUsdcWeth9
