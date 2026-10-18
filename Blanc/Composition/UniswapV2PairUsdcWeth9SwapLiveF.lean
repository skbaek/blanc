import Blanc.Composition.UniswapV2PairUsdcWeth9SwapLiveFacts
import Blanc.Composition.UniswapV2PairUsdcWeth9JointF
import Blanc.Composition.UniswapV2PairUsdcWeth9CheckpointF
import Blanc.Lift.Usdc.HistFFacts

/-!
# C6(c): the swap liveness row over the support-free checkpoint (finite twin)

Twin of `UniswapV2PairUsdcWeth9SwapLive.lean`: `pair_usdc_weth9_history_swap_live_finite`
is the swap row with `joint : JointCheckpoint2F …` and the added quiet premise right after
`governance` (the proof uses `pair_usdc_weth9_joint_finite`, which needs it). USDC's
end facts come from `usdc_history_end_coreF`. The pinned callee environments
(`SwapFrontEnvUW`, `SwapBackCalleeEnvUW`) are shared from
`UniswapV2PairUsdcWeth9SwapLiveFacts`.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.UsdcLive

/-- **C6(c), the swap liveness row, support-free** (USDC = token0, WETH9 = token1, both
outputs allowed). Twin of `pair_usdc_weth9_history_swap_live` with `joint :
JointCheckpoint2F …` and the quiet premise after `governance`. -/
theorem pair_usdc_weth9_history_swap_live_finite {pair usdc weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {KU : Usdc.Key → Prop} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2F pair usdc weth KU KW KP st₀ checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (usdcFresh : Usdc.KeysFresh KU (Usdc.historyTouchedKeys usdc trace))
    (wethFresh : Weth9.KeysFresh KW (Weth9.historyTouchedKeys weth trace))
    (governance : Usdc.UsdcGovernance usdc trace)
    (quiet : PairUsdcAllowQuiet pair usdc trace)
    (neverSigner : Blanc.Lift.Token.NeverSigner usdc (Usdc.usdcBookS usdc) trace pair)
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
  obtain ⟨-, finish, K', replayed, reserve0, -, reserve1, -⟩ := pair_usdc_weth9_joint_finite trace
    joint pairFresh usdcFresh wethFresh governance quiet neverSigner factoryInstalled
    factoryNotSystem
  have futureCode := (pair_history_replayed trace joint.weth9.pairCode joint.weth9.pairRep pairFresh).1
  obtain ⟨-, tokens⟩ := replayed.fixed joint.weth9.unlocked
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.weth9.pairCode factoryInstalled
      joint.weth9.pairNonzero factoryNotSystem)
  have token0 : finish.token0 = usdc := tokens.1.trans joint.token0
  have token1 : finish.token1 = weth := tokens.2.1.trans joint.weth9.token
  have usdcWeth : usdc ≠ weth := fun h =>
    joint.weth9.distinct (joint.token0.trans (h.trans joint.weth9.token.symm))
  obtain ⟨wethFuture, -, -⟩ := Blanc.Lift.Weth9.weth9_history_footprint_universe
    trace joint.weth9.wethCode joint.weth9.sumNof joint.weth9.wethFoot wethFresh
  have wethCodePre : pre.state.getCode weth = Weth9.code := by
    rw [state]
    exact Blanc.Composition.Weth9Token.code_eq_of_image wethFuture
  obtain ⟨instF, -, injH, apartH, goodH⟩ := Usdc.usdc_history_end_coreF trace
    (⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩ : Usdc.UsdcHistF usdc KU trace)
  have instPre : Usdc.UsdcInstalled usdc pre.state := by rw [state]; exact instF
  refine ⟨finish, K', replayed, fun {dC cgC g} callee {d0 d1 cg0 cg1} leg1 leg0 front frameGas
    callbackRoom readGas transferGas leg0Room callbackGovernance context conditions => ?_⟩
  have nonstatic : sevm.isStatic = false := context.2
  obtain ⟨unlocked, positive, liquidity0, liquidity1, to0, to1, -⟩ := id conditions
  have depth1 : sevm.depth ≠ 0 := by omega
  have wethNe : weth ≠ sevm.currentTarget := by rw [target]; exact joint.weth9.apart.symm
  have usdcNe : usdc ≠ sevm.currentTarget := by rw [target]; exact joint.apart.symm
  have nonzero : swapAmount0Out sevm ≠ 0 ∨ swapAmount1Out sevm ≠ 0 := by
    rcases positive with h | h
    · exact Or.inl (ne_of_gt h)
    · exact Or.inr (ne_of_gt h)
  have notPreW : sevm.benvStat.rules.isPrecomp weth = false :=
    propext ⟨fun h => absurd h (joint.weth9.wethNotPrecompile _ fork),
      fun h => absurd h Bool.false_ne_true⟩
  have notPreU : sevm.benvStat.rules.isPrecomp usdc = false :=
    propext ⟨fun h => absurd h (joint.usdcNotPrecompile _ fork),
      fun h => absurd h Bool.false_ne_true⟩
  obtain ⟨rep, -⟩ := replayed.at_frame target state
  -- the legs' results are their skeletons up to gas
  have leg0Snd : (swapUsdcLeg0 sevm pre finish cg1 cgC callee.gas).2 = cg0 :=
    (congrArg Prod.snd leg0).symm
  have leg0Fst : (swapUsdcLeg0 sevm pre finish cg1 cgC callee.gas).1 = d0 :=
    (congrArg Prod.fst leg0).symm
  have leg1Snd : (swapWethLeg1 sevm pre finish (usdcLeg0Skel sevm pre finish) cgC callee.gas).2 = cg1 :=
    (congrArg Prod.snd leg1).symm
  have leg1Fst : (swapWethLeg1 sevm pre finish (usdcLeg0Skel sevm pre finish) cgC callee.gas).1 = d1 :=
    (congrArg Prod.fst leg1).symm
  obtain ⟨x0, skel0⟩ : ∃ x, d0 = (usdcLeg0Skel sevm pre finish).withGasLeft x := by
    rw [← leg0Fst]
    exact ⟨_, usdcTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  obtain ⟨x1, skel1⟩ : ∃ x, d1 =
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)).withGasLeft x := by
    rw [← leg1Fst]
    exact ⟨_, wethTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  have legW : swapWethLeg1 sevm pre finish d0 cgC callee.gas = (d1, cg1) := by
    rw [skel0, swapWethLeg1_withGasLeft0]
    exact leg1.symm
  -- USDC at the swap's prefix world
  have prefixStorU : (swapPrefixWorld sevm pre).state.getStor finish.token0 = pre.state.getStor usdc := by
    rw [token0, swapPrefixWorld_getStor _ _ usdcNe]
  have prefixInst : Usdc.UsdcInstalled finish.token0 (swapPrefixWorld sevm pre).state := by
    rw [token0]
    exact usdcInstalled_of instPre (by rw [swapPrefixWorld_getCode]; exact instPre.proxy)
      (by rw [swapPrefixWorld_getCode]; exact instPre.impl)
      (by rw [swapPrefixWorld_getCode]; exact instPre.lib)
      (by rw [swapPrefixWorld_getStor _ _ usdcNe])
  have prefixAdmin : Usdc.adminOf (swapPrefixWorld sevm pre).state finish.token0 =
      Usdc.adminOf pre.state usdc := by
    unfold Usdc.adminOf
    rw [prefixStorU]
  -- the transfer leg's tracked keys: the history's universe and the recipient's row
  have transfer0 : swapAmount0Out sevm ≠ 0 → SwapTransferCallForward sevm (swapPrefixWorld sevm pre)
      (swapLocalsStack sevm finish) getterInitMemory getterInitMemory.size 128 (swapAmount0Out sevm)
      (swapRecipientWord sevm) finish.token0.toB256 0x8d0 cg0
      (swapOptGas (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
        (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) cg1
        (swapFrontCallbackGas sevm pre d0 d1 cgC callee.gas)) d0 := by
    intro amount0
    have fresh := recipientFresh amount0
    have kPair : SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc trace KU)
        [.bal (swapRecipient sevm)] (.bal sevm.currentTarget) := by
      rw [target]; exact Or.inl (Or.inl joint.tracked)
    have core : FootCore (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc trace KU)
        [.bal (swapRecipient sevm)]) ((swapPrefixWorld sevm pre).state.getStor finish.token0) := by
      rw [prefixStorU, state]
      exact ⟨injH.extend fresh, apartH.extend fresh,
        Usdc.Ledger.good_of goodH (fun _ => Nat.mod_lt _ (Nat.two_pow_pos 255)) rfl rfl⟩
    have spec := swapUsdcLeg0_spec (b := pre) (st := finish) (cg1 := cg1) (cgC := cgC)
      (Gc := callee.gas) fork nonstatic depth prefixInst core (by rw [token0]; exact notPreU)
      kPair (Or.inr (List.mem_singleton_self _)) (by rw [prefixAdmin, target]; exact notAdmin)
      (by rw [prefixStorU, target]; exact usdcLive amount0)
      (by
        rw [prefixStorU, Usdc.ledger_bal kPair, target]
        rw [state]
        omega)
      (by rw [leg0Snd]; exact transferGas.1) (leg0Room amount0)
    rw [leg0Snd, leg0Fst, leg1Fst] at spec
    exact spec
  -- USDC's transfer keeps the world off USDC's storage
  obtain ⟨keepStor0, keepCode0, -⟩ : (∀ a, a ≠ usdc →
      d0.state.getStor a = (swapPrefixWorld sevm pre).state.getStor a) ∧
      (∀ a, d0.state.getCode a = (swapPrefixWorld sevm pre).state.getCode a) ∧
      (∀ a, d0.state.bal a = (swapPrefixWorld sevm pre).state.bal a) := by
    rw [← leg0Fst, ← token0, ← tokenMask_toAdr finish.token0]
    exact usdcTransferCall_keeps _ _ _ _ _ _ _ _ _ _
  -- the WETH9 transfer leg
  have prefixCode : (swapPrefixWorld sevm pre).state.getCode finish.token1 = Weth9.code := by
    rw [swapPrefixWorld_getCode, token1, wethCodePre]
  have needGe : swapFrontCallbackGas sevm pre d0 d1 cgC callee.gas ≤
      leg1Need sevm pre finish d0 cgC callee.gas := by
    have e : leg1Skel sevm pre finish d0 = leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish) := by
      rw [skel0, leg1Skel_withGasLeft0]
    have cb := swapFrontCallbackGas_withGasLeft sevm pre d0 (leg1Skel sevm pre finish d0) cgC
      callee.gas x1
    rw [e, ← skel1] at cb
    unfold leg1Need
    rw [e]
    omega
  have room : leg1Used sevm pre finish d0 + gCallStipend ≤
      except64th (leg1Need sevm pre finish d0 cgC callee.gas + leg1Used sevm pre finish d0) := by
    have used : leg1Used sevm pre finish d0 ≤ 53262 := by
      unfold leg1Used
      exact xferUsed_le _ _ _ _ _ _ _ _ _
    unfold except64th
    simp only [gCallStipend]
    omega
  have fits : (swapWethLeg1 sevm pre finish d0 cgC callee.gas).2 < 2 ^ 256 := by
    rw [legW]; exact transferGas.2
  have transfer1 : swapAmount1Out sevm ≠ 0 → SwapTransferCallForward sevm
      (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm pre) d0) (swapLocalsStack sevm finish)
      (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
      (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0).size
      (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) (swapRecipientWord sevm)
      finish.token1.toB256 0x8e1 cg1 (swapFrontCallbackGas sevm pre d0 d1 cgC callee.gas) d1 := by
    intro _
    by_cases amount0 : swapAmount0Out sevm = 0
    · have balance : swapAmount1Out sevm ≤
          (swapPrefixWorld sevm pre).getStorVal finish.token1 (Weth9.balSlot sevm.currentTarget) := by
        rw [token1, swapPrefixWorld_getStorVal _ _ wethNe, target]
        change swapAmount1Out sevm ≤ (pre.state.getStor weth).get (Weth9.balSlot pair)
        rw [state, B256.le_iff_toNat_le_toNat]
        omega
      have spec := swapWethLeg1_spec fork nonstatic depth1 amount0 prefixCode
        (by rw [token1]; exact notPreW) balance fits room
      rw [legW] at spec
      exact spec
    · have roomL : (swapLocalsStack sevm finish).length ≤ 1000 := by
        simp only [swapLocalsStack, swapBodyStack, List.length_cons, List.length_nil]
        omega
      obtain ⟨⟨n1, mem1⟩, -, lower1, upper1, -⟩ :=
        swapFwdOpt_layout (k := 8) (a := swapAmount0Out sevm) (d := d0) fork roomL
          getterInitMemory_ptr burnEntryMemory_sentinel (by decide) (by decide) (by decide)
          transfer0
      change (leg1Ptr sevm d0).toNat < 2 ^ 8 + 2 ^ 161 at upper1
      have balance : swapAmount1Out sevm ≤
          d0.getStorVal finish.token1 (Weth9.balSlot sevm.currentTarget) := by
        change swapAmount1Out sevm ≤ (d0.state.getStor finish.token1).get _
        rw [token1, keepStor0 weth usdcWeth.symm, swapPrefixWorld_getStor _ _ wethNe, target, state,
          B256.le_iff_toNat_le_toNat]
        omega
      have spec := swapWethLeg1_spec_both fork nonstatic depth1 amount0
        (by rw [keepCode0]; exact prefixCode) (by rw [token1]; exact notPreW) mem1.wf lower1
        (by omega) balance fits room
      rw [legW] at spec
      exact spec
  have front' : SwapFrontForwardEnv sevm pre finish d0 d1 dC cg0 cg1 cgC callee.gas :=
    ⟨transfer0, transfer1, front.callback, front.sentry⟩
  -- the memory at the join
  obtain ⟨ptrMem, -, width, -, -⟩ := swapBody_front_exact fork rep unlocked nonstatic nonzero
    liquidity0 liquidity1 to0 to1 guards front'
  -- WETH9's code at the join
  have optCode : (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm pre) d0).state.getCode
      weth = Weth9.code := by
    have base : (swapPrefixWorld sevm pre).state.getCode weth = Weth9.code := by
      rw [swapPrefixWorld_getCode, wethCodePre]
    unfold swapOptWorld
    by_cases amount0 : swapAmount0Out sevm = 0
    · rw [ite_eq_left amount0]
      exact base
    · rw [ite_eq_right amount0]
      exact weth9Code_of_runCompiled (transfer0 amount0).call base
  have transferCode : (swapFrontTransferWorld sevm pre d0 d1).state.getCode weth = Weth9.code := by
    unfold swapFrontTransferWorld
    by_cases amount1 : swapAmount1Out sevm = 0
    · rw [show swapOptWorld (swapAmount1Out sevm) _ d1 = _ from ite_eq_left amount1]
      exact optCode
    · rw [show swapOptWorld (swapAmount1Out sevm) _ d1 = d1 from ite_eq_right amount1]
      exact weth9Code_of_runCompiled (transfer1 amount1).call optCode
  have joinCode : (swapFrontCutWorld sevm pre d0 d1 dC).state.getCode weth = Weth9.code := by
    unfold swapFrontCutWorld
    by_cases empty : swapDataLength sevm = 0
    · rw [ite_eq_left empty]
      exact transferCode
    · rw [ite_eq_right empty]
      exact weth9Code_of_runCompiled (front.callback empty).call (weth9Code_temporal transferCode)
  -- USDC at the join: its runtimes, its implementation slot and its admin word
  have implFixed : Usdc.implSlot ∈ Usdc.fixedSlots := by
    unfold Usdc.fixedSlots; simp only [List.mem_cons, true_or, or_true]
  have adminFixed : Usdc.adminSlot ∈ Usdc.fixedSlots := by
    unfold Usdc.fixedSlots; simp only [List.mem_cons, List.not_mem_nil, true_or, or_true]
  have offPair : ∀ k ∈ Usdc.fixedSlots, k ≠ Usdc.balSlot sevm.currentTarget := by
    intro k hk e
    rw [target] at e
    exact apartH (.bal pair) (Or.inl joint.tracked) (by show Usdc.balSlot pair ∈ _; rw [← e]; exact hk)
  have offTo : swapAmount0Out sevm ≠ 0 → ∀ k ∈ Usdc.fixedSlots,
      k ≠ Usdc.balSlot (swapRecipient sevm) := by
    intro amount0 k hk e
    exact (apartH.extend (recipientFresh amount0)) (.bal (swapRecipient sevm))
      (Or.inr (List.mem_singleton_self _)) (by show Usdc.balSlot _ ∈ _; rw [← e]; exact hk)
  have tokenStor0 : swapAmount0Out sevm ≠ 0 → ∀ k ∈ Usdc.fixedSlots,
      (d0.state.getStor usdc).get k = ((swapPrefixWorld sevm pre).state.getStor usdc).get k := by
    intro amount0 k hk
    rw [← leg0Fst, ← token0, ← tokenMask_toAdr finish.token0]
    exact usdcTransferCall_tokenStor _ _ _ _ _ _ _ _ _ _ getterInitMemory_ptr.wf (by decide)
      (by decide) (offPair k hk) (by rw [swapRecipientWord_toAdr]; exact offTo amount0 k hk)
  have hP : Usdc.UsdcInstalled usdc (swapPrefixWorld sevm pre).state ∧
      Usdc.adminOf (swapPrefixWorld sevm pre).state usdc = Usdc.adminOf pre.state usdc := by
    refine ⟨?_, ?_⟩
    · rw [← token0]; exact prefixInst
    · have h := prefixAdmin; rw [token0] at h; exact h
  have hO : Usdc.UsdcInstalled usdc
        (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm pre) d0).state ∧
      Usdc.adminOf (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm pre) d0).state usdc =
        Usdc.adminOf pre.state usdc := by
    unfold swapOptWorld
    by_cases amount0 : swapAmount0Out sevm = 0
    · rw [ite_eq_left amount0]
      exact hP
    · rw [ite_eq_right amount0]
      refine ⟨usdcInstalled_of_runCompiled (transfer0 amount0).call hP.1
        (by rw [tokenStor0 amount0 _ implFixed]; exact hP.1.slot), ?_⟩
      show ((d0.state.getStor usdc).get Usdc.adminSlot).toAdr = _
      rw [tokenStor0 amount0 _ adminFixed]
      exact hP.2
  have d1Stor : d1.state.getStor usdc =
      (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm pre) d0).state.getStor usdc := by
    have keep := wethTransferCall_keepsStor sevm (leg1World sevm pre (usdcLeg0Skel sevm pre finish))
      (swapLocalsStack sevm finish) (leg1Mem sevm (usdcLeg0Skel sevm pre finish))
      (leg1Ptr sevm (usdcLeg0Skel sevm pre finish)) (swapAmount1Out sevm) (swapRecipientWord sevm)
      finish.token1.toB256 0x8e1
      (leg1Need sevm pre finish (usdcLeg0Skel sevm pre finish) cgC callee.gas +
        leg1Charge sevm pre finish (usdcLeg0Skel sevm pre finish))
      (a := usdc) (by rw [tokenMask_toAdr, token1]; exact usdcWeth)
    have world : (leg1World sevm pre (usdcLeg0Skel sevm pre finish)).state =
        (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm pre) d0).state := by
      unfold leg1World swapOptWorld
      by_cases amount0 : swapAmount0Out sevm = 0
      · rw [ite_eq_left amount0, ite_eq_left amount0]
      · rw [ite_eq_right amount0, ite_eq_right amount0, skel0, withGasLeft_state]
    rw [← world, ← leg1Fst]
    exact keep
  have hT : Usdc.UsdcInstalled usdc (swapFrontTransferWorld sevm pre d0 d1).state ∧
      Usdc.adminOf (swapFrontTransferWorld sevm pre d0 d1).state usdc =
        Usdc.adminOf pre.state usdc := by
    unfold swapFrontTransferWorld
    by_cases amount1 : swapAmount1Out sevm = 0
    · rw [show swapOptWorld (swapAmount1Out sevm) _ d1 = _ from ite_eq_left amount1]
      exact hO
    · rw [show swapOptWorld (swapAmount1Out sevm) _ d1 = d1 from ite_eq_right amount1]
      refine ⟨usdcInstalled_of_runCompiled (transfer1 amount1).call hO.1
        (by rw [d1Stor]; exact hO.1.slot), ?_⟩
      show ((d1.state.getStor usdc).get Usdc.adminSlot).toAdr = _
      rw [d1Stor]
      exact hO.2
  have hJ : Usdc.UsdcInstalled usdc (swapFrontCutWorld sevm pre d0 d1 dC).state ∧
      pair ≠ Usdc.adminOf (swapFrontCutWorld sevm pre d0 d1 dC).state usdc := by
    by_cases empty : swapDataLength sevm = 0
    · unfold swapFrontCutWorld
      rw [ite_eq_left empty, hT.2]
      exact ⟨hT.1, notAdmin⟩
    · obtain ⟨slot, admin⟩ := callbackGovernance empty
      refine ⟨?_, admin⟩
      have run := (front.callback empty).call
      have inst : Usdc.UsdcInstalled usdc (temporalAccountAccessBase
          (swapFrontTransferWorld sevm pre d0 d1)
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& swapRecipientWord sevm).toAdr).state := by
        rw [Lift.temporalAccountAccessBase_state]; exact hT.1
      have h := usdcInstalled_of_runCompiled run inst (by
        unfold swapFrontCutWorld at slot
        rw [ite_eq_right empty] at slot
        exact slot)
      unfold swapFrontCutWorld
      rw [ite_eq_right empty]
      exact h
  -- the callee's join world is the real one up to gas
  obtain ⟨y, hy⟩ : ∃ y, swapFrontCutWorld sevm pre d0 d1 dC =
      (swapFrontCutWorld sevm pre (usdcLeg0Skel sevm pre finish)
        (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC).withGasLeft y := by
    obtain ⟨y0, h0⟩ := swapFrontCutWorld_withGasLeft0 sevm pre (usdcLeg0Skel sevm pre finish) d1 dC x0
    obtain ⟨y1, h1⟩ := swapFrontCutWorld_withGasLeft sevm pre (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC x1
    refine ⟨y0, ?_⟩
    rw [skel0, h0, skel1, h1, withGasLeft_withGasLeft]
  have hM : swapFrontCutMem sevm d0 d1 dC = swapFrontCutMem sevm (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC := by
    rw [skel0, skel1, swapFrontCutMem_withGasLeft0, swapFrontCutMem_withGasLeft]
  have hp : swapFrontPtr sevm d0 d1 = swapFrontPtr sevm (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) := by
    rw [skel0, skel1, swapFrontPtr_withGasLeft0, swapFrontPtr_withGasLeft]
  have Dstate : (swapFrontCutWorld sevm pre (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC).state =
      (swapFrontCutWorld sevm pre d0 d1 dC).state := by
    rw [hy, withGasLeft_state]
  have tokenAdr0 : (swapTokenWord (swapCutWords sevm finish).token0).toAdr = usdc := by
    change (tokenMask finish.token0.toB256).toAdr = usdc
    rw [tokenMask_toAdr, token0]
  have tokenAdr1 : (swapTokenWord (swapCutWords sevm finish).token1).toAdr = weth := by
    change (tokenMask finish.token1.toB256).toAdr = weth
    rw [tokenMask_toAdr, token1]
  -- the USDC query
  obtain ⟨first0, -, skelEq0⟩ := swapUsdcRead0_spec (sevm := sevm)
    (d := swapFrontCutWorld sevm pre (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC)
    (M := swapFrontCutMem sevm (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC)
    (n := (swapFrontCutMem sevm (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC).size)
    (p := swapFrontPtr sevm (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)))
    (w := swapCutWords sevm finish) (ρ := 0x257) (R := [0x022c0d9f]) (G := g + 1)
    (callGas1 := callee.callGas1) fork depth
    (by rw [tokenAdr0, Dstate]; exact hJ.1) (by rw [tokenAdr0]; exact notPreU)
    (by rw [tokenAdr0, Dstate, target]; exact hJ.2)
    (by rw [← hM]; exact ptrMem.wf) (by rw [← hp]; exact width)
    (by simp only [swapCutTail, List.length_cons, List.length_nil]; omega)
    (by rw [← callee.read0]; exact readGas.1) callee.room0
  rw [← callee.read0] at first0 skelEq0
  dsimp only at first0 skelEq0
  -- the WETH9 query, staged over the USDC query's real result
  have d0Code : callee.d0.state.getCode weth = Weth9.code :=
    weth9Code_of_runCompiled first0.call (weth9Code_temporal (by rw [Dstate]; exact joinCode))
  have r1 : swapWethRead1 sevm (swapFrontCutWorld sevm pre (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC)
      (swapFrontCutMem sevm (usdcLeg0Skel sevm pre finish)
        (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC)
      (swapFrontCutMem sevm (usdcLeg0Skel sevm pre finish)
        (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC).size
      (swapFrontPtr sevm (usdcLeg0Skel sevm pre finish)
        (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)))
      (swapCutWords sevm finish) 0x257 [0x022c0d9f] (g + 1) callee.d0 =
      (callee.d1, callee.callGas1) := by
    conv_lhs => rw [skelEq0]
    rw [swapWethRead1_withGasLeft0]
    exact callee.read1.symm
  have second := swapWethRead1_spec (sevm := sevm)
    (d := swapFrontCutWorld sevm pre (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC)
    (M := swapFrontCutMem sevm (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC)
    (n := (swapFrontCutMem sevm (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC).size)
    (p := swapFrontPtr sevm (usdcLeg0Skel sevm pre finish)
      (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)))
    (w := swapCutWords sevm finish) (ρ := 0x257) (R := [0x022c0d9f]) (G := g + 1)
    (d0 := callee.d0) fork depth1 (by rw [tokenAdr1]; exact d0Code) (by rw [tokenAdr1]; exact notPreW)
    (by rw [← hM]; exact ptrMem.wf) (by rw [← hp]; exact width)
    (by simp only [swapCutTail, List.length_cons, List.length_nil]; omega)
    (by rw [r1]; exact readGas.2)
    (by
      have used := balUsed_le sevm callee.d0 (readStack (swapCutWords sevm finish) 0x257
        [0x022c0d9f] callee.d0) (readMem sevm (swapFrontCutMem sevm (usdcLeg0Skel sevm pre finish)
          (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC)
          (swapFrontPtr sevm (usdcLeg0Skel sevm pre finish)
            (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish))) callee.d0)
        (swapFrontPtr sevm (usdcLeg0Skel sevm pre finish)
          (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)))
        (swapCutWords sevm finish).token1
      have need : 64 ≤ readNeed sevm (swapFrontCutMem sevm (usdcLeg0Skel sevm pre finish)
          (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC)
          (swapFrontCutMem sevm (usdcLeg0Skel sevm pre finish)
            (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)) dC).size
          (swapFrontPtr sevm (usdcLeg0Skel sevm pre finish)
            (leg1Skel sevm pre finish (usdcLeg0Skel sevm pre finish)))
          (swapCutWords sevm finish) 0x257 [0x022c0d9f] (g + 1) callee.d0 := by
        unfold readNeed
        omega
      unfold readUsed except64th
      omega)
  rw [r1] at second
  -- the back environment over the real join world
  obtain ⟨env, hgas, hd0, hd1, hpost, hmem⟩ : ∃ env : SwapBackCalleeEnv sevm
      (swapFrontCutWorld sevm pre d0 d1 dC) (swapFrontCutMem sevm d0 d1 dC)
      (swapFrontCutMem sevm d0 d1 dC).size (swapFrontPtr sevm d0 d1) (swapCutWords sevm finish)
      0x257 [0x022c0d9f] (g + 1),
      env.gas = callee.gas ∧ env.d0 = callee.d0 ∧ env.d1 = callee.d1 ∧ env.post = callee.post ∧
        env.memory = callee.memory := by
    rw [hy, hM, hp]
    exact ⟨{ d0 := callee.d0, d1 := callee.d1, callGas0 := callee.callGas0,
              callGas1 := callee.callGas1, first := swapBalanceEnv_withGasLeft y first0,
              second := second, sentries := callee.sentries, unlock := callee.unlock },
      rfl, rfl, rfl, rfl, rfl⟩
  rw [← hd0, ← hd1] at conditions
  rw [← hgas] at front'
  rw [← hgas, ← hpost, ← hmem]
  exact swap_live_of_replayed joint.weth9.pairRep pairFresh futureCode replayed target state codeEq
    fork output representable value size selector guards env front' context conditions

end Blanc.Composition.UniswapV2PairUsdcWeth9
