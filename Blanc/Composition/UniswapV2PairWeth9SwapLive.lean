import Blanc.Composition.UniswapV2PairWeth9SwapLiveFacts

/-!
# C4(b): the history-level swap row with WETH9 as token1, only WETH9 paid out (Appendix A §9)

`pair_weth9_history_swap_live_one` restates `pair_history_swap_live` from the joint checkpoint with
the WETH9 `transfer` callee record (`SwapFrontForwardEnv.transfer1`) and the WETH9 post-callback
`balanceOf` record (`SwapBackCalleeEnv.second`) removed: both are pinned (`_leg`, `callee.read`) to
`swapWethLeg1`/`swapWethRead1`, the runs WETH9's deployed code determines, and discharged by
`swapWethLeg1_spec`/`swapWethRead1_spec`.

Why WETH9 can pay: `pair_weth9_joint`'s end conjunct gives `reserve1 ≤` the Pair's stored WETH9
balance at the history's end, the model's swap guard gives `amount1Out < reserve1`, and the prefix
world differs from the history's end only in the Pair's own storage.  WETH9's code at every later
world of the frame is a code-identity fact (`runCompiled_codePreserve`); no premise is placed on the
callback subtree or on WETH9's answers.

Frame premises (amendment A12): the frame's gas is a word, the callback branch has at least 3,200
gas (room for WETH9's `transfer` under the 63/64 rule with its `SSTORE` sentry), and the second
query's `GAS` word is a word.  Factory premises as `pair_weth9_joint` takes them (A14).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.UniswapV2Pair

/-- The front environment with WETH9 as token1: the existing fields minus `transfer1`. -/
structure SwapFrontEnvW1 (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State) (d0 d1 dC : Devm)
    (cg0 cg1 cgC Gc : Nat) : Prop where
  transfer0 : swapAmount0Out sevm ≠ 0 → SwapTransferCallForward sevm (swapPrefixWorld sevm b)
    (swapLocalsStack sevm st) getterInitMemory getterInitMemory.size 128 (swapAmount0Out sevm)
    (swapRecipientWord sevm) st.token0.toB256 0x8d0 cg0
    (swapOptGas (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
      (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) cg1
      (swapFrontCallbackGas sevm b d0 d1 cgC Gc)) d0
  callback : swapDataLength sevm ≠ 0 → SwapCallbackCallForward sevm
    (swapFrontTransferWorld sevm b d0 d1) (swapLocalsStack sevm st)
    (swapFrontTransferMem sevm d0 d1) (swapFrontPtr sevm d0 d1) (swapRecipientWord sevm)
    (swapAmount0Out sevm) (swapAmount1Out sevm) (swapDataLength sevm) (swapDataStart sevm) cgC Gc dC
  sentry : gCallStipend < swapFrontTransferGas sevm b d0 d1 cg0 cg1 cgC Gc +
    sstoreCost sevm (afterSload sevm b 12) 12 0

/-- The back environment with WETH9 as token1: the token0 `balanceOf` callee kept, the WETH9 one
pinned to what WETH9's code determines (`read`), the store sentries kept. -/
structure SwapBackCalleeEnvW1 (sevm : Sevm) (d : Devm) (M : Mem) (n : Nat) (p : B256)
    (w : SwapCutWords) (ρ : B256) (R : List B256) (G : Nat) where
  d0 : Devm
  d1 : Devm
  callGas0 : Nat
  callGas1 : Nat
  read : (d1, callGas1) = swapWethRead1 sevm d M n p w ρ R G d0
  first : SwapBalanceEnv sevm d M p w.token0 (w.token1 :: w.token0 :: 0 :: 0 :: swapCutTail w ρ R)
    d0 callGas0 (callGas1 + 5 + swapRequestCharge d0 (swapRequestSize n p) p w.token1 83 + 21)
  sentries : SwapUpdateSentries sevm d1 (swapRequestSize (swapRequestSize n p) p) p w.reserve0
    w.reserve1 (swapBalanceWord d0.returnData) (swapBalanceWord d1.returnData)
    (swapEventRunGas G (swapSyncSize (swapRequestSize (swapRequestSize n p) p) p) p
      (swapUnlockCost sevm d1 w.reserve0 w.reserve1 (swapBalanceWord d0.returnData)
        (swapBalanceWord d1.returnData)
        (swapInWord (swapBalanceWord d0.returnData) w.reserve0 w.amount0Out)
        (swapInWord (swapBalanceWord d1.returnData) w.reserve1 w.amount1Out)
        w.amount0Out w.amount1Out w.recipient))
  unlock : gCallStipend < G + 26 + swapUnlockCost sevm d1 w.reserve0 w.reserve1
    (swapBalanceWord d0.returnData) (swapBalanceWord d1.returnData)
    (swapInWord (swapBalanceWord d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out w.recipient

section W1
variable {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256} {w : SwapCutWords} {ρ : B256}
  {R : List B256} {G : Nat}

def SwapBackCalleeEnvW1.gas (env : SwapBackCalleeEnvW1 sevm d M n p w ρ R G) : Nat :=
  env.callGas0 + 5 + swapRequestCharge d n p w.token0 72 + 16

def SwapBackCalleeEnvW1.post (env : SwapBackCalleeEnvW1 sevm d M n p w ρ R G) : Devm :=
  afterSstore sevm (swapLoggedWorld sevm env.d1 w.reserve0 w.reserve1
    (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData)
    (swapInWord (swapBalanceWord env.d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord env.d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out w.recipient) 12 1

def SwapBackCalleeEnvW1.memory (env : SwapBackCalleeEnvW1 sevm d M n p w ρ R G) : Mem :=
  swapEventMemory (swapSyncMemory (swapBalanceReply (swapBalanceReply M p sevm.currentTarget
      env.d0.returnData) p sevm.currentTarget env.d1.returnData) p
      (updateFinalPackedWord sevm env.d1 w.reserve0 w.reserve1
        (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData)))
    p (swapInWord (swapBalanceWord env.d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord env.d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out

end W1

/-! ## Discharging the WETH9 records -/

/-- The back environment with the WETH9 query's record supplied. -/
def SwapBackCalleeEnvW1.toEnv {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {w : SwapCutWords} {ρ : B256} {R : List B256} {G : Nat}
    (env : SwapBackCalleeEnvW1 sevm d M n p w ρ R G)
    (second : SwapBalanceEnv sevm env.d0 (swapBalanceReply M p sevm.currentTarget env.d0.returnData)
      p w.token1 (w.token1 :: w.token0 :: 0 :: swapBalanceWord env.d0.returnData :: swapCutTail w ρ R)
      env.d1 env.callGas1 (swapBackPostGas sevm env.d1 (swapRequestSize (swapRequestSize n p) p) p w
        (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData) G)) :
    SwapBackCalleeEnv sevm d M n p w ρ R G :=
  { d0 := env.d0, d1 := env.d1, callGas0 := env.callGas0, callGas1 := env.callGas1,
    first := env.first, second := second, sentries := env.sentries, unlock := env.unlock }

/-- **C4(b), the swap liveness row with WETH9 as token1 and only WETH9 paid out.**  As
`pair_history_swap_live`, from the joint checkpoint, with the WETH9 `transfer` callee record and the
WETH9 post-callback `balanceOf` record removed: both are WETH9's own runs, pinned by
`swapWethLeg1`/`swapWethRead1`.  What stays is the other token's `balanceOf` callee, the callback, and
the Pair's own gas sentries; the frame premises of A12 are the frame's gas word, the callback
branch's gas lower bound and the second query's gas word. -/
theorem pair_weth9_history_swap_live_one {pair weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop} {KP : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ .one checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress)
    {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) (guards : SwapAbiGuards sevm)
    (onlyWeth : swapAmount0Out sevm = 0)
    (_wethKeys : KeysFresh (historyKeyUniverse weth trace K₀)
      [.bal pair, .bal (swapRecipient sevm), .allow (swapRecipient sevm) pair,
        .allow pair (swapRecipient sevm), .bal (swapAmount1Out sevm).toAdr]) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
      ∀ {d1 dC : Devm} {cg1 cgC g : Nat}
        (callee : SwapBackCalleeEnvW1 sevm
          (swapFrontCutWorld sevm pre pre d1 dC)
          (swapFrontCutMem sevm pre d1 dC)
          (swapFrontCutMem sevm pre d1 dC).size
          (swapFrontPtr sevm pre d1)
          (swapCutWords sevm finish) 0x257 [0x022c0d9f] (g + 1))
        (_leg : (d1, cg1) = swapWethLeg1 sevm pre finish pre cgC callee.gas)
        (_front : SwapFrontEnvW1 sevm pre finish pre
          d1 dC 0
          cg1 cgC callee.gas)
        (_frameGas : swapFrontTransferGas sevm pre pre d1 0 cg1 cgC callee.gas +
          swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166 < 2 ^ 256)
        (_callbackRoom : 3200 ≤ swapFrontCallbackGas sevm pre pre d1 cgC callee.gas)
        (_readGas : callee.callGas1 < 2 ^ 256),
        SwapContextConditions (writerContext sevm []) →
        SwapModelConditions finish (swapAmount0Out sevm) (swapAmount1Out sevm) (swapRecipient sevm)
          (swapBalanceWord callee.d0.returnData) (swapBalanceWord callee.d1.returnData) →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty
            (swapFrontTransferGas sevm pre pre d1
                0 cg1 cgC callee.gas +
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
  obtain ⟨-, finish, K', replayed, reserve, -⟩ := pair_weth9_joint .one trace joint pairFresh
    wethFresh factoryInstalled factoryNotSystem
  have futureCode := (pair_history_replayed trace joint.pairCode joint.pairRep pairFresh).1
  obtain ⟨-, tokens⟩ := replayed.fixed joint.unlocked
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.pairCode factoryInstalled
      joint.pairNonzero factoryNotSystem)
  have token1 : finish.token1 = weth := tokens.2.1.trans joint.token
  obtain ⟨wethFuture, -, -⟩ := Blanc.Lift.Weth9.weth9_history_footprint_universe trace
    joint.wethCode joint.sumNof joint.wethFoot wethFresh
  have wethCodePre : pre.state.getCode weth = Weth9.code := by
    rw [state]
    exact Blanc.Composition.Weth9Token.code_eq_of_image wethFuture
  refine ⟨finish, K', replayed,
    fun {d1 dC cg1 cgC g} callee leg front frameGas callbackRoom readGas context conditions => ?_⟩
  have nonstatic : sevm.isStatic = false := context.2
  obtain ⟨unlocked, positive, liquidity0, liquidity1, to0, to1, -⟩ := id conditions
  have depth : sevm.depth ≠ 0 := depth_of_balanceEnv fork callee.first
  have pairNe : weth ≠ sevm.currentTarget := by
    rw [target]
    exact joint.apart.symm
  have amount1 : swapAmount1Out sevm ≠ 0 := by
    rcases positive with h | h
    · rw [onlyWeth] at h
      exact absurd h (by decide)
    · exact ne_of_gt h
  have nonzero : swapAmount0Out sevm ≠ 0 ∨ swapAmount1Out sevm ≠ 0 := Or.inr amount1
  have notPre : sevm.benvStat.rules.isPrecomp weth = false :=
    propext ⟨fun h => absurd h (joint.wethNotPrecompile _ fork), fun h => absurd h Bool.false_ne_true⟩
  -- the transfer leg
  have prefixCode : (swapPrefixWorld sevm pre).state.getCode finish.token1 = Weth9.code := by
    rw [swapPrefixWorld_getCode, token1, wethCodePre]
  have balance : swapAmount1Out sevm ≤
      (swapPrefixWorld sevm pre).getStorVal finish.token1 (Weth9.balSlot sevm.currentTarget) := by
    rw [token1, swapPrefixWorld_getStorVal _ _ pairNe, target]
    change swapAmount1Out sevm ≤ (pre.state.getStor weth).get (Weth9.balSlot pair)
    rw [state, B256.le_iff_toNat_le_toNat]
    change finish.reserve1.val ≤ _ at reserve
    omega
  have legSnd : (swapWethLeg1 sevm pre finish pre cgC callee.gas).2 = cg1 :=
    (congrArg Prod.snd leg).symm
  have legFst : (swapWethLeg1 sevm pre finish pre cgC callee.gas).1 = d1 :=
    (congrArg Prod.fst leg).symm
  have fits : (swapWethLeg1 sevm pre finish pre cgC callee.gas).2 < 2 ^ 256 := by
    rw [legSnd]
    simp only [swapFrontTransferGas, swapOptGas, onlyWeth, amount1, ↓reduceIte] at frameGas
    omega
  obtain ⟨x, skel⟩ : ∃ x, d1 = (leg1Skel sevm pre finish pre).withGasLeft x := by
    rw [← legFst]
    exact ⟨_, wethTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  have needGe : swapFrontCallbackGas sevm pre pre d1 cgC callee.gas ≤
      leg1Need sevm pre finish pre cgC callee.gas := by
    have cb := swapFrontCallbackGas_withGasLeft sevm pre pre (leg1Skel sevm pre finish pre) cgC
      callee.gas x
    rw [← skel] at cb
    unfold leg1Need
    omega
  have room : leg1Used sevm pre finish pre + gCallStipend ≤
      except64th (leg1Need sevm pre finish pre cgC callee.gas + leg1Used sevm pre finish pre) := by
    have used : leg1Used sevm pre finish pre ≤ 53262 := by
      unfold leg1Used
      exact xferUsed_le _ _ _ _ _ _ _ _ _
    unfold except64th
    simp only [gCallStipend]
    omega
  have transfer1 := swapWethLeg1_spec fork nonstatic depth onlyWeth prefixCode
    (by rw [token1]; exact notPre) balance fits room
  rw [legSnd, legFst] at transfer1
  have front' : SwapFrontForwardEnv sevm pre finish pre d1 dC 0 cg1 cgC callee.gas :=
    ⟨front.transfer0, fun _ => transfer1, front.callback, front.sentry⟩
  -- the memory at the join
  obtain ⟨rep, -⟩ := replayed.at_frame target state
  obtain ⟨ptrMem, -, width, -, -⟩ := swapBody_front_exact fork rep unlocked nonstatic nonzero
    liquidity0 liquidity1 to0 to1 guards front'
  -- WETH9's code at the second query's world
  have optCode : (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm pre) pre).state.getCode
      weth = Weth9.code := by
    unfold swapOptWorld
    rw [ite_eq_left onlyWeth, swapPrefixWorld_getCode, wethCodePre]
  have transferCode : (swapFrontTransferWorld sevm pre pre d1).state.getCode weth = Weth9.code := by
    unfold swapFrontTransferWorld
    rw [show swapOptWorld (swapAmount1Out sevm) _ d1 = d1 from ite_eq_right amount1]
    exact weth9Code_of_runCompiled transfer1.call optCode
  have joinCode : (swapFrontCutWorld sevm pre pre d1 dC).state.getCode weth = Weth9.code := by
    unfold swapFrontCutWorld
    by_cases empty : swapDataLength sevm = 0
    · rw [ite_eq_left empty]
      exact transferCode
    · rw [ite_eq_right empty]
      exact weth9Code_of_runCompiled (front.callback empty).call (weth9Code_temporal transferCode)
  have d0Code : callee.d0.state.getCode weth = Weth9.code :=
    weth9Code_of_runCompiled callee.first.call (weth9Code_temporal joinCode)
  have tokenAdr : (swapTokenWord (swapCutWords sevm finish).token1).toAdr = weth := by
    change (tokenMask finish.token1.toB256).toAdr = weth
    rw [tokenMask_toAdr, token1]
  -- the WETH9 query
  have readSnd : (swapWethRead1 sevm (swapFrontCutWorld sevm pre pre d1 dC)
      (swapFrontCutMem sevm pre d1 dC) (swapFrontCutMem sevm pre d1 dC).size
      (swapFrontPtr sevm pre d1) (swapCutWords sevm finish) 0x257 [0x022c0d9f] (g + 1)
      callee.d0).2 = callee.callGas1 := by
    rw [← callee.read]
  have readFst : (swapWethRead1 sevm (swapFrontCutWorld sevm pre pre d1 dC)
      (swapFrontCutMem sevm pre d1 dC) (swapFrontCutMem sevm pre d1 dC).size
      (swapFrontPtr sevm pre d1) (swapCutWords sevm finish) 0x257 [0x022c0d9f] (g + 1)
      callee.d0).1 = callee.d1 := by
    rw [← callee.read]
  have second := swapWethRead1_spec (d := swapFrontCutWorld sevm pre pre d1 dC)
    (M := swapFrontCutMem sevm pre d1 dC) (p := swapFrontPtr sevm pre d1)
    (w := swapCutWords sevm finish) (ρ := 0x257) (R := [0x022c0d9f])
    (n := (swapFrontCutMem sevm pre d1 dC).size) (G := g + 1) (d0 := callee.d0) fork depth
    (by rw [tokenAdr]; exact d0Code) (by rw [tokenAdr]; exact notPre) ptrMem.wf width
    (by simp only [swapCutTail, List.length_cons, List.length_nil]; omega)
    (by rw [readSnd]; exact readGas)
    (by
      have used := balUsed_le sevm callee.d0 (readStack (swapCutWords sevm finish) 0x257
        [0x022c0d9f] callee.d0) (readMem sevm (swapFrontCutMem sevm pre d1 dC)
        (swapFrontPtr sevm pre d1) callee.d0) (swapFrontPtr sevm pre d1)
        (swapCutWords sevm finish).token1
      have need : 64 ≤ readNeed sevm (swapFrontCutMem sevm pre d1 dC)
          (swapFrontCutMem sevm pre d1 dC).size (swapFrontPtr sevm pre d1)
          (swapCutWords sevm finish) 0x257 [0x022c0d9f] (g + 1) callee.d0 := by
        unfold readNeed
        omega
      unfold readUsed except64th
      omega)
  rw [readSnd, readFst] at second
  exact swap_live_of_replayed joint.pairRep pairFresh futureCode replayed target state codeEq fork
    output representable value size selector guards (callee.toEnv second) front' context conditions

end Blanc.Composition.UniswapV2PairWeth9Joint
