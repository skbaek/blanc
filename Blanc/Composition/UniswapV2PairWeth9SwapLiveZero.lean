import Blanc.Composition.UniswapV2PairWeth9SwapLiveFacts

/-!
# C4(b): the history-level swap row with WETH9 as token0 (both outputs allowed)

`pair_weth9_history_swap_live_zero` restates `pair_history_swap_live` from the joint checkpoint with
the WETH9 `transfer` callee record (`SwapFrontForwardEnv.transfer0`) and the WETH9 post-callback
`balanceOf` record (`SwapBackCalleeEnv.first`) removed: both are pinned (`_leg`, `callee.read`) to
`swapWethLeg0`/`swapWethRead0` and discharged by `swapWethLeg0_spec`/`swapWethRead0_spec`.  WETH9 pays
first, so both outputs may be nonzero: WETH9's leg runs at the swap's prefix world, where the Pair's
WETH9 balance is the history end's, and `pair_weth9_joint` bounds the reserve by it.

What stays: the other token's `transfer` record, the callback, the other token's `balanceOf`
record and the Pair's own gas sentries.  Frame premises (amendment A12): the frame's gas is a word,
the gas the Pair needs after WETH9's `transfer` is at least 3,200 (room for WETH9's `transfer` under
the 63/64 rule with its `SSTORE` sentry), and the first query's `GAS` word is a word.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.UniswapV2Pair

/-- The front environment with WETH9 as token0: the existing fields minus `transfer0`. -/
structure SwapFrontEnvW0 (sevm : Sevm) (b : Devm) (st : UniswapV2Pair.State) (d0 d1 dC : Devm)
    (cg0 cg1 cgC Gc : Nat) : Prop where
  transfer1 : swapAmount1Out sevm ≠ 0 → SwapTransferCallForward sevm
    (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm b) d0) (swapLocalsStack sevm st)
    (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
    (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0).size
    (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) (swapRecipientWord sevm)
    st.token1.toB256 0x8e1 cg1 (swapFrontCallbackGas sevm b d0 d1 cgC Gc) d1
  callback : swapDataLength sevm ≠ 0 → SwapCallbackCallForward sevm
    (swapFrontTransferWorld sevm b d0 d1) (swapLocalsStack sevm st)
    (swapFrontTransferMem sevm d0 d1) (swapFrontPtr sevm d0 d1) (swapRecipientWord sevm)
    (swapAmount0Out sevm) (swapAmount1Out sevm) (swapDataLength sevm) (swapDataStart sevm) cgC Gc dC
  sentry : gCallStipend < swapFrontTransferGas sevm b d0 d1 cg0 cg1 cgC Gc +
    sstoreCost sevm (afterSload sevm b 12) 12 0

/-- The back environment with WETH9 as token0: the WETH9 `balanceOf` callee pinned to what WETH9's
code determines (`read`), the token1 one kept, the store sentries kept. -/
structure SwapBackCalleeEnvW0 (sevm : Sevm) (d : Devm) (M : Mem) (n : Nat) (p : B256)
    (w : SwapCutWords) (ρ : B256) (R : List B256) (G : Nat) where
  d0 : Devm
  d1 : Devm
  callGas0 : Nat
  callGas1 : Nat
  read : (d0, callGas0) = swapWethRead0 sevm d M n p w ρ R callGas1
  second : SwapBalanceEnv sevm d0 (swapBalanceReply M p sevm.currentTarget d0.returnData) p
    w.token1 (w.token1 :: w.token0 :: 0 :: swapBalanceWord d0.returnData :: swapCutTail w ρ R) d1
    callGas1 (swapBackPostGas sevm d1 (swapRequestSize (swapRequestSize n p) p) p w
      (swapBalanceWord d0.returnData) (swapBalanceWord d1.returnData) G)
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

section W0
variable {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256} {w : SwapCutWords} {ρ : B256}
  {R : List B256} {G : Nat}

def SwapBackCalleeEnvW0.gas (env : SwapBackCalleeEnvW0 sevm d M n p w ρ R G) : Nat :=
  env.callGas0 + 5 + swapRequestCharge d n p w.token0 72 + 16

def SwapBackCalleeEnvW0.post (env : SwapBackCalleeEnvW0 sevm d M n p w ρ R G) : Devm :=
  afterSstore sevm (swapLoggedWorld sevm env.d1 w.reserve0 w.reserve1
    (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData)
    (swapInWord (swapBalanceWord env.d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord env.d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out w.recipient) 12 1

def SwapBackCalleeEnvW0.memory (env : SwapBackCalleeEnvW0 sevm d M n p w ρ R G) : Mem :=
  swapEventMemory (swapSyncMemory (swapBalanceReply (swapBalanceReply M p sevm.currentTarget
      env.d0.returnData) p sevm.currentTarget env.d1.returnData) p
      (updateFinalPackedWord sevm env.d1 w.reserve0 w.reserve1
        (swapBalanceWord env.d0.returnData) (swapBalanceWord env.d1.returnData)))
    p (swapInWord (swapBalanceWord env.d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord env.d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out

/-- The back environment with the WETH9 query's record supplied. -/
def SwapBackCalleeEnvW0.toEnv (env : SwapBackCalleeEnvW0 sevm d M n p w ρ R G)
    (first : SwapBalanceEnv sevm d M p w.token0 (w.token1 :: w.token0 :: 0 :: 0 :: swapCutTail w ρ R)
      env.d0 env.callGas0
      (env.callGas1 + 5 + swapRequestCharge env.d0 (swapRequestSize n p) p w.token1 83 + 21)) :
    SwapBackCalleeEnv sevm d M n p w ρ R G :=
  { d0 := env.d0, d1 := env.d1, callGas0 := env.callGas0, callGas1 := env.callGas1,
    first := first, second := env.second, sentries := env.sentries, unlock := env.unlock }

end W0

/-- The back environment carried to a gas-shifted join world: the WETH9 query reads the join world
only off non-gas fields (`swapWethRead0_withGasLeft`), as does the staging charge. -/
theorem SwapBackCalleeEnvW0.transport {sevm : Sevm} {d d' : Devm} {M M' : Mem} {n n' : Nat}
    {p p' : B256} {w : SwapCutWords} {ρ : B256} {R : List B256} {G : Nat}
    (hd : ∃ y, d' = d.withGasLeft y) (hM : M' = M) (hn : n' = n) (hp : p' = p)
    (env : SwapBackCalleeEnvW0 sevm d M n p w ρ R G) :
    ∃ env' : SwapBackCalleeEnvW0 sevm d' M' n' p' w ρ R G,
      env'.gas = env.gas ∧ env'.d0 = env.d0 ∧ env'.d1 = env.d1 ∧ env'.callGas0 = env.callGas0 ∧
      env'.post = env.post ∧ env'.memory = env.memory := by
  obtain ⟨y, rfl⟩ := hd
  subst hM hn hp
  exact ⟨{ d0 := env.d0, d1 := env.d1, callGas0 := env.callGas0, callGas1 := env.callGas1,
            read := by rw [swapWethRead0_withGasLeft]; exact env.read, second := env.second,
            sentries := env.sentries, unlock := env.unlock }, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **C4(b), the swap liveness row with WETH9 as token0** (both outputs allowed; WETH9 pays first).
As `pair_history_swap_live`, from the joint checkpoint, with the WETH9 `transfer` callee record and the
WETH9 post-callback `balanceOf` record removed: both are WETH9's own runs, pinned by
`swapWethLeg0`/`swapWethRead0`.  What stays is the other token's `transfer` and `balanceOf` callees,
the callback, and the Pair's own gas sentries; the frame premises of A12 are the frame's gas word,
the gas lower bound after WETH9's `transfer` (only when it is taken) and the first query's gas
word. -/
theorem pair_weth9_history_swap_live_zero {pair weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop} {KP : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ .zero checkpoint.state)
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
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) (guards : SwapAbiGuards sevm) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
      ∀ {d1 dC : Devm} {cg1 cgC g : Nat}
        (callee : SwapBackCalleeEnvW0 sevm
          (swapFrontCutWorld sevm pre (leg0Skel sevm pre finish) d1 dC)
          (swapFrontCutMem sevm (leg0Skel sevm pre finish) d1 dC)
          (swapFrontCutMem sevm (leg0Skel sevm pre finish) d1 dC).size
          (swapFrontPtr sevm (leg0Skel sevm pre finish) d1)
          (swapCutWords sevm finish) 0x257 [0x022c0d9f] (g + 1))
        {d0 : Devm} {cg0 : Nat}
        (_leg : (d0, cg0) = swapWethLeg0 sevm pre finish d1 cg1 cgC callee.gas)
        (_front : SwapFrontEnvW0 sevm pre finish d0 d1 dC cg0 cg1 cgC callee.gas)
        (_frameGas : swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
          swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166 < 2 ^ 256)
        (_transferRoom : swapAmount0Out sevm ≠ 0 → 3200 ≤
          swapOptGas (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
            (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) cg1
            (swapFrontCallbackGas sevm pre d0 d1 cgC callee.gas))
        (_readGas : callee.callGas0 < 2 ^ 256),
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
  obtain ⟨-, finish, K', replayed, reserve, -⟩ := pair_weth9_joint .zero trace joint pairFresh
    wethFresh factoryInstalled factoryNotSystem
  have futureCode := (pair_history_replayed trace joint.pairCode joint.pairRep pairFresh).1
  obtain ⟨-, tokens⟩ := replayed.fixed joint.unlocked
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.pairCode factoryInstalled
      joint.pairNonzero factoryNotSystem)
  have token0 : finish.token0 = weth := tokens.1.trans joint.token
  obtain ⟨wethFuture, -, -⟩ := Blanc.Lift.Weth9.weth9_history_footprint_universe trace
    joint.wethCode joint.sumNof joint.wethFoot wethFresh
  have wethCodePre : pre.state.getCode weth = Weth9.code := by
    rw [state]
    exact Blanc.Composition.Weth9Token.code_eq_of_image wethFuture
  refine ⟨finish, K', replayed, fun {d1 dC cg1 cgC g} callee {d0 cg0} leg front frameGas
    transferRoom readGas context conditions => ?_⟩
  have nonstatic : sevm.isStatic = false := context.2
  obtain ⟨unlocked, positive, liquidity0, liquidity1, to0, to1, -⟩ := id conditions
  have depth : sevm.depth ≠ 0 := depth_of_balanceEnv fork callee.second
  have pairNe : weth ≠ sevm.currentTarget := by
    rw [target]
    exact joint.apart.symm
  have nonzero : swapAmount0Out sevm ≠ 0 ∨ swapAmount1Out sevm ≠ 0 := by
    rcases positive with h | h
    · exact Or.inl (ne_of_gt h)
    · exact Or.inr (ne_of_gt h)
  have notPre : sevm.benvStat.rules.isPrecomp weth = (false = true) :=
    propext ⟨fun h => absurd h (joint.wethNotPrecompile _ fork), fun h => absurd h Bool.false_ne_true⟩
  -- the transfer leg
  have prefixCode : (swapPrefixWorld sevm pre).state.getCode finish.token0 = Weth9.code := by
    rw [swapPrefixWorld_getCode, token0, wethCodePre]
  have balance : swapAmount0Out sevm ≤
      (swapPrefixWorld sevm pre).getStorVal finish.token0 (Weth9.balSlot sevm.currentTarget) := by
    rw [token0, swapPrefixWorld_getStorVal _ _ pairNe, target]
    change swapAmount0Out sevm ≤ (pre.state.getStor weth).get (Weth9.balSlot pair)
    rw [state, B256.le_iff_toNat_le_toNat]
    change finish.reserve0.val ≤ _ at reserve
    omega
  have legSnd : (swapWethLeg0 sevm pre finish d1 cg1 cgC callee.gas).2 = cg0 :=
    (congrArg Prod.snd leg).symm
  have legFst : (swapWethLeg0 sevm pre finish d1 cg1 cgC callee.gas).1 = d0 :=
    (congrArg Prod.fst leg).symm
  obtain ⟨x, skel⟩ : ∃ x, d0 = (leg0Skel sevm pre finish).withGasLeft x := by
    rw [← legFst]
    exact ⟨_, wethTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  -- carry the callee from the skeleton's join world to the real one
  obtain ⟨callee', hgas, hd0, hd1, hcg0, hpost, hmem⟩ := callee.transport
    (d' := swapFrontCutWorld sevm pre d0 d1 dC) (M' := swapFrontCutMem sevm d0 d1 dC)
    (n' := (swapFrontCutMem sevm d0 d1 dC).size) (p' := swapFrontPtr sevm d0 d1)
    (by rw [skel]; exact swapFrontCutWorld_withGasLeft0 sevm pre _ d1 dC x)
    (by rw [skel, swapFrontCutMem_withGasLeft0]) (by rw [skel, swapFrontCutMem_withGasLeft0])
    (by rw [skel, swapFrontPtr_withGasLeft0])
  rw [← hgas] at leg front frameGas transferRoom legSnd legFst
  rw [← hd0, ← hd1] at conditions
  rw [← hcg0] at readGas
  rw [← hgas, ← hpost, ← hmem]
  clear hgas hd0 hd1 hcg0 hpost hmem
  have transfer0 : swapAmount0Out sevm ≠ 0 → SwapTransferCallForward sevm (swapPrefixWorld sevm pre)
      (swapLocalsStack sevm finish) getterInitMemory getterInitMemory.size 128 (swapAmount0Out sevm)
      (swapRecipientWord sevm) finish.token0.toB256 0x8d0 cg0
      (swapOptGas (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
        (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) cg1
        (swapFrontCallbackGas sevm pre d0 d1 cgC callee'.gas)) d0 := by
    intro amount0
    have fits : (swapWethLeg0 sevm pre finish d1 cg1 cgC callee'.gas).2 < 2 ^ 256 := by
      rw [legSnd]
      simp only [swapFrontTransferGas, swapOptGas, amount0, ↓reduceIte] at frameGas
      omega
    have nextEq := leg0Next_withGasLeft sevm pre d1 cg1 cgC callee'.gas (leg0Skel sevm pre finish) x
    rw [← skel] at nextEq
    have room : leg0Used sevm pre finish + gCallStipend ≤
        except64th (leg0Need sevm pre finish d1 cg1 cgC callee'.gas + leg0Used sevm pre finish) := by
      have used : leg0Used sevm pre finish ≤ 53262 := by
        unfold leg0Used
        exact xferUsed_le _ _ _ _ _ _ _ _ _
      have bound := transferRoom amount0
      change 3200 ≤ leg0Next sevm pre d1 cg1 cgC callee'.gas d0 at bound
      unfold leg0Need except64th
      simp only [gCallStipend]
      omega
    have spec := swapWethLeg0_spec fork nonstatic depth prefixCode
      (by rw [token0]; exact notPre) balance fits room
    rw [legSnd, legFst] at spec
    exact spec
  have front' : SwapFrontForwardEnv sevm pre finish d0 d1 dC cg0 cg1 cgC callee'.gas :=
    ⟨transfer0, front.transfer1, front.callback, front.sentry⟩
  -- the memory at the join
  obtain ⟨rep, -⟩ := replayed.at_frame target state
  obtain ⟨ptrMem, -, width, -, -⟩ := swapBody_front_exact fork rep unlocked nonstatic nonzero
    liquidity0 liquidity1 to0 to1 guards front'
  -- WETH9's code at the first query's world
  have optCode : (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm pre) d0).state.getCode
      weth = Weth9.code := by
    unfold swapOptWorld
    by_cases amount0 : swapAmount0Out sevm = 0
    · rw [ite_eq_left amount0, swapPrefixWorld_getCode, wethCodePre]
    · rw [ite_eq_right amount0]
      have base : (swapPrefixWorld sevm pre).state.getCode weth = Weth9.code := by
        rw [swapPrefixWorld_getCode, wethCodePre]
      exact weth9Code_of_runCompiled (transfer0 amount0).call base
  have transferCode : (swapFrontTransferWorld sevm pre d0 d1).state.getCode weth = Weth9.code := by
    unfold swapFrontTransferWorld
    by_cases amount1 : swapAmount1Out sevm = 0
    · rw [show swapOptWorld (swapAmount1Out sevm) _ d1 = _ from ite_eq_left amount1]
      exact optCode
    · rw [show swapOptWorld (swapAmount1Out sevm) _ d1 = d1 from ite_eq_right amount1]
      exact weth9Code_of_runCompiled (front.transfer1 amount1).call optCode
  have joinCode : (swapFrontCutWorld sevm pre d0 d1 dC).state.getCode weth = Weth9.code := by
    unfold swapFrontCutWorld
    by_cases empty : swapDataLength sevm = 0
    · rw [ite_eq_left empty]
      exact transferCode
    · rw [ite_eq_right empty]
      exact weth9Code_of_runCompiled (front.callback empty).call (weth9Code_temporal transferCode)
  have tokenAdr : (swapTokenWord (swapCutWords sevm finish).token0).toAdr = weth := by
    change (tokenMask finish.token0.toB256).toAdr = weth
    rw [tokenMask_toAdr, token0]
  -- the WETH9 query
  have readSnd : (swapWethRead0 sevm (swapFrontCutWorld sevm pre d0 d1 dC)
      (swapFrontCutMem sevm d0 d1 dC) (swapFrontCutMem sevm d0 d1 dC).size
      (swapFrontPtr sevm d0 d1) (swapCutWords sevm finish) 0x257 [0x022c0d9f]
      callee'.callGas1).2 = callee'.callGas0 := by
    rw [← callee'.read]
  have readFst : (swapWethRead0 sevm (swapFrontCutWorld sevm pre d0 d1 dC)
      (swapFrontCutMem sevm d0 d1 dC) (swapFrontCutMem sevm d0 d1 dC).size
      (swapFrontPtr sevm d0 d1) (swapCutWords sevm finish) 0x257 [0x022c0d9f]
      callee'.callGas1).1 = callee'.d0 := by
    rw [← callee'.read]
  have first := (swapWethRead0_spec (d := swapFrontCutWorld sevm pre d0 d1 dC)
    (M := swapFrontCutMem sevm d0 d1 dC) (p := swapFrontPtr sevm d0 d1)
    (w := swapCutWords sevm finish) (ρ := 0x257) (R := [0x022c0d9f])
    (n := (swapFrontCutMem sevm d0 d1 dC).size) (callGas1 := callee'.callGas1) fork depth
    (by rw [tokenAdr]; exact joinCode) (by rw [tokenAdr]; exact notPre) ptrMem.wf width
    (by simp only [swapCutTail, List.length_cons, List.length_nil]; omega)
    (by rw [readSnd]; exact readGas)
    (by
      have used := balUsed_le sevm (swapFrontCutWorld sevm pre d0 d1 dC)
        (read0Stack (swapCutWords sevm finish) 0x257 [0x022c0d9f]) (swapFrontCutMem sevm d0 d1 dC)
        (swapFrontPtr sevm d0 d1) (swapCutWords sevm finish).token0
      unfold read0Need except64th
      omega)).1
  rw [readSnd, readFst] at first
  exact swap_live_of_replayed joint.pairRep pairFresh futureCode replayed target state codeEq fork
    output representable value size selector guards (callee'.toEnv first) front' context conditions

end Blanc.Composition.UniswapV2PairWeth9Joint
