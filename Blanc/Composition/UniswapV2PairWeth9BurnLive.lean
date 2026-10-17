import Blanc.Composition.UniswapV2PairWeth9BurnEnv
import Blanc.Composition.UniswapV2PairWeth9SyncLive

/-!
# C4(b): the burn liveness row with WETH9 = token0 (U8d)

`pair_weth9_history_burn_live_zero` restates `pair_history_burn_live` from the joint checkpoint with
WETH9's three records removed (`BurnEnvW0`: pinned to `burnWethRead0`, `burnWethLeg0`,
`burnWethFinal0`).  Inside the model's acceptance the records are rebuilt:

* the initial query and the final query are code-only: WETH9's code at the token the Pair loads
  (history), carried to each staged world (`WethKeeps`, `runCompiled_codePreserve`);
* the transfer's balance condition `amount0 ≤` the Pair's WETH9 balance at the suffix world: the
  priced `amount0` word is at most the initial answer (`burnFee_amount0_le`), which is the Pair's
  WETH9 balance at the query's world, unchanged to the suffix world since the Pair's own steps write
  only its storage and the other two queries are `STATICCALL`s (`burnBodyWorld_keeps`);
* the final query's memory facts come from the suffix layout (`burnSuffix_layout`).

The body is `pair_history_burn_live`'s, at the history's own replay.  The frame's call depth and the
legs' gas sentries (`BurnEnvW0.WethSentries`) are premises.

The WETH9 = token1 row needs X-leg quiescence (U8c) and is not here.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.UniswapV2Pair

/-- **The gas sentries of WETH9's three Burn legs**: each leg's call gas a word, and room for
WETH9's run under the 63/64 rule (with the `transfer`'s `SSTORE` stipend). -/
structure BurnEnvW0.WethSentries {sevm : Sevm} {b : Devm} {g : Nat} (env : BurnEnvW0 sevm b g) :
    Prop where
  fitsRead : env.initial.callGas0 < 2 ^ 256
  roomRead : balUsed sevm (burnRead0World sevm b) (burnRead0Stack sevm b [0x89afcb44])
      getterInitMemory 128 (burnT0 sevm b) ≤
    except64th (burnRead0Need sevm b env.initial.callGas1 (wethBalanceSkel sevm
        (burnRead0World sevm b) (burnRead0Stack sevm b [0x89afcb44]) getterInitMemory 128
        (burnT0 sevm b)) +
      balUsed sevm (burnRead0World sevm b) (burnRead0Stack sevm b [0x89afcb44]) getterInitMemory 128
        (burnT0 sevm b))
  fitsLeg : env.back.callGas0 < 2 ^ 256
  roomLeg : burnLeg0Used sevm (burnBodyWorld sevm b env.d0 env.d1 env.dF)
      (burnBodyWorld sevm b env.d0 env.d1 env.dF).memory 128
      (burnBodyWords sevm b env.d0 env.d1 env.dF) [0x89afcb44] + gCallStipend ≤
    except64th (burnLeg0Need sevm (burnBodyWorld sevm b env.d0 env.d1 env.dF)
        (burnBodyWorld sevm b env.d0 env.d1 env.dF).memory 128
        (burnBodyWords sevm b env.d0 env.d1 env.dF) [0x89afcb44] env.back.callGas1 +
      burnLeg0Used sevm (burnBodyWorld sevm b env.d0 env.d1 env.dF)
        (burnBodyWorld sevm b env.d0 env.d1 env.dF).memory 128
        (burnBodyWords sevm b env.d0 env.d1 env.dF) [0x89afcb44])
  fitsFinal : env.back.balanceGas0 < 2 ^ 256
  roomFinal : balUsed sevm env.back.d1
      ((burnBodyWords sevm b env.d0 env.d1 env.dF).locals
        (burnBodyWords sevm b env.d0 env.d1 env.dF).balance1
        (burnBodyWords sevm b env.d0 env.d1 env.dF).balance0 [0x89afcb44])
      (burnSuffixMem2 (burnBodyWorld sevm b env.d0 env.d1 env.dF).memory 128
        (burnBodyWords sevm b env.d0 env.d1 env.dF) env.back.d0 env.back.d1)
      (burnSuffixPtr 128 env.back.d0 env.back.d1) (burnBodyWords sevm b env.d0 env.d1 env.dF).token0 ≤
    except64th (burnFinal0Need (burnBodyWorld sevm b env.d0 env.d1 env.dF).memory 128
        (burnBodyWords sevm b env.d0 env.d1 env.dF) env.back.d0 env.back.d1 env.back.balanceGas1
        (wethBalanceSkel sevm env.back.d1
          ((burnBodyWords sevm b env.d0 env.d1 env.dF).locals
            (burnBodyWords sevm b env.d0 env.d1 env.dF).balance1
            (burnBodyWords sevm b env.d0 env.d1 env.dF).balance0 [0x89afcb44])
          (burnSuffixMem2 (burnBodyWorld sevm b env.d0 env.d1 env.dF).memory 128
            (burnBodyWords sevm b env.d0 env.d1 env.dF) env.back.d0 env.back.d1)
          (burnSuffixPtr 128 env.back.d0 env.back.d1)
          (burnBodyWords sevm b env.d0 env.d1 env.dF).token0) +
      balUsed sevm env.back.d1
        ((burnBodyWords sevm b env.d0 env.d1 env.dF).locals
          (burnBodyWords sevm b env.d0 env.d1 env.dF).balance1
          (burnBodyWords sevm b env.d0 env.d1 env.dF).balance0 [0x89afcb44])
        (burnSuffixMem2 (burnBodyWorld sevm b env.d0 env.d1 env.dF).memory 128
          (burnBodyWords sevm b env.d0 env.d1 env.dF) env.back.d0 env.back.d1)
        (burnSuffixPtr 128 env.back.d0 env.back.d1)
        (burnBodyWords sevm b env.d0 env.d1 env.dF).token0)

theorem burnReservedWorld_slot {sevm : Sevm} {pre : Devm} {k : B256} (hk : (12 : B256) ≠ k) :
    (burnReservedWorld sevm pre).getStorVal sevm.currentTarget k =
      pre.getStorVal sevm.currentTarget k := by
  change (Devm.getStor (burnReservedWorld sevm pre) sevm.currentTarget).get k =
    (Devm.getStor pre sevm.currentTarget).get k
  unfold burnReservedWorld burnLockedWorld
  rw [afterSload_getStor, afterSstore_getStor_self, Stor.get_set_ne _ hk, afterSload_getStor]

/-- **C4(b), the burn liveness row with WETH9 as token0.**  As `pair_history_burn_live`, from the
joint checkpoint, with WETH9's initial query, transfer and final query removed (pinned in `callee`
to the legs WETH9's code determines).  What stays is token1's records, the factory record, the
Pair's charges and sentries, the LP rows' HASH-T, the frame's call depth and the legs' gas
sentries. -/
theorem pair_weth9_history_burn_live_zero {pair weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop} {KP : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ .zero checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44) (depth : sevm.depth ≠ 0)
    (callee : BurnEnvW0 sevm pre g) (sentries : callee.WethSentries)
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace KP)
      (lpMintTouched sevm.currentTarget ++ lpMintTouched callee.feeTo)) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final0 →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final1 →
        (runTyped finish (writerContext sevm []) (.burn (Sevm.dataWord sevm 4).toAdr)
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
  obtain ⟨futureCode, finish, K', replayed⟩ := pair_history_replayed trace joint.pairCode
    joint.pairRep pairFresh
  refine ⟨finish, K', replayed,
    fun transcript returndata answer0 answer1 answerFee final0 final1 accepted => ?_⟩
  have conditions := runTyped_burn_conditions accepted
  rw [answer0, answer1, answerFee, final0, final1] at conditions
  have hist : WriterRep (pairHistoryUniverse pair trace KP) (checkpoint.state.getStor pair) st₀ :=
    joint.pairRep.extend pairFresh
  obtain ⟨rep, inside⟩ := replayed.at_frame target state
  let rows := lpMintTouched sevm.currentTarget ++ lpMintTouched callee.feeTo
  have inj := hist.inj.extend rowsFresh
  have apart := hist.apart.extend rowsFresh
  have rowIn : ∀ k ∈ rows, WriterExtend (pairHistoryUniverse pair trace KP) rows k :=
    fun k member => Or.inr member
  have ownRow : WriterExtend (pairHistoryUniverse pair trace KP) rows
      (.balance sevm.currentTarget) :=
    rowIn _ (by simp only [rows, lpMintTouched, List.mem_append, List.mem_singleton, true_or])
  have feeRow : WriterExtend (pairHistoryUniverse pair trace KP) rows (.balance callee.feeTo) :=
    rowIn _ (by simp only [rows, lpMintTouched, List.mem_append, List.mem_singleton, or_true])
  have subK : ∀ k, K' k → WriterExtend (pairHistoryUniverse pair trace KP) rows k :=
    fun k tracked => Or.inl (inside k tracked)
  have ownFresh : WriterFreshKeys K' (lpMintTouched sevm.currentTarget) :=
    Blanc.SlotFootprint.FreshKeys.of_universe inj apart subK
      (fun k member => by rw [List.mem_singleton.mp member]; exact ownRow)
  have repOwn := rep.extend ownFresh
  have subOwn : ∀ k, WriterExtend K' (lpMintTouched sevm.currentTarget) k →
      WriterExtend (pairHistoryUniverse pair trace KP) rows k := by
    intro k member
    rcases member with old | row
    · exact subK k old
    · rw [List.mem_singleton.mp row]; exact ownRow
  have tracked : WriterExtend K' (lpMintTouched sevm.currentTarget) (.balance sevm.currentTarget) :=
    Or.inr (List.mem_singleton_self _)
  have guards : BurnForwardGuards (WriterExtend K' (lpMintTouched sevm.currentTarget)) finish sevm
      pre callee.d0 callee.d1 callee.dF callee.back.e0 callee.back.e1 :=
    burnGuards_of_model callee.initial.long1 repOwn inj apart subOwn feeRow conditions
  have guardsCopy := guards
  obtain ⟨-, nonstatic, ⟨fee, feeAccepted, amount0, amount1, burnPost, events, priced, positive0,
    positive1, burned⟩, fresh, -, -⟩ := guardsCopy
  -- WETH9 on token0, from the history
  obtain ⟨code, token, -, -⟩ := pair_weth9_frame .zero trace joint pairFresh wethFresh
    factoryInstalled factoryNotSystem state
  have ne : sevm.currentTarget ≠ weth := target ▸ joint.apart
  have tok : (burnT0 sevm pre).toAdr = weth := by
    unfold burnT0
    rw [burnAddrMask_and, toAdr_toB256, burnReservedWorld_slot (by decide), target]
    exact token
  have keeps0 := burnRead0World_keeps sevm pre ne
  have np : sevm.benvStat.rules.isPrecomp (burnT0 sevm pre).toAdr = (false = true) := by
    rw [tok]
    exact notPrecompile_of_joint joint fork
  -- the initial query
  have hr : (burnWethRead0 sevm pre [0x89afcb44] callee.initial.callGas1).1 = callee.d0 :=
    (congrArg Prod.fst callee.initial.read).symm
  have hr' : (burnWethRead0 sevm pre [0x89afcb44] callee.initial.callGas1).2 =
      callee.initial.callGas0 := (congrArg Prod.snd callee.initial.read).symm
  have specR := burnWethRead0_spec (R := [0x89afcb44]) fork depth
    (by rw [tok]; exact keeps0.1.trans code) np (by decide)
    (by rw [hr']; exact sentries.fitsRead) sentries.roomRead
  dsimp only at specR
  rw [hr, hr'] at specR
  obtain ⟨code0, call0, success0, long0, returnedGas0, reply0⟩ := specR
  -- the locked state at `d1` (as `burnPc0_exact`)
  obtain ⟨bound0, bound1⟩ := burnR_bounds sevm pre
  have stor0 := compiled_staticcall_stor fork call0
  have stor1 := compiled_staticcall_stor fork callee.initial.call1
  have d1Rep : WriterRep (WriterExtend K' (lpMintTouched sevm.currentTarget))
      (callee.d1.getStor sevm.currentTarget) { finish with unlocked := 0 } := by
    have same : callee.d1.getStor sevm.currentTarget =
        (burnLockedWorld sevm pre).getStor sevm.currentTarget :=
      calc callee.d1.getStor sevm.currentTarget
          = (burnCall1World sevm pre callee.d0).getStor sevm.currentTarget := stor1 _
        _ = callee.d0.getStor sevm.currentTarget := by
          simp only [burnCall1World, Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
        _ = (burnCall0World sevm pre).getStor sevm.currentTarget := stor0 _
        _ = (burnTokensWorld sevm (burnReservedWorld sevm pre)).getStor sevm.currentTarget := by
          simp only [burnCall0World, Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
        _ = (burnLockedWorld sevm pre).getStor sevm.currentTarget := by
          rw [burnTokensWorld, afterSload_getStor, afterSload_getStor, burnReservedWorld,
            afterSload_getStor]
    rw [same]
    exact repOwn.burn_locked_world
  have req0 := balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget
  have reply0m := balanceReplyMemory_ptr callee.d0.returnData req0
  have reply1 : PtrMem 128 192 (burnMem2 sevm callee.d0 callee.d1) :=
    balanceReplyMemory_ptr callee.d1.returnData (balanceRequestMemory_ptr reply0m sevm.currentTarget)
  obtain ⟨nonzero0, nonzero1, -⟩ := burnFeePricing_exact
    (len := callee.d1.returnData.length.toB256) (discarded := 0) fork reply1 (by decide) d1Rep
    tracked nonstatic bound0 bound1 callee.fee feeAccepted fresh priced positive0 positive1 burned
  have amountLe := burnFee_amount0_le fork reply1 (by decide) d1Rep tracked nonstatic bound0 bound1
    callee.fee feeAccepted fresh priced burned
  -- the suffix world's memory (as `burnPc0_exact`)
  have feeMem : PtrMem 128 192
      (feeReplyMemory (feeBurnMemory (burnMem2 sevm callee.d0 callee.d1) sevm.currentTarget)
        callee.dF.returnData) :=
    feeReplyMemory_ptr callee.dF.returnData
      (feeRequestMemory_ptr (feeBurnMemory_ptr reply1 sevm.currentTarget))
  have feeMachine := mintFeePost_machine (sevm := sevm) (b := feeKLastWorld sevm callee.dF)
    (R := burnFeeLocalsAt sevm callee.d1 (burnMem2 sevm callee.d0 callee.d1) (burnB0 callee.d0)
      (burnT1 sevm pre) (burnT0 sevm pre) (burnR1 sevm pre) (burnR0 sevm pre)
      (burnRecipientWord sevm) 0x053d [0x89afcb44])
    (K := feeKLastWord sevm callee.dF) (w := Bytes.toB256 (callee.dF.returnData.take 32))
    (r0 := burnR0 sevm pre) (r1 := burnR1 sevm pre) (G := 0) feeMem
  have pricedMem : PtrMem 128 192 (burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF).memory := by
    have image := lpMintMemory_ptr (lpMintScratch_ptr feeMachine.2 sevm.currentTarget.toB256)
      sevm.currentTarget.toB256 (feeBurnLiquidity sevm callee.d1)
    rw [burnBodyWorld_def]
    simpa only [burnPricedWorld, burnFeeWorld, lpBurnPost, lpBurnBalancePost, lpBurnSupplyPost,
      St.memory, lpMintMemory] using image
  have pricedSentinel :
      memWord (burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF).memory 96 = 0 := by
    rw [burnBodyWorld_def]
    exact (burnLP_sentinel feeMachine.2.wf).trans ((burnFeePost_sentinel feeMem.wf).trans
      ((burnFeeReply_sentinel (feeBurnMemory_ptr reply1 sevm.currentTarget).wf _).trans
      ((burnFeeScratch_sentinel reply1.wf sevm.currentTarget).trans
      ((burnBalanceReply_sentinel reply0m.wf sevm.currentTarget _).trans
      ((burnBalanceReply_sentinel getterInitMemory_ptr.wf sevm.currentTarget _).trans
        burnEntryMemory_sentinel)))))
  -- WETH9's account from the query's world to the suffix world
  have keepsD1 : WethKeeps weth pre callee.d1 := by
    have staged0 : WethKeeps weth pre (burnCall0World sevm pre) :=
      keeps0.trans (WethKeeps.access (burnRead0World sevm pre) (burnT0 sevm pre).toAdr)
    have atD0 := staged0.trans (WethKeeps.staticcall fork call0
      (weth9_code_toList_ne (staged0.1.trans code)))
    have staged1 : WethKeeps weth pre (burnCall1World sevm pre callee.d0) :=
      atD0.trans (WethKeeps.access callee.d0 _)
    exact staged1.trans (WethKeeps.staticcall fork callee.initial.call1
      (weth9_code_toList_ne (staged1.1.trans code)))
  have keepsW := keepsD1.trans (burnBodyWorld_keeps (b := pre) (d0 := callee.d0) fork ne
    callee.fee.call (weth9_code_toList_ne (keepsD1.1.trans code)))
  have token0W : (burnBodyWords sevm pre callee.d0 callee.d1 callee.dF).token0 = burnT0 sevm pre :=
    rfl
  have bal : (burnBodyWords sevm pre callee.d0 callee.d1 callee.dF).amount0 ≤
      (burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF).getStorVal
        (swapTokenWord (burnBodyWords sevm pre callee.d0 callee.d1 callee.dF).token0).toAdr
        (Weth9.balSlot sevm.currentTarget) := by
    rw [token0W, swapTokenWord_burnT0, tok, keepsW.getStorVal]
    have le : (burnBodyWords sevm pre callee.d0 callee.d1 callee.dF).amount0 ≤ burnB0 callee.d0 :=
      amountLe
    unfold burnB0 at le
    rw [reply0, toB256_take_toBytes, tok, keeps0.getStorVal] at le
    exact le
  have wcodeW : (burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF).state.getCode
      (swapTokenWord (burnBodyWords sevm pre callee.d0 callee.d1 callee.dF).token0).toAdr =
        Weth9.code := by
    rw [token0W, swapTokenWord_burnT0, tok]
    exact keepsW.1.trans code
  have npW : sevm.benvStat.rules.isPrecomp
      (swapTokenWord (burnBodyWords sevm pre callee.d0 callee.d1 callee.dF).token0).toAdr =
      (false = true) := by
    rw [token0W, swapTokenWord_burnT0]
    exact np
  -- the transfer
  have hl : (burnWethLeg0 sevm (burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF)
      (burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF).memory 128
      (burnBodyWords sevm pre callee.d0 callee.d1 callee.dF) [0x89afcb44]
      callee.back.callGas1).1 = callee.back.d0 := (congrArg Prod.fst callee.back.leg).symm
  have hl' : (burnWethLeg0 sevm (burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF)
      (burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF).memory 128
      (burnBodyWords sevm pre callee.d0 callee.d1 callee.dF) [0x89afcb44]
      callee.back.callGas1).2 = callee.back.callGas0 := (congrArg Prod.snd callee.back.leg).symm
  have transfer0 := burnWethLeg0_spec (b := burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF)
    (M := (burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF).memory) (p0 := 128)
    (w := burnBodyWords sevm pre callee.d0 callee.d1 callee.dF) (R := [0x89afcb44])
    (callGas1 := callee.back.callGas1) fork nonstatic depth
    wcodeW npW pricedMem.wf (by decide) (by decide) (by decide) bal
    (by rw [hl']; exact sentries.fitsLeg) sentries.roomLeg
  rw [hl, hl'] at transfer0
  -- the final query
  obtain ⟨wf2, width2⟩ := burnSuffix_layout (w := burnBodyWords sevm pre callee.d0 callee.d1 callee.dF)
    fork pricedMem pricedSentinel (by decide) (by decide) nonzero0 nonzero1 (by decide) transfer0
    callee.back.transfer1
  have codeT0 := runCompiled_codePreserve transfer0.call weth
    (weth9_code_toList_ne (keepsW.1.trans code))
  have codeT1 := runCompiled_codePreserve callee.back.transfer1.call weth
    (weth9_code_toList_ne (codeT0.trans (keepsW.1.trans code)))
  have wcodeT1 : callee.back.d1.state.getCode
      (swapTokenWord (burnBodyWords sevm pre callee.d0 callee.d1 callee.dF).token0).toAdr =
      Weth9.code := by
    rw [token0W, swapTokenWord_burnT0, tok]
    exact codeT1.trans (codeT0.trans (keepsW.1.trans code))
  have hf : (burnWethFinal0 sevm (burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF).memory 128
      (burnBodyWords sevm pre callee.d0 callee.d1 callee.dF) [0x89afcb44] callee.back.d0
      callee.back.d1 callee.back.balanceGas1).1 = callee.back.e0 :=
    (congrArg Prod.fst callee.back.final).symm
  have hf' : (burnWethFinal0 sevm (burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF).memory 128
      (burnBodyWords sevm pre callee.d0 callee.d1 callee.dF) [0x89afcb44] callee.back.d0
      callee.back.d1 callee.back.balanceGas1).2 = callee.back.balanceGas0 :=
    (congrArg Prod.snd callee.back.final).symm
  have specF := burnWethFinal0_spec (M := (burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF).memory)
    (p0 := 128) (w := burnBodyWords sevm pre callee.d0 callee.d1 callee.dF) (R := [0x89afcb44])
    (d0 := callee.back.d0) (d1 := callee.back.d1) (balanceGas1 := callee.back.balanceGas1)
    fork depth wcodeT1 npW wf2 width2 (by decide)
    (by rw [hf']; exact sentries.fitsFinal) sentries.roomFinal
  rw [hf, hf'] at specF
  obtain ⟨first, -⟩ := specF
  -- the whole environment and the run
  let env : BurnForwardEnv sevm pre g :=
    ⟨callee.d0, callee.d1, callee.dF, callee.back.toBack transfer0 first, callee.fee,
      callee.initial.toInitial code0 call0 success0 long0 returnedGas0⟩
  have installedPre : some (pre.getCode sevm.currentTarget).toList = pairSem.image := by
    rw [target]
    change some (pre.state.getCode pair).toList = pairSem.image
    rw [state, futureCode]
    rfl
  obtain ⟨run, _⟩ := burn_bytecode_forward_consumes
    (current := { state := finish, logs := [], updates := [] }) [] codeEq fork value size
    guard selector repOwn tracked pairSem pairSem_image installedPre env guards
  exact ⟨run, rfl, fun newFresh => pair_live_outcome joint.pairRep pairFresh futureCode replayed run
    target state codeEq fork output representable newFresh⟩

end Blanc.Composition.UniswapV2PairWeth9Joint
