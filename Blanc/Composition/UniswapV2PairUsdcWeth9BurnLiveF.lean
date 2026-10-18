import Blanc.Composition.UniswapV2PairUsdcWeth9BurnEnv
import Blanc.Composition.UniswapV2PairUsdcWeth9CheckpointF
import Blanc.Composition.UniswapV2PairWeth9BurnLiveOne
import Blanc.Composition.UniswapV2PairWeth9BurnLive
import Blanc.Lift.Usdc.HistFFacts

/-!
# C6(c): the burn liveness row over the support-free checkpoint (finite twin)

Twin of `UniswapV2PairUsdcWeth9BurnLive.lean`: `pair_usdc_weth9_history_burn_live_finite`
is the burn row with `joint : JointCheckpoint2F …` and no quiet premise (the proof never
uses USDC's joint relation: no never-signer premise), proved exactly as the original via
`usdc_history_end_coreF` in place of the support version.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.UsdcLive

/-- **C6(c), the burn liveness row, support-free** (USDC = token0, WETH9 = token1).
Twin of `pair_usdc_weth9_history_burn_live` with `joint : JointCheckpoint2F …` and no
quiet premise: USDC's transfer is covered by its own queried balance, so no never-signer
premise and no joint relation are needed. -/
theorem pair_usdc_weth9_history_burn_live_finite {pair usdc weth : Adr} {cfg : ChainConfig}
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
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44) (depth : 2 ≤ sevm.depth)
    (notAdmin : pair ≠ Usdc.adminOf pre.state usdc)
    (callee : BurnEnvUW sevm pre g) (usdcSentries : callee.UsdcSentries)
    (wethSentries : callee.WethSentries)
    (recipientFresh : Usdc.KeysFresh (Usdc.historyKeyUniverse usdc trace KU)
      [.bal (Sevm.dataWord sevm 4).toAdr])
    (usdcLive : UsdcTransferOk
      (Usdc.ledger (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc trace KU)
        [.bal (Sevm.dataWord sevm 4).toAdr]) (pre.state.getStor usdc))
      pair (Sevm.dataWord sevm 4).toAdr callee.words.amount0.toNat)
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
  -- the Pair's replay and USDC at the history's end
  obtain ⟨futureCode, finish, K', replayed⟩ := pair_history_replayed trace joint.weth9.pairCode
    joint.weth9.pairRep pairFresh
  obtain ⟨-, tokens⟩ := replayed.fixed joint.weth9.unlocked
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.weth9.pairCode factoryInstalled
      joint.weth9.pairNonzero factoryNotSystem)
  have histF : Usdc.UsdcHistF usdc KU trace :=
    ⟨joint.usdcInstalled, governance, joint.usdcFoot, usdcFresh⟩
  obtain ⟨instF, -, injF, apartF, goodF⟩ := Usdc.usdc_history_end_coreF trace histF
  refine ⟨finish, K', replayed,
    fun transcript returndata answer0 answer1 answerFee final0 final1 accepted => ?_⟩
  have conditions := runTyped_burn_conditions accepted
  rw [answer0, answer1, answerFee, final0, final1] at conditions
  have histRep : WriterRep (pairHistoryUniverse pair trace KP) (checkpoint.state.getStor pair) st₀ :=
    joint.weth9.pairRep.extend pairFresh
  obtain ⟨rep, inside⟩ := replayed.at_frame target state
  let rows := lpMintTouched sevm.currentTarget ++ lpMintTouched callee.feeTo
  have inj := histRep.inj.extend rowsFresh
  have apart := histRep.apart.extend rowsFresh
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
  -- the tokens at the frame
  obtain ⟨code, token, -, -⟩ := pair_weth9_frame .one trace joint.weth9 pairFresh wethFresh
    factoryInstalled factoryNotSystem state
  have ne : sevm.currentTarget ≠ weth := target ▸ joint.weth9.apart
  have neU : sevm.currentTarget ≠ usdc := target ▸ joint.apart
  have wu : weth ≠ usdc := by
    have d := joint.weth9.distinct
    have t1 : st₀.token1 = weth := joint.weth9.token
    rw [joint.token0, t1] at d
    exact fun h => d h.symm
  have np : sevm.benvStat.rules.isPrecomp weth = false :=
    propext ⟨fun h => absurd h (joint.weth9.wethNotPrecompile _ fork),
      fun h => absurd h Bool.false_ne_true⟩
  have npU : sevm.benvStat.rules.isPrecomp usdc = false :=
    propext ⟨fun h => absurd h (joint.usdcNotPrecompile _ fork), fun h => absurd h Bool.false_ne_true⟩
  have tok1 : (burnT1 sevm pre &&& burnAddrMask).toAdr = weth := by
    unfold burnT1
    rw [and_burnAddrMask, burnAddrMask_and, toAdr_toB256, toAdr_toB256]
    change ((Devm.getStor (afterSload sevm (burnReservedWorld sevm pre) 6)
      sevm.currentTarget).get 7).toAdr = weth
    rw [afterSload_getStor]
    change ((burnReservedWorld sevm pre).getStorVal sevm.currentTarget 7).toAdr = weth
    rw [burnReservedWorld_slot (by decide), target]
    exact token
  have tok0 : (burnT0 sevm pre).toAdr = usdc := by
    unfold burnT0
    rw [burnAddrMask_and, toAdr_toB256, burnReservedWorld_slot (by decide)]
    obtain ⟨-, -, -, slot6, -⟩ := rep.fixed
    change ((pre.getStor sevm.currentTarget).get 6).toAdr = usdc
    rw [slot6, tokens.1]
    exact joint.token0
  have instPre : Usdc.UsdcInstalled usdc pre.state := by rw [state]; exact instF
  have usdcCodePre : pre.state.getCode usdc = Usdc.Proxy.code :=
    Blanc.ExecutionTrace.bytes_eq_of_image instPre.proxy
  have usdcNonempty : (pre.state.getCode usdc).toList ≠ [] := by
    rw [usdcCodePre]; exact Usdc.proxy_nonempty
  -- the initial USDC query
  have keepsC0U : WethKeeps usdc pre (burnCall0World sevm pre) :=
    (burnRead0World_keeps sevm pre neU).trans (WethKeeps.access _ _)
  have keepsR0U : WethKeeps usdc pre (burnRead0World sevm pre) := burnRead0World_keeps sevm pre neU
  have read0Fst : (burnUsdcRead0 sevm pre [0x89afcb44] callee.callGas1).1 = callee.d0 :=
    (congrArg Prod.fst callee.read0).symm
  have read0Snd : (burnUsdcRead0 sevm pre [0x89afcb44] callee.callGas1).2 = callee.callGas0 :=
    (congrArg Prod.snd callee.read0).symm
  have codesR0 : ∀ a, (burnRead0World sevm pre).state.getCode a = pre.state.getCode a := by
    intro a
    have h := (burnCall0World_bal sevm pre).2 a
    unfold burnCall0World at h
    rw [show (temporalAccountAccessBase (burnTokensWorld sevm (burnReservedWorld sevm pre))
      (burnT0 sevm pre).toAdr).state = (burnTokensWorld sevm (burnReservedWorld sevm pre)).state from
      UniswapV2PairWeth9Joint.temporalAccountAccessBase_state _ _] at h
    exact h
  have instR0 : Usdc.UsdcInstalled usdc (burnRead0World sevm pre).state :=
    usdcInstalled_of_codes instPre (fun a _ => codesR0 a)
      (congrArg (fun s : Stor => s.get Usdc.implSlot) keepsR0U.2)
  have specR0 := burnUsdcRead0_spec (R := [0x89afcb44]) (callGas1 := callee.callGas1) fork depth
    (by rw [tok0]; exact instR0) (by rw [tok0]; exact npU)
    (by
      rw [tok0, target]
      unfold Usdc.adminOf
      rw [show (burnRead0World sevm pre).state.getStor usdc = pre.state.getStor usdc from keepsR0U.2]
      exact notAdmin)
    (by decide) (by rw [read0Snd]; exact usdcSentries.fitsRead) usdcSentries.roomRead
  dsimp only at specR0
  rw [read0Fst, read0Snd] at specR0
  obtain ⟨code0, call0, success0, long0, returnedGas0, reply0, skel0⟩ := specR0
  -- the initial WETH9 query, over USDC's result
  have keepsC0 : WethKeeps weth pre (burnCall0World sevm pre) :=
    (burnRead0World_keeps sevm pre ne).trans (WethKeeps.access _ _)
  have keepsD0 : WethKeeps weth pre callee.d0 :=
    keepsC0.trans (WethKeeps.staticcall fork call0 (weth9_code_toList_ne (keepsC0.1.trans code)))
  have keepsD0U : WethKeeps usdc pre callee.d0 :=
    keepsC0U.trans (WethKeeps.staticcall fork call0 (by
      change ((burnCall0World sevm pre).state.getCode usdc).toList ≠ []
      rw [show (burnCall0World sevm pre).state.getCode usdc = pre.state.getCode usdc from keepsC0U.1]
      exact usdcNonempty))
  have hW : ∀ T, burnWethRead1 sevm pre callee.d0 [0x89afcb44] T =
      burnWethRead1 sevm pre (burnUsdcRead0Skel sevm pre [0x89afcb44]) [0x89afcb44] T := by
    intro T
    rw [skel0]
    exact burnWethRead1_withGasLeft _ _ _ _ _ _
  have hF : burnFee1Gas sevm pre callee.d0 [0x89afcb44] callee.factoryGas =
      burnFee1Gas sevm pre (burnUsdcRead0Skel sevm pre [0x89afcb44]) [0x89afcb44]
        callee.factoryGas := by
    rw [skel0]
    unfold burnFee1Gas
    rw [burnRead1Skel_withGasLeft]
  have read1Fst : (burnWethRead1 sevm pre (burnUsdcRead0Skel sevm pre [0x89afcb44]) [0x89afcb44]
      (burnFee1Gas sevm pre (burnUsdcRead0Skel sevm pre [0x89afcb44]) [0x89afcb44]
        callee.factoryGas)).1 = callee.d1 := (congrArg Prod.fst callee.read1).symm
  have read1Snd : (burnWethRead1 sevm pre (burnUsdcRead0Skel sevm pre [0x89afcb44]) [0x89afcb44]
      (burnFee1Gas sevm pre (burnUsdcRead0Skel sevm pre [0x89afcb44]) [0x89afcb44]
        callee.factoryGas)).2 = callee.callGas1 := (congrArg Prod.snd callee.read1).symm
  have specR1 := burnWethRead1_spec (b := pre) (d0 := callee.d0) (R := [0x89afcb44])
    (T1 := burnFee1Gas sevm pre callee.d0 [0x89afcb44] callee.factoryGas) fork (by omega)
    (by rw [tok1]; exact keepsD0.1.trans code) (by rw [tok1]; exact np) (by decide)
    (by rw [hW, hF, read1Snd]; exact wethSentries.fitsRead) wethSentries.roomRead
  dsimp only at specR1
  rw [hF, hW, read1Fst, read1Snd] at specR1
  obtain ⟨code1, call1, success1, long1, returnedGas1, reply1⟩ := specR1
  have returnedGas1' : callee.d1.gasLeft = callee.fee.gas + 64 := by
    rw [callee.fee_gas]
    exact returnedGas1
  have keepsD1 : WethKeeps weth pre callee.d1 :=
    (keepsD0.trans (WethKeeps.access callee.d0 _)).trans (WethKeeps.staticcall fork call1
      (weth9_code_toList_ne ((keepsD0.trans (WethKeeps.access callee.d0 _)).1.trans code)))
  have keepsD1U : WethKeeps usdc pre callee.d1 :=
    (keepsD0U.trans (WethKeeps.access callee.d0 _)).trans (WethKeeps.staticcall fork call1 (by
      change ((burnCall1World sevm pre callee.d0).state.getCode usdc).toList ≠ []
      rw [show (burnCall1World sevm pre callee.d0).state.getCode usdc = pre.state.getCode usdc from
        (keepsD0U.trans (WethKeeps.access callee.d0 _)).1]
      exact usdcNonempty))
  -- the guards
  have guards : BurnForwardGuards (WriterExtend K' (lpMintTouched sevm.currentTarget)) finish sevm
      pre callee.d0 callee.d1 callee.dF callee.back.e0 callee.back.e1 :=
    burnGuards_of_model long1 repOwn inj apart subOwn feeRow conditions
  have guardsCopy := guards
  obtain ⟨-, nonstatic, ⟨fee, feeAccepted, amount0, amount1, burnPost, events, priced, positive0,
    positive1, burned⟩, fresh, -, -⟩ := guardsCopy
  -- the locked state at `d1` (as `burnPc0_exact`)
  obtain ⟨bound0, bound1⟩ := burnR_bounds sevm pre
  have stor0 := compiled_staticcall_stor fork call0
  have stor1 := compiled_staticcall_stor fork call1
  have d1Rep : WriterRep (WriterExtend K' (lpMintTouched sevm.currentTarget))
      (callee.d1.getStor sevm.currentTarget) { finish with unlocked := 0 } := by
    have same : callee.d1.getStor sevm.currentTarget =
        (burnLockedWorld sevm pre).getStor sevm.currentTarget :=
      calc callee.d1.getStor sevm.currentTarget
          = (burnCall1World sevm pre callee.d0).getStor sevm.currentTarget := stor1 _
        _ = callee.d0.getStor sevm.currentTarget := by
          simp only [burnCall1World, Devm.getStor, Devm.getAcct, UniswapV2PairWeth9Joint.temporalAccountAccessBase_state]
        _ = (burnCall0World sevm pre).getStor sevm.currentTarget := stor0 _
        _ = (burnTokensWorld sevm (burnReservedWorld sevm pre)).getStor sevm.currentTarget := by
          simp only [burnCall0World, Devm.getStor, Devm.getAcct, UniswapV2PairWeth9Joint.temporalAccountAccessBase_state]
        _ = (burnLockedWorld sevm pre).getStor sevm.currentTarget := by
          rw [burnTokensWorld, afterSload_getStor, afterSload_getStor, burnReservedWorld,
            afterSload_getStor]
    rw [same]
    exact repOwn.burn_locked_world
  have req0 := balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget
  have reply0m := balanceReplyMemory_ptr callee.d0.returnData req0
  have reply1m : PtrMem 128 192 (burnMem2 sevm callee.d0 callee.d1) :=
    balanceReplyMemory_ptr callee.d1.returnData (balanceRequestMemory_ptr reply0m sevm.currentTarget)
  obtain ⟨nonzero0, nonzero1, -⟩ := burnFeePricing_exact
    (len := callee.d1.returnData.length.toB256) (discarded := 0) fork reply1m (by decide) d1Rep
    tracked nonstatic bound0 bound1 callee.fee feeAccepted fresh priced positive0 positive1 burned
  obtain ⟨amountLe1, -⟩ := burnPriced_lockedRep fork reply1m (by decide) d1Rep tracked nonstatic
    bound0 bound1 callee.fee feeAccepted fresh priced burned
  have amountLe0 := burnFee_amount0_le fork reply1m (by decide) d1Rep tracked nonstatic bound0
    bound1 callee.fee feeAccepted fresh priced burned
  -- the suffix world's memory (as `burnPc0_exact`)
  have feeMem : PtrMem 128 192
      (feeReplyMemory (feeBurnMemory (burnMem2 sevm callee.d0 callee.d1) sevm.currentTarget)
        callee.dF.returnData) :=
    feeReplyMemory_ptr callee.dF.returnData
      (feeRequestMemory_ptr (feeBurnMemory_ptr reply1m sevm.currentTarget))
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
      ((burnFeeReply_sentinel (feeBurnMemory_ptr reply1m sevm.currentTarget).wf _).trans
      ((burnFeeScratch_sentinel reply1m.wf sevm.currentTarget).trans
      ((burnBalanceReply_sentinel reply0m.wf sevm.currentTarget _).trans
      ((burnBalanceReply_sentinel getterInitMemory_ptr.wf sevm.currentTarget _).trans
        burnEntryMemory_sentinel)))))
  -- the accounts at the suffix's entry world
  have keepsB : WethKeeps weth pre callee.body := keepsD1.trans (burnBodyWorld_keeps (b := pre)
    (d0 := callee.d0) fork ne callee.fee.call (weth9_code_toList_ne (keepsD1.1.trans code)))
  have keepsBU : WethKeeps usdc pre callee.body := keepsD1U.trans (burnBodyWorld_keeps (b := pre)
    (d0 := callee.d0) fork neU callee.fee.call (by
      change (callee.d1.state.getCode usdc).toList ≠ []
      rw [show callee.d1.state.getCode usdc = pre.state.getCode usdc from keepsD1U.1]
      exact usdcNonempty))
  have codeB : ∀ a, (pre.state.getCode a).toList ≠ [] →
      callee.body.state.getCode a = pre.state.getCode a := by
    intro a nonempty
    have c0 : (St (burnCall0World sevm pre) (callee.callGas0.toB256 :: burnT0 sevm pre :: 128 :: 36 ::
        128 :: 32 :: 164 :: 0x70a08231 :: burnT0 sevm pre :: 0 :: burnT1 sevm pre :: burnT0 sevm pre ::
        burnInitLocals sevm pre [0x89afcb44]) (balanceRequestMemory getterInitMemory
          sevm.currentTarget) callee.callGas0).state.getCode a = pre.state.getCode a := by
      rw [St, Devm.setMach_state]
      exact (burnCall0World_bal sevm pre).2 a
    have cD0 : callee.d0.state.getCode a = pre.state.getCode a :=
      (runCompiled_codePreserve call0 a (by intro h; apply nonempty; rw [← c0]; exact h)).trans c0
    have c1 : (St (burnCall1World sevm pre callee.d0) (callee.callGas1.toB256 ::
        (burnT1 sevm pre &&& burnAddrMask) :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
        (burnT1 sevm pre &&& burnAddrMask) :: 0 :: burnB0 callee.d0 :: burnT1 sevm pre ::
        burnT0 sevm pre :: burnInitLocals sevm pre [0x89afcb44])
        (balanceRequestMemory (burnMem1 sevm callee.d0) sevm.currentTarget)
        callee.callGas1).state.getCode a = pre.state.getCode a := by
      rw [St, Devm.setMach_state]
      exact ((WethKeeps.access (w := a) callee.d0 _).1).trans cD0
    have cD1 : callee.d1.state.getCode a = pre.state.getCode a :=
      (runCompiled_codePreserve call1 a (by intro h; apply nonempty; rw [← c1]; exact h)).trans c1
    have cFp : (St (feeFactoryCallWorld sevm (feeBurnWorld sevm callee.d1))
        (callee.fee.factoryGas.toB256 :: feeFactoryWord sevm (feeBurnWorld sevm callee.d1) :: 128 ::
          4 :: 128 :: 32 :: 132 :: 0x017e7e58 :: feeFactoryWord sevm (feeBurnWorld sevm callee.d1) ::
          0 :: 0 :: burnR1 sevm pre :: burnR0 sevm pre :: 0x15e2 ::
          burnFeeLocalsAt sevm callee.d1 (burnMem2 sevm callee.d0 callee.d1) (burnB0 callee.d0)
            (burnT1 sevm pre) (burnT0 sevm pre) (burnR1 sevm pre) (burnR0 sevm pre)
            (burnRecipientWord sevm) 0x053d [0x89afcb44])
        (feeRequestMemory (feeBurnMemory (burnMem2 sevm callee.d0 callee.d1) sevm.currentTarget))
        callee.fee.factoryGas).state.getCode a = pre.state.getCode a := by
      rw [St, Devm.setMach_state]
      exact ((feeFactoryCallWorld_keeps (w := weth) sevm callee.d1).2.2 a).trans cD1
    have cF : callee.dF.state.getCode a = pre.state.getCode a :=
      (runCompiled_codePreserve callee.fee.call a (by intro h; apply nonempty; rw [← cFp]; exact h)).trans cFp
    exact ((burnBodyWorld_fromF (w := weth) sevm pre callee.d0 callee.d1 callee.dF ne).2.2 a).trans cF
  have token0W : (swapTokenWord callee.words.token0).toAdr = usdc := by
    change (swapTokenWord (burnT0 sevm pre)).toAdr = usdc
    rw [swapTokenWord_burnT0, tok0]
  have token1W : (swapTokenWord callee.words.token1).toAdr = weth := by
    change (swapTokenWord (burnT1 sevm pre)).toAdr = weth
    unfold swapTokenWord
    rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask by decide,
      and_mask_word, toAdr_toB256]
    rw [← tok1, and_burnAddrMask, toAdr_toB256]
  have recW : callee.words.recipient.toAdr = (Sevm.dataWord sevm 4).toAdr := by
    change (burnRecipientWord sevm).toAdr = _
    unfold burnRecipientWord
    rw [toAdr_toB256]
  -- USDC at the suffix's entry world
  let H := Usdc.historyKeyUniverse usdc trace KU
  let U := SlotFootprint.extendBy H [.bal (Sevm.dataWord sevm 4).toAdr]
  have storBU : callee.body.state.getStor usdc = future.state.getStor usdc := by
    rw [← state]; exact keepsBU.2
  have storBU' : callee.body.state.getStor usdc = pre.state.getStor usdc := keepsBU.2
  have instB : Usdc.UsdcInstalled usdc callee.body.state :=
    usdcInstalled_of_codes instPre codeB (by rw [storBU'])
  have finvB : FootCore U (callee.body.state.getStor usdc) :=
    ⟨injF.extend recipientFresh, apartF.extend recipientFresh,
      Usdc.ledger_good_congr goodF (by rw [storBU]) (by rw [storBU])⟩
  have kPair : U (.bal pair) := Or.inl (Or.inl joint.tracked)
  have kTo : U (.bal (Sevm.dataWord sevm 4).toAdr) := Or.inr (List.mem_singleton_self _)
  have notAdminB : pair ≠ Usdc.adminOf callee.body.state usdc := by
    unfold Usdc.adminOf; rw [storBU']; exact notAdmin
  have balanceB : callee.words.amount0.toNat ≤ (Usdc.ledger U (callee.body.state.getStor usdc)).bal pair := by
    rw [Usdc.ledger_bal kPair, storBU']
    have le : callee.words.amount0 ≤ burnB0 callee.d0 := amountLe0
    unfold burnB0 at le
    rw [reply0, toB256_take_toBytes, tok0, target,
      show (burnRead0World sevm pre).state.getStor usdc = pre.state.getStor usdc from keepsR0U.2] at le
    have lt : Usdc.balanceBits ((pre.state.getStor usdc).get (Usdc.balSlot pair)) < 2 ^ 256 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 255)) (Nat.pow_le_pow_right (by decide) (by decide))
    have h := B256.le_iff_toNat_le_toNat.mp le
    rw [B256.toNat_toB256_of_lt lt] at h
    exact h
  -- USDC's transfer
  have leg0Fst : (burnUsdcLeg0 sevm callee.body callee.body.memory 128 callee.words [0x89afcb44]
      callee.back.callGas1).1 = callee.back.d0 := (congrArg Prod.fst callee.back.leg0).symm
  have leg0Snd : (burnUsdcLeg0 sevm callee.body callee.body.memory 128 callee.words [0x89afcb44]
      callee.back.callGas1).2 = callee.back.callGas0 := (congrArg Prod.snd callee.back.leg0).symm
  have transfer0 := burnUsdcLeg0_spec (b := callee.body) (M := callee.body.memory) (p0 := 128)
    (w := callee.words) (R := [0x89afcb44]) (callGas1 := callee.back.callGas1) (U := U) fork
    nonstatic depth (by rw [token0W]; exact instB) (by rw [token0W]; exact finvB)
    (by rw [token0W]; exact npU) (by rw [target]; exact kPair) (by rw [recW]; exact kTo)
    (by rw [token0W, target]; exact notAdminB) (by rw [token0W, target, recW, storBU']; exact usdcLive)
    (by rw [token0W, target]; exact balanceB) pricedMem.wf (by decide) (by decide) (by decide)
    (by rw [leg0Snd]; exact usdcSentries.fitsLeg) usdcSentries.roomLeg
  rw [leg0Fst, leg0Snd] at transfer0
  -- what USDC's transfer keeps
  have dT : callee.back.d0 = usdcTransferCall sevm callee.body (burnLegStack callee.words [0x89afcb44])
      callee.body.memory 128 callee.words.amount0 callee.words.recipient callee.words.token0 0x1698
      callee.back.callGas0 := by
    rw [← leg0Fst, ← leg0Snd]
    rfl
  have tm0 : (tokenMask callee.words.token0).toAdr = usdc := token0W
  have keepT := usdcTransferCall_keeps sevm callee.body (burnLegStack callee.words [0x89afcb44])
    callee.body.memory 128 callee.words.amount0 callee.words.recipient callee.words.token0 0x1698
    callee.back.callGas0
  have codesD0 : ∀ a, callee.back.d0.state.getCode a = callee.body.state.getCode a := by
    intro a; rw [dT]; exact keepT.2.1 a
  have kPairT : U (.bal sevm.currentTarget) := by rw [target]; exact kPair
  have kToT : U (.bal callee.words.recipient.toAdr) := by rw [recW]; exact kTo
  have slotFix : ∀ k, k ∈ Usdc.fixedSlots →
      (callee.back.d0.state.getStor usdc).get k = (callee.body.state.getStor usdc).get k := by
    intro k hk
    rw [dT, ← tm0]
    exact usdcTransferCall_tokenStor sevm callee.body (burnLegStack callee.words [0x89afcb44])
      callee.body.memory 128 callee.words.amount0 callee.words.recipient callee.words.token0 0x1698
      callee.back.callGas0 pricedMem.wf (by decide) (by decide)
      (fun e => finvB.apart _ kPairT (show Usdc.balSlot sevm.currentTarget ∈ Usdc.fixedSlots by
        rw [← e]; exact hk))
      (fun e => finvB.apart _ kToT (show Usdc.balSlot callee.words.recipient.toAdr ∈ Usdc.fixedSlots by
        rw [← e]; exact hk))
  have implMem : Usdc.implSlot ∈ Usdc.fixedSlots := by
    unfold Usdc.fixedSlots; simp only [List.mem_cons, List.not_mem_nil, or_true, true_or]
  have adminMem : Usdc.adminSlot ∈ Usdc.fixedSlots := by
    unfold Usdc.fixedSlots; simp only [List.mem_cons, List.not_mem_nil, or_true, true_or]
  have instD0 : Usdc.UsdcInstalled usdc callee.back.d0.state :=
    usdcInstalled_of_codes instB (fun a _ => codesD0 a) (slotFix _ implMem)
  have storWd0 : callee.back.d0.state.getStor weth = callee.body.state.getStor weth := by
    rw [dT]; exact keepT.1 weth (by rw [tm0]; exact wu)
  have codeWd0 : callee.back.d0.state.getCode weth = Weth9.code :=
    (codesD0 weth).trans ((codeB weth (weth9_code_toList_ne code)).trans code)
  -- WETH9's balance word at the transfer world covers `amount1`
  have balanceW : callee.words.amount1 ≤
      callee.body.getStorVal weth (Weth9.balSlot sevm.currentTarget) := by
    have answer : feeBurnBalance1 (burnMem2 sevm callee.d0 callee.d1) =
        Bytes.toB256 (callee.d1.returnData.take 32) :=
      balanceReplyMemory_word reply0m.wf sevm.currentTarget callee.d1.returnData long1
    have le : callee.words.amount1 ≤ feeBurnBalance1 (burnMem2 sevm callee.d0 callee.d1) := amountLe1
    rw [answer, reply1, toB256_take_toBytes, tok1, keepsD0.getStorVal] at le
    rw [keepsB.getStorVal]
    exact le
  have balD0 : callee.words.amount1 ≤ callee.back.d0.getStorVal
      (swapTokenWord callee.words.token1).toAdr (Weth9.balSlot sevm.currentTarget) := by
    rw [token1W]
    show _ ≤ (callee.back.d0.state.getStor weth).get _
    rw [storWd0]
    exact balanceW
  -- WETH9's transfer, at USDC's result
  obtain ⟨y0, hy0⟩ : ∃ y, callee.back.d0 =
      (burnUsdcLeg0Skel sevm callee.body callee.body.memory 128 callee.words [0x89afcb44]).withGasLeft y :=
    ⟨_, dT.trans (usdcTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _)⟩
  have leg1Eq : ∀ bg, burnWethLeg1 sevm callee.back.d0 callee.body.memory 128 callee.words
      [0x89afcb44] bg = burnWethLeg1 sevm (burnUsdcLeg0Skel sevm callee.body callee.body.memory 128
        callee.words [0x89afcb44]) callee.body.memory 128 callee.words [0x89afcb44] bg := by
    intro bg; rw [hy0]; exact burnWethLeg1_withGasLeft _ _ _ _ _ _ _ _
  have leg1Fst : (burnWethLeg1 sevm callee.back.d0 callee.body.memory 128 callee.words [0x89afcb44]
      callee.back.balanceGas0).1 = callee.back.d1 := by
    rw [leg1Eq]; exact (congrArg Prod.fst callee.back.leg1).symm
  have leg1Snd : (burnWethLeg1 sevm callee.back.d0 callee.body.memory 128 callee.words [0x89afcb44]
      callee.back.balanceGas0).2 = callee.back.callGas1 := by
    rw [leg1Eq]; exact (congrArg Prod.snd callee.back.leg1).symm
  have nz0 : callee.words.amount0 ≠ 0 := nonzero0
  have nz1 : callee.words.amount1 ≠ 0 := nonzero1
  have roomL : (callee.words.locals callee.words.balance1 callee.words.balance0 [0x89afcb44]).length
      ≤ 1000 := by
    simp only [BurnSuffixWords.locals, burnPricedLocals, List.length_cons, List.length_nil]
    omega
  obtain ⟨⟨n1, mem1⟩, -, lower1, upper1, -⟩ :=
    swapFwdOpt_layout (k := 161) (a := callee.words.amount0) (d := callee.back.d0) fork roomL
      pricedMem pricedSentinel (by decide) (by decide) (by decide) (fun _ => transfer0)
  simp only [swapOptPtr, swapOptMem, nz0, ↓reduceIte] at mem1 lower1 upper1
  have transfer1 := burnWethLeg1_spec (d0 := callee.back.d0) (M := callee.body.memory) (p0 := 128)
    (w := callee.words) (R := [0x89afcb44]) (balanceGas0 := callee.back.balanceGas0) fork nonstatic
    (by omega) (by rw [token1W]; exact codeWd0) (by rw [token1W]; exact np) mem1.wf lower1
    (by
      have : 2 ^ 161 + 2 ^ 161 + 164 < 2 ^ 256 := by decide
      omega)
    (by decide) balD0 (by rw [leg1Snd]; exact wethSentries.fitsLeg) wethSentries.roomLeg
  rw [leg1Fst, leg1Snd] at transfer1
  -- USDC after WETH9's transfer
  have d1T : callee.back.d1 = wethTransferCall sevm callee.back.d0
      (burnLegStack callee.words [0x89afcb44]) (burnLeg1Mem callee.body.memory 128 callee.words
        callee.back.d0) (burnLeg1Ptr 128 callee.back.d0) callee.words.amount1 callee.words.recipient
      callee.words.token1 0x16a3 callee.back.callGas1 := by
    rw [← leg1Fst, ← leg1Snd]
    rfl
  have tm1 : (tokenMask callee.words.token1).toAdr = weth := token1W
  have storUd1 : callee.back.d1.state.getStor usdc = callee.back.d0.state.getStor usdc := by
    rw [d1T]
    exact wethTransferCall_storOff _ _ _ _ _ _ _ _ _ _ (by rw [tm1]; exact wu.symm)
  have codesD1 : ∀ a, (callee.back.d0.state.getCode a).toList ≠ [] →
      callee.back.d1.state.getCode a = callee.back.d0.state.getCode a :=
    fun a h => runCompiled_codePreserve transfer1.call a h
  have instD1 : Usdc.UsdcInstalled usdc callee.back.d1.state :=
    usdcInstalled_of_codes instD0 codesD1 (by rw [storUd1])
  have notAdminD1 : pair ≠ Usdc.adminOf callee.back.d1.state usdc := by
    unfold Usdc.adminOf
    rw [storUd1, slotFix _ adminMem, storBU']
    exact notAdmin
  -- USDC's final query
  obtain ⟨wf2, width2⟩ := burnSuffix_layout (w := callee.words) fork pricedMem pricedSentinel
    (by decide) (by decide) nz0 nz1 (by decide) transfer0 transfer1
  obtain ⟨y1, hy1⟩ : ∃ y, callee.back.d1 = (burnLeg1Skel sevm (burnUsdcLeg0Skel sevm callee.body
      callee.body.memory 128 callee.words [0x89afcb44]) callee.body.memory 128 callee.words
      [0x89afcb44]).withGasLeft y :=
    ⟨_, (congrArg Prod.fst callee.back.leg1).trans (wethTransferCallAt_eq _ _ _ _ _ _ _ _ _ _ _ _ _)⟩
  have fin0Fst : (burnUsdcFinal0 sevm callee.body.memory 128 callee.words [0x89afcb44] callee.back.d0
      callee.back.d1 callee.back.balanceGas1).1 = callee.back.e0 := callee.back.final0.symm
  have fin0Snd : (burnUsdcFinal0 sevm callee.body.memory 128 callee.words [0x89afcb44] callee.back.d0
      callee.back.d1 callee.back.balanceGas1).2 = callee.back.balanceGas0 := by
    rw [hy1, hy0, burnUsdcFinal0_withGasLeft]
    exact callee.back.gas0.symm
  have specU := burnUsdcFinal0_spec (M := callee.body.memory) (p0 := 128) (w := callee.words)
    (R := [0x89afcb44]) (d0 := callee.back.d0) (d1 := callee.back.d1)
    (balanceGas1 := callee.back.balanceGas1) fork depth (by rw [token0W]; exact instD1)
    (by rw [token0W]; exact npU) (by rw [token0W, target]; exact notAdminD1) wf2 width2 (by decide)
    (by rw [fin0Snd]; exact usdcSentries.fitsFinal) usdcSentries.roomFinal
  rw [fin0Fst, fin0Snd] at specU
  obtain ⟨first, -, skelE0⟩ := specU
  -- WETH9's final query, over USDC's
  have codeT1 : callee.back.d1.state.getCode weth = Weth9.code :=
    (codesD1 weth (weth9_code_toList_ne codeWd0)).trans codeWd0
  have codeE0 : callee.back.e0.state.getCode weth = Weth9.code :=
    weth9Code_of_runCompiled first.call (weth9Code_temporal codeT1)
  have fin1Eq : burnWethFinal1 sevm callee.body.memory 128 callee.words [0x89afcb44] callee.back.d0
      callee.back.d1 callee.back.e0 (g + 64) =
      burnWethFinal1 sevm callee.body.memory 128 callee.words [0x89afcb44]
        (burnUsdcLeg0Skel sevm callee.body callee.body.memory 128 callee.words [0x89afcb44])
        (burnLeg1Skel sevm (burnUsdcLeg0Skel sevm callee.body callee.body.memory 128 callee.words
          [0x89afcb44]) callee.body.memory 128 callee.words [0x89afcb44])
        (burnUsdcFinal0Skel sevm callee.body.memory 128 callee.words [0x89afcb44]
          (burnUsdcLeg0Skel sevm callee.body callee.body.memory 128 callee.words [0x89afcb44])
          (burnLeg1Skel sevm (burnUsdcLeg0Skel sevm callee.body callee.body.memory 128 callee.words
            [0x89afcb44]) callee.body.memory 128 callee.words [0x89afcb44])) (g + 64) := by
    rw [skelE0, hy1, hy0, burnUsdcFinal0Skel_withGasLeft, burnWethFinal1_withGasLeft]
  have fin1Fst : (burnWethFinal1 sevm callee.body.memory 128 callee.words [0x89afcb44] callee.back.d0
      callee.back.d1 callee.back.e0 (g + 64)).1 = callee.back.e1 := by
    rw [fin1Eq]; exact (congrArg Prod.fst callee.back.final1).symm
  have fin1Snd : (burnWethFinal1 sevm callee.body.memory 128 callee.words [0x89afcb44] callee.back.d0
      callee.back.d1 callee.back.e0 (g + 64)).2 = callee.back.balanceGas1 := by
    rw [fin1Eq]; exact (congrArg Prod.snd callee.back.final1).symm
  have specF := burnWethFinal1_spec (M := callee.body.memory) (p0 := 128) (w := callee.words)
    (R := [0x89afcb44]) (d0 := callee.back.d0) (d1 := callee.back.d1) (e0 := callee.back.e0)
    (G := g + 64) fork (by omega) (by rw [token1W]; exact codeE0) (by rw [token1W]; exact np) wf2
    width2 (by decide) (by rw [fin1Snd]; exact wethSentries.fitsFinal) wethSentries.roomFinal
  rw [fin1Fst, fin1Snd] at specF
  obtain ⟨second, -⟩ := specF
  -- the whole environment and the run
  let initial : BurnInitialCallee sevm pre callee.d0 callee.d1 [0x89afcb44] callee.fee.gas :=
    { callGas0 := callee.callGas0, callGas1 := callee.callGas1, lockLoad := callee.initial.lockLoad,
      lockStore := callee.initial.lockStore, reserveLoad := callee.initial.reserveLoad,
      loadEq := callee.initial.loadEq, storeEq := callee.initial.storeEq,
      reserveEq := callee.initial.reserveEq, sentry := callee.initial.sentry, code0 := code0,
      call0 := call0, success0 := success0, long0 := long0, returnedGas0 := returnedGas0,
      code1 := code1, call1 := call1, success1 := success1, long1 := long1,
      returnedGas1 := returnedGas1' }
  let env : BurnForwardEnv sevm pre g :=
    ⟨callee.d0, callee.d1, callee.dF, callee.back.toBack transfer0 transfer1 first second, callee.fee,
      initial⟩
  have installedPre : some (pre.getCode sevm.currentTarget).toList = pairSem.image := by
    rw [target]
    change some (pre.state.getCode pair).toList = pairSem.image
    rw [state, futureCode]
    rfl
  obtain ⟨run, _⟩ := burn_bytecode_forward_consumes
    (current := { state := finish, logs := [], updates := [] }) [] codeEq fork value size
    guard selector repOwn tracked pairSem pairSem_image installedPre env guards
  exact ⟨run, rfl, fun newFresh => pair_live_outcome joint.weth9.pairRep pairFresh futureCode
    replayed run target state codeEq fork output representable newFresh⟩

end Blanc.Composition.UniswapV2PairUsdcWeth9
