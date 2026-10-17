import Blanc.Composition.UniswapV2PairWeth9BurnLive
import Blanc.Composition.UniswapV2PairWeth9BurnWorldOne
import Blanc.Composition.UniswapV2PairWeth9SwapLiveBothFacts
import Blanc.Composition.UniswapV2PairWeth9LegsSkim

/-!
# C4(b): the burn liveness row with WETH9 = token1 (U8h)

`pair_weth9_history_burn_live_one` restates `pair_history_burn_live` from the joint checkpoint with
WETH9's three records removed (`BurnEnvW1`: pinned to `burnWethRead1`, `burnWethLeg1`,
`burnWethFinal1`).  Inside the model's acceptance the records are rebuilt:

* the WETH9 initial query (after X's) and final query (after X's) are code-only: WETH9's code at the
  token the Pair loads (history), carried to each staged world;
* WETH9's transfer comes after X's transfer, so it is discharged by the X-leg quiescence
  (`burnWethLeg1_spec_afterX`).  Its world facts at the suffix's entry world are WETH9's code,
  footprint and the ether-supply bound (`WethFootAt`, from the history's end across X's initial
  query and the factory query, `static_foot`), the Pair's WETH9 allowances zero (C3), the Pair's
  storage representing the locked state after the fee mint and the LP burn (`burnPriced_lockedRep`),
  the factory's runtime at that state's factory (A4/A14 code premise carried over the history), and
  `amount1 ≤` the Pair's WETH9 balance there (the priced `amount1` is at most the second initial
  answer, which is that balance: the Pair writes only its own storage and the static queries write
  none).

Added premises, all HASH-T or gas (none mentions WETH9's answers): HASH-T over the WETH9 keys of
X's initial-query child and of the factory-query child (`BurnEnvW1.XFresh.read`, `.factory`, so the
footprint crosses those `STATICCALL`s), HASH-T over X's transfer child (`.xWeth` against WETH9's
history universe, `.xPair` against the Pair's history universe extended by the LP rows, A16
addendum), the legs' call gases words and their 63/64 sentries (`BurnEnvW1.WethSentries`), and the
frame's call depth.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.UniswapV2Pair
open Blanc.Composition.UniswapV2PairWeth9XLeg (CallChildFresh StaticChildFresh wethRunKeys
  pairRunKeys)

section W1

variable {sevm : Sevm} {b : Devm} {g : Nat}

/-- The suffix's entry world of a `BurnEnvW1`. -/
abbrev BurnEnvW1.body (env : BurnEnvW1 sevm b g) : Devm := burnBodyWorld sevm b env.d0 env.d1 env.dF

/-- The suffix's words of a `BurnEnvW1`. -/
abbrev BurnEnvW1.words (env : BurnEnvW1 sevm b g) : BurnSuffixWords :=
  burnBodyWords sevm b env.d0 env.d1 env.dF

/-- X's initial query's staged state (`BurnInitialCallee.call0`). -/
def BurnEnvW1.readPre (env : BurnEnvW1 sevm b g) : Devm :=
  St (burnCall0World sevm b) (env.initial.callGas0.toB256 :: burnT0 sevm b :: 128 :: 36 :: 128 ::
      32 :: 164 :: 0x70a08231 :: burnT0 sevm b :: 0 :: burnT1 sevm b :: burnT0 sevm b ::
      burnInitLocals sevm b [0x89afcb44])
    (balanceRequestMemory getterInitMemory sevm.currentTarget) env.initial.callGas0

/-- The factory query's staged state (`BurnFeeCallee.call`). -/
def BurnEnvW1.factoryPre (env : BurnEnvW1 sevm b g) : Devm :=
  St (feeFactoryCallWorld sevm (feeBurnWorld sevm env.d1))
    (env.fee.factoryGas.toB256 :: feeFactoryWord sevm (feeBurnWorld sevm env.d1) :: 128 :: 4 ::
      128 :: 32 :: 132 :: 0x017e7e58 :: feeFactoryWord sevm (feeBurnWorld sevm env.d1) :: 0 :: 0 ::
      burnR1 sevm b :: burnR0 sevm b :: 0x15e2 ::
      burnFeeLocalsAt sevm env.d1 (burnMem2 sevm env.d0 env.d1) (burnB0 env.d0) (burnT1 sevm b)
        (burnT0 sevm b) (burnR1 sevm b) (burnR0 sevm b) (burnRecipientWord sevm) 0x053d [0x89afcb44])
    (feeRequestMemory (feeBurnMemory (burnMem2 sevm env.d0 env.d1) sevm.currentTarget))
    env.fee.factoryGas

/-- X's transfer `CALL`'s staged state (`BurnBackForwardEnv.transfer0`). -/
def BurnEnvW1.xferPre (env : BurnEnvW1 sevm b g) : Devm :=
  xferCallState env.body (env.words.locals env.words.balance1 env.words.balance0 [0x89afcb44])
    env.body.memory 128 env.words.amount0 env.words.recipient env.words.token0 0x1698
    env.back.callGas0

/-- **HASH-T over X's children (and the factory query's).**  The keys the WETH9 frames of X's
initial-query child, of the factory-query child and of X's transfer child touch are fresh against
WETH9's universe `UW`, and the Pair rows X's transfer child touches are fresh against `UP`. -/
structure BurnEnvW1.XFresh (env : BurnEnvW1 sevm b g) (weth : Adr) (UW : Weth9.Key → Prop)
    (UP : WriterKey → Prop) : Prop where
  read : StaticChildFresh sevm env.readPre fun D => Weth9.KeysFresh UW (wethRunKeys weth D)
  factory : StaticChildFresh sevm env.factoryPre fun D => Weth9.KeysFresh UW (wethRunKeys weth D)
  xWeth : CallChildFresh sevm env.xferPre fun D => Weth9.KeysFresh UW (wethRunKeys weth D)
  xPair : CallChildFresh sevm env.xferPre fun D => WriterFreshKeys UP (pairRunKeys sevm.currentTarget D)

/-- **The gas sentries of WETH9's three Burn legs (token1)**: each leg's call gas a word, and room
for WETH9's run under the 63/64 rule (with the `transfer`'s `SSTORE` stipend). -/
structure BurnEnvW1.WethSentries (env : BurnEnvW1 sevm b g) : Prop where
  fitsRead : env.callGas1 < 2 ^ 256
  roomRead : balUsed sevm env.d0 (burnRead1Stack sevm b [0x89afcb44] env.d0) (burnMem1 sevm env.d0) 128
      (burnT1 sevm b &&& burnAddrMask) ≤
    except64th (burnFee1Gas sevm b env.d0 [0x89afcb44] env.factoryGas + 64 +
      balUsed sevm env.d0 (burnRead1Stack sevm b [0x89afcb44] env.d0) (burnMem1 sevm env.d0) 128
        (burnT1 sevm b &&& burnAddrMask))
  fitsLeg : env.back.callGas1 < 2 ^ 256
  roomLeg : burnLeg1Used sevm env.back.d0 env.body.memory 128 env.words [0x89afcb44] + gCallStipend ≤
    except64th (burnLeg1Need sevm env.back.d0 env.body.memory 128 env.words [0x89afcb44]
        env.back.balanceGas0 +
      burnLeg1Used sevm env.back.d0 env.body.memory 128 env.words [0x89afcb44])
  fitsFinal : env.back.balanceGas1 < 2 ^ 256
  roomFinal : balUsed sevm env.back.e0 (burnFinal1Stack env.words [0x89afcb44] env.back.e0)
      (burnFinal1Mem sevm env.body.memory 128 env.words env.back.d0 env.back.d1 env.back.e0)
      (burnSuffixPtr 128 env.back.d0 env.back.d1) env.words.token1 ≤
    except64th (burnFinal1Need sevm env.body.memory 128 env.words env.back.d0 env.back.d1 env.back.e0
        (g + 64) (wethBalanceSkel sevm env.back.e0 (burnFinal1Stack env.words [0x89afcb44] env.back.e0)
          (burnFinal1Mem sevm env.body.memory 128 env.words env.back.d0 env.back.d1 env.back.e0)
          (burnSuffixPtr 128 env.back.d0 env.back.d1) env.words.token1) +
      balUsed sevm env.back.e0 (burnFinal1Stack env.words [0x89afcb44] env.back.e0)
        (burnFinal1Mem sevm env.body.memory 128 env.words env.back.d0 env.back.d1 env.back.e0)
        (burnSuffixPtr 128 env.back.d0 env.back.d1) env.words.token1)

end W1

/-- **C4(b), the burn liveness row with WETH9 as token1.**  As `pair_history_burn_live`, from the
joint checkpoint, with WETH9's initial query, transfer and final query removed (pinned in `callee`
to the legs WETH9's code determines).  What stays is X = token0's records, the factory record, the
Pair's charges and sentries, the LP rows' HASH-T, the frame's call depth, HASH-T over X's children
and the factory query's child, and the legs' gas sentries. -/
theorem pair_weth9_history_burn_live_one {pair weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop} {KP : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ .one checkpoint.state)
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
    (callee : BurnEnvW1 sevm pre g) (sentries : callee.WethSentries)
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace KP)
      (lpMintTouched sevm.currentTarget ++ lpMintTouched callee.feeTo))
    (xFresh : callee.XFresh weth (historyKeyUniverse weth trace K₀)
      (WriterExtend (pairHistoryUniverse pair trace KP)
        (lpMintTouched sevm.currentTarget ++ lpMintTouched callee.feeTo))) :
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
  obtain ⟨-, finish, K', replayed, -, noAllow⟩ := pair_weth9_joint .one trace joint pairFresh
    wethFresh factoryInstalled factoryNotSystem
  have futureCode := (pair_history_replayed trace joint.pairCode joint.pairRep pairFresh).1
  obtain ⟨-, tokens⟩ := replayed.fixed joint.unlocked
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.pairCode factoryInstalled
      joint.pairNonzero factoryNotSystem)
  obtain ⟨-, sumFuture, footFuture⟩ := Blanc.Lift.Weth9.weth9_history_footprint_universe
    trace joint.wethCode joint.sumNof joint.wethFoot wethFresh
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
  -- WETH9 and X at the frame
  obtain ⟨code, token, -, -⟩ := pair_weth9_frame .one trace joint pairFresh wethFresh
    factoryInstalled factoryNotSystem state
  have ne : sevm.currentTarget ≠ weth := target ▸ joint.apart
  have pairNe : weth ≠ sevm.currentTarget := fun h => ne h.symm
  have np : sevm.benvStat.rules.isPrecomp weth = false :=
    propext ⟨fun h => absurd h (joint.wethNotPrecompile _ fork), fun h => absurd h Bool.false_ne_true⟩
  have tok1 : (burnT1 sevm pre &&& burnAddrMask).toAdr = weth := by
    unfold burnT1
    rw [and_burnAddrMask, burnAddrMask_and, toAdr_toB256, toAdr_toB256]
    change ((Devm.getStor (afterSload sevm (burnReservedWorld sevm pre) 6)
      sevm.currentTarget).get 7).toAdr = weth
    rw [afterSload_getStor]
    change ((burnReservedWorld sevm pre).getStorVal sevm.currentTarget 7).toAdr = weth
    rw [burnReservedWorld_slot (by decide), target]
    exact token
  have tok0 : (burnT0 sevm pre).toAdr ≠ weth := by
    unfold burnT0
    rw [burnAddrMask_and, toAdr_toB256, burnReservedWorld_slot (by decide)]
    obtain ⟨-, -, -, slot6, -⟩ := rep.fixed
    change ((pre.getStor sevm.currentTarget).get 6).toAdr ≠ weth
    have token1 : st₀.token1 = weth := joint.token
    rw [slot6, tokens.1, ← token1]
    exact joint.distinct
  -- WETH9's footprint from the history's end to X's initial query's result
  have fPre : WethFootAt weth (historyKeyUniverse weth trace K₀) pre :=
    ⟨code, by rw [state]; exact footFuture, by rw [state]; exact sumFuture⟩
  have keepsC0 : WethKeeps weth pre (burnCall0World sevm pre) :=
    (burnRead0World_keeps sevm pre ne).trans (WethKeeps.access _ _)
  have fC0 : WethFootAt weth (historyKeyUniverse weth trace K₀) callee.readPre :=
    (fPre.keeps keepsC0 (burnCall0World_bal sevm pre)).keeps (WethKeeps.ofSt _ _ _ _)
      (BalKeeps.ofSt _ _ _ _)
  have fD0 := fC0.static callee.initial.call0 fork ne (fun g c rest h => by
    simp only [BurnEnvW1.readPre, St, Devm.setMach_stack, List.cons.injEq] at h
    rw [← h.2.1]
    exact tok0) xFresh.read
  -- the WETH9 query
  have readFst : (burnWethRead1 sevm pre callee.d0 [0x89afcb44]
      (burnFee1Gas sevm pre callee.d0 [0x89afcb44] callee.factoryGas)).1 = callee.d1 :=
    (congrArg Prod.fst callee.read).symm
  have readSnd : (burnWethRead1 sevm pre callee.d0 [0x89afcb44]
      (burnFee1Gas sevm pre callee.d0 [0x89afcb44] callee.factoryGas)).2 = callee.callGas1 :=
    (congrArg Prod.snd callee.read).symm
  have specR := burnWethRead1_spec (R := [0x89afcb44])
    (T1 := burnFee1Gas sevm pre callee.d0 [0x89afcb44] callee.factoryGas) fork depth
    (by rw [tok1]; exact fD0.code) (by rw [tok1]; exact np) (by decide)
    (by rw [readSnd]; exact sentries.fitsRead) sentries.roomRead
  dsimp only at specR
  rw [readFst, readSnd] at specR
  obtain ⟨code1, call1, success1, long1, returnedGas1, reply1⟩ := specR
  have returnedGas1' : callee.d1.gasLeft = callee.fee.gas + 64 := by
    rw [callee.fee_gas]
    exact returnedGas1
  have d1State : callee.d1.state = callee.d0.state := by
    rw [← readFst]
    unfold burnWethRead1
    rw [wethReadLeg_state]
  -- the guards
  have guards : BurnForwardGuards (WriterExtend K' (lpMintTouched sevm.currentTarget)) finish sevm
      pre callee.d0 callee.d1 callee.dF callee.back.e0 callee.back.e1 :=
    burnGuards_of_model long1 repOwn inj apart subOwn feeRow conditions
  have guardsCopy := guards
  obtain ⟨-, nonstatic, ⟨fee, feeAccepted, amount0, amount1, burnPost, events, priced, positive0,
    positive1, burned⟩, fresh, -, -⟩ := guardsCopy
  -- the locked state at `d1` (as `burnPc0_exact`)
  obtain ⟨bound0, bound1⟩ := burnR_bounds sevm pre
  have stor0 := compiled_staticcall_stor fork callee.initial.call0
  have stor1 := compiled_staticcall_stor fork call1
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
  have reply1m : PtrMem 128 192 (burnMem2 sevm callee.d0 callee.d1) :=
    balanceReplyMemory_ptr callee.d1.returnData (balanceRequestMemory_ptr reply0m sevm.currentTarget)
  obtain ⟨nonzero0, nonzero1, -⟩ := burnFeePricing_exact
    (len := callee.d1.returnData.length.toB256) (discarded := 0) fork reply1m (by decide) d1Rep
    tracked nonstatic bound0 bound1 callee.fee feeAccepted fresh priced positive0 positive1 burned
  obtain ⟨amountLe, Kb, stb, repB, unlockedB, factoryB, subB⟩ := burnPriced_lockedRep fork reply1m
    (by decide) d1Rep tracked nonstatic bound0 bound1 callee.fee feeAccepted fresh priced burned
  have tok1' : (burnT1 sevm pre).toAdr = weth := by
    rw [← tok1, and_burnAddrMask, toAdr_toB256]
  have token1W : (swapTokenWord callee.words.token1).toAdr = weth := by
    change (swapTokenWord (burnT1 sevm pre)).toAdr = weth
    unfold swapTokenWord
    rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask by decide,
      and_mask_word, toAdr_toB256]
    exact tok1'
  have token0W : (swapTokenWord callee.words.token0).toAdr ≠ weth := by
    change (swapTokenWord (burnT0 sevm pre)).toAdr ≠ weth
    rw [swapTokenWord_burnT0]
    exact tok0
  -- WETH9's account and footprint at the suffix's entry world
  have k01 : WethKeeps weth callee.d0 callee.d1 :=
    ⟨congrArg (fun s : Jaune.State => s.getCode weth) d1State,
      congrArg (fun s : Jaune.State => s.getStor weth) d1State⟩
  have keepsD0 : WethKeeps weth pre callee.d0 :=
    keepsC0.trans (WethKeeps.staticcall fork callee.initial.call0
      (weth9_code_toList_ne (keepsC0.1.trans code)))
  have keepsD1 := keepsD0.trans k01
  have keepsB : WethKeeps weth pre callee.body := keepsD1.trans (burnBodyWorld_keeps (b := pre)
    (d0 := callee.d0) fork ne callee.fee.call (weth9_code_toList_ne (keepsD1.1.trans code)))
  have fD1 := fD0.keeps k01 (BalKeeps.ofState d1State)
  have factoryPreF : (pre.state.getCode st₀.factory) = UniswapV2Factory.code := by
    rw [state]
    exact UniswapV2Factory.code_eq_of_toList (history_code_of_image trace factoryInstalled)
  have wethFactory : weth ≠ st₀.factory := weth_ne_factory code factoryPreF
  have fFp : WethFootAt weth (historyKeyUniverse weth trace K₀) callee.factoryPre :=
    (fD1.keeps (feeFactoryCallWorld_keeps sevm callee.d1).1
      (feeFactoryCallWorld_keeps (w := weth) sevm callee.d1).2).keeps (WethKeeps.ofSt _ _ _ _)
      (BalKeeps.ofSt _ _ _ _)
  have fF := fFp.static callee.fee.call fork ne (fun g c rest h => by
    simp only [BurnEnvW1.factoryPre, St, Devm.setMach_stack, List.cons.injEq] at h
    rw [← h.2.1]
    obtain ⟨-, -, slot5, -⟩ := d1Rep.fixed
    unfold feeFactoryWord feeBurnWorld
    rw [toAdr_toB256]
    change ((Devm.getStor (afterSload sevm callee.d1 _) sevm.currentTarget).get 5).toAdr ≠ weth
    rw [afterSload_getStor, slot5]
    show finish.factory ≠ weth
    rw [tokens.2.2]
    exact wethFactory.symm) xFresh.factory
  have fB : WethFootAt weth (historyKeyUniverse weth trace K₀) callee.body :=
    fF.keeps (burnBodyWorld_fromF sevm pre callee.d0 callee.d1 callee.dF ne).1
      (burnBodyWorld_fromF (w := weth) sevm pre callee.d0 callee.d1 callee.dF ne).2
  -- codes at the suffix's entry world
  have codeB : ∀ a, (pre.state.getCode a).toList ≠ [] →
      callee.body.state.getCode a = pre.state.getCode a := by
    intro a nonempty
    have c0 : callee.readPre.state.getCode a = pre.state.getCode a := by
      rw [BurnEnvW1.readPre, St, Devm.setMach_state]
      exact (burnCall0World_bal sevm pre).2 a
    have cD0 : callee.d0.state.getCode a = pre.state.getCode a :=
      (runCompiled_codePreserve callee.initial.call0 a
        (show (callee.readPre.state.getCode a).toList ≠ [] by rw [c0]; exact nonempty)).trans c0
    have cD1 : callee.d1.state.getCode a = pre.state.getCode a := by rw [d1State]; exact cD0
    have cFp : callee.factoryPre.state.getCode a = pre.state.getCode a := by
      rw [BurnEnvW1.factoryPre, St, Devm.setMach_state]
      exact ((feeFactoryCallWorld_keeps (w := weth) sevm callee.d1).2.2 a).trans cD1
    have cF : callee.dF.state.getCode a = pre.state.getCode a :=
      (runCompiled_codePreserve callee.fee.call a
        (show (callee.factoryPre.state.getCode a).toList ≠ [] by rw [cFp]; exact nonempty)).trans cFp
    exact ((burnBodyWorld_fromF (w := weth) sevm pre callee.d0 callee.d1 callee.dF ne).2.2 a).trans cF
  have pairPre : pre.state.getCode sevm.currentTarget = UniswapV2Pair.code := by
    rw [state, target]
    exact futureCode
  have pairB : callee.body.state.getCode sevm.currentTarget = UniswapV2Pair.code := by
    rw [codeB _ (by rw [pairPre]; exact UniswapV2Pair.pairSem.ne_nil rfl), pairPre]
  have factoryStb : stb.factory = st₀.factory := factoryB.trans tokens.2.2
  have factoryBody : callee.body.state.getCode stb.factory = UniswapV2Factory.code := by
    rw [factoryStb, codeB _ (by rw [factoryPreF]; exact UniswapV2Factory.factorySem.ne_nil rfl),
      factoryPreF]
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
  -- the Pair's WETH9 balance at the entry world covers `amount1`
  have balance : callee.words.amount1 ≤
      callee.body.getStorVal weth (Weth9.balSlot sevm.currentTarget) := by
    have answer : feeBurnBalance1 (burnMem2 sevm callee.d0 callee.d1) =
        Bytes.toB256 (callee.d1.returnData.take 32) :=
      balanceReplyMemory_word reply0m.wf sevm.currentTarget callee.d1.returnData long1
    have le : callee.words.amount1 ≤ feeBurnBalance1 (burnMem2 sevm callee.d0 callee.d1) := amountLe
    rw [answer, reply1, toB256_take_toBytes, tok1, keepsD0.getStorVal] at le
    rw [keepsB.getStorVal]
    exact le
  -- the WETH9 transfer after X's
  have zeroB : ∀ g', Weth9Token.weth9Book.allow (Weth9.ledger (historyKeyUniverse weth trace K₀)
      (callee.body.state.getStor weth)) sevm.currentTarget g' = 0 := by
    intro g'
    have storB : callee.body.state.getStor weth = future.state.getStor weth := by
      rw [← state]
      exact keepsB.2
    rw [storB, target]
    show (Weth9.trackedAllow _ _ pair g').toNat = 0
    by_cases h : historyKeyUniverse weth trace K₀ (.allow pair g')
    · rw [Weth9.trackedAllow_self h, noAllow g' h]
      rfl
    · rw [Weth9.trackedAllow_of_not h]
      rfl
  have legFst : (burnWethLeg1 sevm callee.back.d0 callee.body.memory 128 callee.words [0x89afcb44]
      callee.back.balanceGas0).1 = callee.back.d1 := (congrArg Prod.fst callee.back.leg).symm
  have legSnd : (burnWethLeg1 sevm callee.back.d0 callee.body.memory 128 callee.words [0x89afcb44]
      callee.back.balanceGas0).2 = callee.back.callGas1 := (congrArg Prod.snd callee.back.leg).symm
  have subP : ∀ k, Kb k → WriterExtend (pairHistoryUniverse pair trace KP) rows k :=
    subB _ subOwn feeRow ownRow
  have transfer1 := burnWethLeg1_spec_afterX (b := callee.body) (U := historyKeyUniverse weth trace K₀)
    (stL := stb) fork nonstatic depth callee.back.transfer0 pricedMem pricedSentinel (by decide)
    (by decide) nonzero0 (by decide) token1W token0W ne fB.code fB.foot
    (by rw [target]; exact Or.inl joint.tracked) zeroB pairB
    (by
      show WriterRep Kb ((burnBodyWorld sevm pre callee.d0 callee.d1 callee.dF).getStor
        sevm.currentTarget) stb
      rw [burnBodyWorld_def]
      exact repB)
    (by rw [unlockedB]; show (0 : B256) ≠ 1; decide) factoryBody
    (by rw [target]; exact joint.pairNonzero) fB.bound balance xFresh.xWeth
    (fun {_ _ _ _} spawn enter child =>
      freshKeys_of_wider inj apart subP (xFresh.xPair spawn enter child))
    np (by rw [legSnd]; exact sentries.fitsLeg) sentries.roomLeg
  rw [legFst, legSnd] at transfer1
  -- the final query
  obtain ⟨wf2, width2⟩ := burnSuffix_layout (w := callee.words) fork pricedMem pricedSentinel
    (by decide) (by decide) nonzero0 nonzero1 (by decide) callee.back.transfer0 transfer1
  have codeT0 : callee.back.d0.state.getCode weth = Weth9.code :=
    (runCompiled_codePreserve callee.back.transfer0.call weth
      (weth9_code_toList_ne fB.code)).trans fB.code
  have codeT1 : callee.back.d1.state.getCode weth = Weth9.code :=
    (runCompiled_codePreserve transfer1.call weth (weth9_code_toList_ne codeT0)).trans codeT0
  have codeE0 : callee.back.e0.state.getCode weth = Weth9.code :=
    weth9Code_of_runCompiled callee.back.first.call (weth9Code_temporal codeT1)
  have finFst : (burnWethFinal1 sevm callee.body.memory 128 callee.words [0x89afcb44] callee.back.d0
      callee.back.d1 callee.back.e0 (g + 64)).1 = callee.back.e1 :=
    (congrArg Prod.fst callee.back.final).symm
  have finSnd : (burnWethFinal1 sevm callee.body.memory 128 callee.words [0x89afcb44] callee.back.d0
      callee.back.d1 callee.back.e0 (g + 64)).2 = callee.back.balanceGas1 :=
    (congrArg Prod.snd callee.back.final).symm
  have specF := burnWethFinal1_spec (M := callee.body.memory) (p0 := 128) (w := callee.words)
    (R := [0x89afcb44]) (d0 := callee.back.d0) (d1 := callee.back.d1) (e0 := callee.back.e0)
    (G := g + 64) fork depth (by rw [token1W]; exact codeE0) (by rw [token1W]; exact np) wf2 width2
    (by decide) (by rw [finSnd]; exact sentries.fitsFinal) sentries.roomFinal
  rw [finFst, finSnd] at specF
  obtain ⟨second, -⟩ := specF
  -- the whole environment and the run
  let env : BurnForwardEnv sevm pre g :=
    ⟨callee.d0, callee.d1, callee.dF, callee.back.toBack transfer1 second, callee.fee,
      callee.initial.toInitial code1 call1 success1 long1 returnedGas1'⟩
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

/-! ## Non-vacuity of the pins -/

/-- **The token1 burn row's pins are solvable (A17).**  For any free values (X's initial result
`d0`, the factory result `dF` and call gas `factoryGas`; then, inside the suffix, X's transfer result
`d0'`, X's final result `e0`, X's final query's call gas `balanceGas0`, the residual `G`), values of
the pinned fields satisfying `read`, `back.leg` and `back.final` exist: each pin's right side reads
only those free values and earlier pins.  With `BurnEnvW1.fee_gas`, the read's residual is the fee
record's own entry gas, so no pin is circular through a record. -/
theorem burnEnvW1_pins_solvable (sevm : Sevm) (b d0 dF : Devm) (factoryGas : Nat) :
    ∃ (d1 : Devm) (callGas1 : Nat),
      (d1, callGas1) = burnWethRead1 sevm b d0 [0x89afcb44]
        (burnFee1Gas sevm b d0 [0x89afcb44] factoryGas) ∧
      ∀ (d0' e0 : Devm) (balanceGas0 G : Nat), ∃ (d1' : Devm) (callGas1' : Nat) (e1 : Devm)
        (balanceGas1 : Nat),
        (d1', callGas1') = burnWethLeg1 sevm d0' (burnBodyWorld sevm b d0 d1 dF).memory 128
          (burnBodyWords sevm b d0 d1 dF) [0x89afcb44] balanceGas0 ∧
        (e1, balanceGas1) = burnWethFinal1 sevm (burnBodyWorld sevm b d0 d1 dF).memory 128
          (burnBodyWords sevm b d0 d1 dF) [0x89afcb44] d0' d1' e0 G :=
  ⟨_, _, rfl, fun _ _ _ _ => ⟨_, _, _, _, rfl, rfl⟩⟩

end Blanc.Composition.UniswapV2PairWeth9Joint
