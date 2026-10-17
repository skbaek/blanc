import Blanc.Composition.UniswapV2PairWeth9SyncLive
import Blanc.Composition.UniswapV2PairWeth9LegsSkim
import Blanc.Lift.UniswapV2Pair.SkimForwardKeep

/-!
# C4(b): the skim liveness row with WETH9 = token0 (U8d)

`pair_history_skim_live` takes `SkimForwardEnv`: both `balanceOf(pair)` queries and both
transfer `CALL`s.  With WETH9 as token0, its query (`code0`, `qenv0`) and its transfer (`tenv0`)
are WETH9's own runs: their results and call gases are pinned in order (`gasT0`, `read`, `leg`) to
`skimLeg0Gas`, `skimWethRead0` and `skimWethLeg0` (U8b2, U8f), and their premises are discharged
from the history: WETH9's code at the token the Pair loads, WETH9 not a precompile, and the
transfer's amount `answer − reserve0`
covered by the Pair's WETH9 balance (`skimWethLeg0_of_read`), from C3's `reserve0 ≤` the Pair's
stored WETH9 balance word at the history's end (`pair_weth9_frame`).  The frame's call depth and
mutability and the legs' gas sentries are premises.  Token1's query and transfer, the lock
sentries and the first transfer's trace-local HASH-T (`FirstCallFresh`) stay.

The WETH9 = token1 row needs X-leg quiescence (U8c) and is not here.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.UniswapV2Pair

/-- **Skim's callee environment with WETH9 as token0**: `SkimForwardEnv` with WETH9's query and
transfer records replaced by pins to the legs WETH9's code determines.  The pins are definitions in
order: `gasT0` fixes the transfer's call gas from the second query's call gas `callGasQ1` (on the
query's gas-free skeleton, `skimLeg0Gas`), `read` fixes the query's result and call gas from it, and
`leg` fixes the transfer's result from those.  Any choice of the other fields extends to an
environment satisfying all three. -/
structure SkimCalleeW0 (sevm : Sevm) (b : Devm) (g : Nat) where
  qd1 : Devm
  dt1 : Devm
  callGasQ1 : Nat
  callGasT1 : Nat
  callGasT0 : Nat
  qd0 : Devm
  callGasQ0 : Nat
  dt0 : Devm
  gasT0 : callGasT0 = skimLeg0Gas sevm b callGasQ1
  read : (qd0, callGasQ0) = skimWethRead0 sevm b callGasT0
  leg : dt0 = (skimWethLeg0 sevm b qd0 callGasQ1).1
  sentry : gCallStipend < ((((callGasQ0 + 5) +
      sloadCost sevm (syncLockedWorld sevm b) 6 +
      sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7 +
      sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8 +
      swapStoreCost 96 128 + swapStoreCost 160 132 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 186)) +
      sstoreCost sevm (afterSload sevm b 12) 12 0)
  sentryU : gCallStipend < (g + 11) + sstoreCost sevm dt1 12 1
  code1 : ((((afterSload sevm dt0 8).getCode
      ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
        skimToken1 sevm b)).toAdr)).size.toB256) ≠ 0
  qenv1 : SkimQueryEnv sevm
      (temporalAccountAccessBase (afterSload sevm dt0 8)
        ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
          skimToken1 sevm b)).toAdr)
      (skimRequestMemory
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
          128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
          (skimToWord sevm) dt0.returnData)
        (swapMovedPointer 128 dt0.returnData) sevm.currentTarget)
      (swapMovedPointer 128 dt0.returnData)
      (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
        skimToken1 sevm b)
      (((swapMovedPointer 128 dt0.returnData) + 36) :: 0x70a08231 ::
        (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
          skimToken1 sevm b) ::
        skimReserve1Word (dt0.getStorVal sevm.currentTarget 8) :: 0x1a26 ::
        skimToWord sevm :: skimToken1 sevm b :: 0x1aca :: skimToken1 sevm b ::
        skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      qd1 callGasQ1 (((callGasT1 +
        safeTransferPreCharge (((skimRequestMemory
          (swapTransferMemory
            (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
            128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
            (skimToWord sevm) dt0.returnData)
          (swapMovedPointer 128 dt0.returnData) sevm.currentTarget).extends
          [((swapMovedPointer 128 dt0.returnData).toNat, 36),
            ((swapMovedPointer 128 dt0.returnData).toNat, 32)]).write
          (swapMovedPointer 128 dt0.returnData).toNat
          (qd1.returnData.take 32)).size
          (swapMovedPointer 128 dt0.returnData) + 12)) + 80)
  tenv1 : SwapTransferCallForward sevm qd1
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      (((skimRequestMemory
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
          128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
          (skimToWord sevm) dt0.returnData)
        (swapMovedPointer 128 dt0.returnData) sevm.currentTarget).extends
        [((swapMovedPointer 128 dt0.returnData).toNat, 36),
          ((swapMovedPointer 128 dt0.returnData).toNat, 32)]).write
        (swapMovedPointer 128 dt0.returnData).toNat (qd1.returnData.take 32))
      ((((skimRequestMemory
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
          128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
          (skimToWord sevm) dt0.returnData)
        (swapMovedPointer 128 dt0.returnData) sevm.currentTarget).extends
        [((swapMovedPointer 128 dt0.returnData).toNat, 36),
          ((swapMovedPointer 128 dt0.returnData).toNat, 32)]).write
        (swapMovedPointer 128 dt0.returnData).toNat (qd1.returnData.take 32)).size)
      (swapMovedPointer 128 dt0.returnData)
      (Bytes.toB256 (qd1.returnData.take 32) -
        skimReserve1Word (dt0.getStorVal sevm.currentTarget 8))
      (skimToWord sevm) (skimToken1 sevm b) 0x1aca callGasT1 (g +
        sstoreCost sevm dt1 12 1 + 22) dt1

section W0

variable {sevm : Sevm} {b : Devm} {g : Nat}

def SkimCalleeW0.gas (env : SkimCalleeW0 sevm b g) : Nat :=
  (env.callGasQ0 + 5) +
      sstoreCost sevm (afterSload sevm b 12) 12 0 +
      sloadCost sevm (syncLockedWorld sevm b) 6 +
      sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7 +
      sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8 +
      swapStoreCost 96 128 + swapStoreCost 160 132 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 193 +
      sloadCost sevm b 12 + 23 + 63 + 123 + 63

def SkimCalleeW0.post (env : SkimCalleeW0 sevm b g) : Devm :=
  St (afterSstore sevm env.dt1 12 1) [0xbc25cf77]
      (swapTransferMemory
        (((skimRequestMemory
          (swapTransferMemory
            (balanceReplyMemory getterInitMemory sevm.currentTarget env.qd0.returnData)
            128 (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b)
            (skimToWord sevm) env.dt0.returnData)
          (swapMovedPointer 128 env.dt0.returnData) sevm.currentTarget).extends
          [((swapMovedPointer 128 env.dt0.returnData).toNat, 36),
            ((swapMovedPointer 128 env.dt0.returnData).toNat, 32)]).write
          (swapMovedPointer 128 env.dt0.returnData).toNat (env.qd1.returnData.take 32))
        (swapMovedPointer 128 env.dt0.returnData)
        (Bytes.toB256 (env.qd1.returnData.take 32) -
          skimReserve1Word (env.dt0.getStorVal sevm.currentTarget 8))
        (skimToWord sevm) env.dt1.returnData) g

def SkimCalleeW0.balance0 (env : SkimCalleeW0 sevm b g) : B256 :=
  Bytes.toB256 (env.qd0.returnData.take 32)

def SkimCalleeW0.balance1 (env : SkimCalleeW0 sevm b g) : B256 :=
  Bytes.toB256 (env.qd1.returnData.take 32)

end W0

/-- The staged world of skim's first transfer `CALL` (`SkimForwardEnv.firstCallPre`). -/
def SkimCalleeW0.firstCallPre {sevm : Sevm} {b : Devm} {g : Nat}
    (env : SkimCalleeW0 sevm b g) : Devm :=
  St env.qd0 (env.callGasT0.toB256 ::
      (skimToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      0 :: (128 + 164) :: 68 :: (128 + 164) :: 0 :: (68 + (128 + 164)) ::
      (skimToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b) ::
      skimToWord sevm :: skimToken0 sevm b :: 0x1a2b ::
      skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
    (safeTransfer_dynamicCallMemory
      (balanceReplyMemory getterInitMemory sevm.currentTarget env.qd0.returnData) 128
      (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b) (skimToWord sevm))
    env.callGasT0

/-- Trace-local HASH-T for skim's first transfer (`SkimForwardEnv.FirstCallFresh`). -/
def SkimCalleeW0.FirstCallFresh {sevm : Sevm} {b : Devm} {g : Nat}
    (env : SkimCalleeW0 sevm b g) (U : WriterKey → Prop) : Prop :=
  ∃ R : Exec.Deriv, Blanc.Lift.StepIn R sevm env.firstCallPre (.exec .call) env.dt0 ∧
    WriterFreshKeys U (pairTraceKeys sevm.currentTarget R)

/-- The W0 environment with WETH9's records is the whole skim environment. -/
def SkimCalleeW0.toEnv {sevm : Sevm} {b : Devm} {g : Nat} (env : SkimCalleeW0 sevm b g)
    (code0 : (((skimCachedWorld sevm b).getCode (skimToken0 sevm b).toAdr).size.toB256) ≠ 0)
    (qenv0 : SkimQueryEnv sevm
      (temporalAccountAccessBase (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr)
      (balanceRequestMemory getterInitMemory sevm.currentTarget) 128
      (skimToken0 sevm b)
      (164 :: 0x70a08231 :: skimToken0 sevm b :: skimReserve0 sevm b :: 0x1a26 ::
        skimToWord sevm :: skimToken0 sevm b :: 0x1a2b :: skimToken1 sevm b ::
        skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      env.qd0 env.callGasQ0 (((env.callGasT0 +
        safeTransferPreCharge (balanceReplyMemory getterInitMemory sevm.currentTarget
          env.qd0.returnData).size 128 + 12)) + 80))
    (tenv0 : SwapTransferCallForward sevm env.qd0
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      (balanceReplyMemory getterInitMemory sevm.currentTarget env.qd0.returnData)
      ((balanceReplyMemory getterInitMemory sevm.currentTarget env.qd0.returnData).size)
      128 (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b)
      (skimToWord sevm) (skimToken0 sevm b) 0x1a2b env.callGasT0
      (skimLeg0Next sevm b env.qd0 env.callGasQ1 env.dt0) env.dt0) :
    SkimForwardEnv sevm b g :=
  { qd0 := env.qd0, dt0 := env.dt0, qd1 := env.qd1, dt1 := env.dt1, callGasQ0 := env.callGasQ0,
    callGasT0 := env.callGasT0, callGasQ1 := env.callGasQ1, callGasT1 := env.callGasT1,
    code0 := code0, sentry := env.sentry, sentryU := env.sentryU, qenv0 := qenv0, tenv0 := tenv0,
    code1 := env.code1, qenv1 := env.qenv1, tenv1 := env.tenv1 }

theorem skimCachedWorld_keeps (sevm : Sevm) (pre : Devm) {w : Adr} (ne : sevm.currentTarget ≠ w) :
    WethKeeps w pre (skimCachedWorld sevm pre) :=
  ((((WethKeeps.afterSload sevm pre 12).trans (WethKeeps.afterSstore ne _ 12 0)).trans
    (WethKeeps.afterSload sevm _ 6)).trans (WethKeeps.afterSload sevm _ 7)).trans
    (WethKeeps.afterSload sevm _ 8)

theorem skimReserve0_eq (sevm : Sevm) (pre : Devm) :
    skimReserve0 sevm pre = reserve0Read ((pre.getStor sevm.currentTarget).get 8) := by
  change skimReserveMask &&& (Devm.getStor (afterSload sevm (afterSload sevm
    (afterSstore sevm (afterSload sevm pre 12) 12 0) 6) 7) sevm.currentTarget).get 8 = _
  rw [afterSload_getStor, afterSload_getStor, afterSstore_getStor_self,
    Stor.get_set_ne _ (by decide : (12 : B256) ≠ 8), afterSload_getStor, B256.and_comm]
  rfl

/-- **C4(b), the skim liveness row with WETH9 as token0.**  As `pair_history_skim_live`, from the
joint checkpoint, with WETH9's query and transfer records removed (pinned in order by
`callee.gasT0`, `callee.read` and `callee.leg` to `skimLeg0Gas`, `skimWethRead0` and
`skimWethLeg0`).  The transfer's balance condition comes from C3.  What stays is token1's
records, the lock sentries, the first transfer's trace-local HASH-T,
the frame's call depth and mutability, and the legs' gas sentries. -/
theorem pair_weth9_history_skim_live_zero {pair weth : Adr} {cfg : ChainConfig}
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
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (static : sevm.isStatic = false) (depth : sevm.depth ≠ 0)
    (callee : SkimCalleeW0 sevm pre g)
    (fitsRead : callee.callGasQ0 < 2 ^ 256)
    (roomRead : balUsed sevm (skimCachedWorld sevm pre) (skimRead0Stack sevm pre) getterInitMemory
        128 (skimToken0 sevm pre) ≤
      except64th (skimRead0Need sevm callee.callGasT0 (wethBalanceSkel sevm
          (skimCachedWorld sevm pre) (skimRead0Stack sevm pre) getterInitMemory 128
          (skimToken0 sevm pre)) +
        balUsed sevm (skimCachedWorld sevm pre) (skimRead0Stack sevm pre) getterInitMemory 128
          (skimToken0 sevm pre)))
    (fits : callee.callGasT0 < 2 ^ 256)
    (room : skimLeg0Used sevm pre callee.qd0 + gCallStipend ≤
      except64th (skimLeg0Need sevm pre callee.qd0 callee.callGasQ1 +
        skimLeg0Used sevm pre callee.qd0))
    (firstFresh : callee.FirstCallFresh (pairHistoryUniverse pair trace KP)) :
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
  have hq : (skimWethRead0 sevm pre callee.callGasT0).1 = callee.qd0 :=
    (congrArg Prod.fst callee.read).symm
  have hq' : (skimWethRead0 sevm pre callee.callGasT0).2 = callee.callGasQ0 :=
    (congrArg Prod.snd callee.read).symm
  have hl : (skimWethLeg0 sevm pre callee.qd0 callee.callGasQ1).1 = callee.dt0 := callee.leg.symm
  have hl' : (skimWethLeg0 sevm pre callee.qd0 callee.callGasQ1).2 = callee.callGasT0 := by
    rw [← hq, skimWethLeg0_read, callee.gasT0]
    rfl
  obtain ⟨code, token, -, reserve⟩ := pair_weth9_frame .zero trace joint pairFresh wethFresh
    factoryInstalled factoryNotSystem state
  have ne : sevm.currentTarget ≠ weth := target ▸ joint.apart
  have keeps := skimCachedWorld_keeps sevm pre ne
  have tok : (skimToken0 sevm pre).toAdr = weth := by
    unfold skimToken0
    rw [toAdr_toB256, syncLockedWorld_slot (by decide), target]
    exact token
  have wcode : (skimCachedWorld sevm pre).state.getCode (skimToken0 sevm pre).toAdr =
      Weth9.code := by
    rw [tok]
    exact keeps.1.trans code
  have np : sevm.benvStat.rules.isPrecomp (skimToken0 sevm pre).toAdr = (false = true) := by
    rw [tok]
    exact notPrecompile_of_joint joint fork
  have cover : skimReserve0 sevm pre ≤ (skimCachedWorld sevm pre).getStorVal
      (skimToken0 sevm pre).toAdr (Weth9.balSlot sevm.currentTarget) := by
    rw [tok, keeps.getStorVal, skimReserve0_eq, B256.le_iff_toNat_le_toNat, target]
    exact reserve
  have fitsRead' : (skimWethRead0 sevm pre callee.callGasT0).2 < 2 ^ 256 := by
    rw [hq']
    exact fitsRead
  obtain ⟨code0, qenv0, -⟩ := skimWethRead0_spec fork depth wcode np fitsRead' roomRead
  rw [hq, hq'] at qenv0
  have tenv0 := skimWethLeg0_of_read (callGasQ1 := callee.callGasQ1) fork static depth wcode np
    cover fitsRead' roomRead (by rw [hq, hl']; exact fits) (by rw [hq]; exact room)
  rw [hq, hl, hl'] at tenv0
  exact pair_history_skim_live trace joint.pairCode joint.pairRep pairFresh target state codeEq
    fork output representable value size abi selector (callee.toEnv code0 qenv0 tenv0) firstFresh

end Blanc.Composition.UniswapV2PairWeth9Joint
