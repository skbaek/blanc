import Blanc.Lift.UniswapV2Pair.SkimForward
import Blanc.Lift.UniswapV2Pair.MintForwardAccept

/-!
# Skim liveness pieces: the callee-only environment and the model's guards

`skim_bytecode_forward_consumes` (`SkimForward.lean`) takes the skim frame's callees (two
`balanceOf(pair)` queries, two transfers through the shared helper) together with the guards the
bytes check: the lock, mutability and the two checked subtractions `cover0`/`cover1`. This module
splits the callees off (`SkimForwardEnv`), states the model's skim guards at the actual answers
(`SkimModelConditions`), proves every skim the model accepts passes them
(`runTyped_skim_conditions`); the forward run from them is `SkimForwardEnv.run_of_model`.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The Pair's storage slots only lock-guarded entries write: `totalSupply` (0), the packed reserves
(8), both price accumulators (9, 10), `kLast` (11) and the lock (12). The unlocked entries
(`transfer`, `approve`, `transferFrom`, `permit`, `initialize`) write only balance, allowance and
nonce rows and the token slots. -/
def pairLockedSlots : List B256 := [0, 8, 9, 10, 11, 12]

/-- The U6 `SendOk`-shaped token-call clause: from the staged world `pre` to the settled world
`post`, a token `CALL` writes none of the Pair's lock-guarded slots.

It is no longer a premise of skim liveness, which derives the lock-guarded fields it reads instead
(`SkimForwardEnv.firstCall_keeps`, `SkimForwardKeep.lean`). -/
def NoPairWriteOutsideLock (sevm : Sevm) (pre post : Devm) : Prop :=
  ∀ k ∈ pairLockedSlots, post.getStorVal sevm.currentTarget k = pre.getStorVal sevm.currentTarget k

/-- **The callee-only skim environment**: both `balanceOf(pair)` `STATICCALL`s (`SkimQueryEnv`) and
both transfer `CALL`s through the shared helper (`SwapTransferCallForward`), each from its actual
staged state with its success, reply and returned gas, the code checks of both tokens, and the lock
and unlock sentries. Nothing about what the callees do to the Pair is part of it: that the first
`CALL` keeps the Pair's lock-guarded fields is derived (`SkimForwardEnv.firstCall_keeps`) under
trace-local HASH-T. No model acceptance fact and no successful run is part of it. -/
structure SkimForwardEnv (sevm : Sevm) (b : Devm) (g : Nat) where
  qd0 : Devm
  dt0 : Devm
  qd1 : Devm
  dt1 : Devm
  callGasQ0 : Nat
  callGasT0 : Nat
  callGasQ1 : Nat
  callGasT1 : Nat
  code0 : (((skimCachedWorld sevm b).getCode
      (skimToken0 sevm b).toAdr).size.toB256) ≠ 0
  sentry : gCallStipend < ((((callGasQ0 + 5) +
      sloadCost sevm (syncLockedWorld sevm b) 6 +
      sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7 +
      sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8 +
      swapStoreCost 96 128 + swapStoreCost 160 132 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 186)) +
      sstoreCost sevm (afterSload sevm b 12) 12 0)
  sentryU : gCallStipend < (g + 11) + sstoreCost sevm dt1 12 1
  qenv0 : SkimQueryEnv sevm
      (temporalAccountAccessBase (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr)
      (balanceRequestMemory getterInitMemory sevm.currentTarget) 128
      (skimToken0 sevm b)
      (164 :: 0x70a08231 :: skimToken0 sevm b :: skimReserve0 sevm b :: 0x1a26 ::
        skimToWord sevm :: skimToken0 sevm b :: 0x1a2b :: skimToken1 sevm b ::
        skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      qd0 callGasQ0 (((callGasT0 +
        safeTransferPreCharge (balanceReplyMemory getterInitMemory sevm.currentTarget
          qd0.returnData).size 128 + 12)) + 80)
  tenv0 : SwapTransferCallForward sevm qd0
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
      ((balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData).size)
      128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
      (skimToWord sevm) (skimToken0 sevm b) 0x1a2b callGasT0
      (((callGasQ1 + 5) +
        sloadCost sevm dt0 8 +
        swapStoreCost
          (swapTransferMemory
            (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
            128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
            (skimToWord sevm) dt0.returnData).size
          (swapMovedPointer 128 dt0.returnData).toNat +
        swapStoreCost
          (memExtSize
            (swapTransferMemory
              (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
              128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
              (skimToWord sevm) dt0.returnData).size
            (swapMovedPointer 128 dt0.returnData).toNat 32)
          ((swapMovedPointer 128 dt0.returnData) + 4).toNat +
        temporalAccountAccessCost (afterSload sevm dt0 8)
          ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
            skimToken1 sevm b)).toAdr + 171)) dt0
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

/-- The pc-zero gas: the lock, cache and request charges and the gas forwarded to the first
token query. -/
def SkimForwardEnv.gas {sevm : Sevm} {b : Devm} {g : Nat} (env : SkimForwardEnv sevm b g) : Nat :=
  (env.callGasQ0 + 5) +
      sstoreCost sevm (afterSload sevm b 12) 12 0 +
      sloadCost sevm (syncLockedWorld sevm b) 6 +
      sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7 +
      sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8 +
      swapStoreCost 96 128 + swapStoreCost 160 132 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 193 +
      sloadCost sevm b 12 + 23 + 63 + 123 + 63

/-- The halted world. -/
def SkimForwardEnv.post {sevm : Sevm} {b : Devm} {g : Nat} (env : SkimForwardEnv sevm b g) : Devm :=
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

/-- The two answers of the skim queries. -/
def SkimForwardEnv.balance0 {sevm : Sevm} {b : Devm} {g : Nat} (env : SkimForwardEnv sevm b g) : B256 :=
  Bytes.toB256 (env.qd0.returnData.take 32)

def SkimForwardEnv.balance1 {sevm : Sevm} {b : Devm} {g : Nat} (env : SkimForwardEnv sevm b g) : B256 :=
  Bytes.toB256 (env.qd1.returnData.take 32)

/-! ## The model's skim guards -/

/-- **The model's skim guards** at the two token answers, from the state `st` the frame enters: the
call is non-payable and non-static, the lock is open, and both answers cover the reserves (the two
checked subtractions). -/
def SkimModelConditions (st : State) (ctx : Context) (balance0 balance1 : B256) : Prop :=
  ctx.value = 0 ∧ ctx.isStatic = false ∧ st.unlocked = 1 ∧
  st.reserve0.val ≤ balance0.toNat ∧ st.reserve1.val ≤ balance1.toNat

/-- A successful second skim query covers the frame's reserve1. -/
theorem drive_skimBalance1_cover {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SkimLocals} {owner : Adr} {transcript : Transcript} {returndata : Bytes}
    (operation : request.operation = .balanceOf owner) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.skimBalance1 locals))
      transcript).status = .success returndata) :
    frame.current.state.reserve1.val ≤ transcript.firstWord.toNat := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, _⟩ :=
      drive_suspended_success successful
    have staticExternal : externalStatic frame request = true := by
      rw [externalStatic, kind]
      cases frame.context.isStatic <;> rfl
    have settled := Frame.settleExternal_static_frame frame fuel request result turns staticExternal
    rw [settled] at resumedSuccess
    cases decoded : decodeExternal request result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | address address =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance1 =>
        have observedWord := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded] at resumedSuccess
        by_cases backing : (frame.beginResume request).current.state.reserve1.val ≤ balance1.toNat
        · rw [shape, Transcript.firstWord, ← observedWord]
          exact backing
        · rw [ite_eq_right backing, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _
            (.sourceGuard "ds-math-sub-underflow") tail returndata resumedSuccess)

/-- A successful first skim transfer, from a locked frame, keeps reserve1 and covers it by the
second answer. -/
theorem drive_skimTransfer0_cover {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SkimLocals} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (successful : (drive fuel (.suspended frame request (.skimTransfer0 locals))
      transcript).status = .success returndata) :
    frame.current.state.reserve1.val ≤ transcript.ownTail.firstWord.toNat := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, _⟩ :=
      drive_suspended_success successful
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    cases decoded : decodeExternal request result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | address address =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word value =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess
        have cover := drive_skimBalance1_cover rfl rfl resumedSuccess
        have kept : (frame.settleExternal fuel request result turns).current.state.reserve1 =
            frame.current.state.reserve1 := congrArg (fun c => c.2.1.2) core
        rw [shape, Transcript.ownTail]
        have h : ((frame.settleExternal fuel request result turns).beginResume
            request).current.state.reserve1 = frame.current.state.reserve1 := kept
        rw [← h]
        exact cover

/-- A successful first skim query, from a locked frame, covers both reserves by the two answers. -/
theorem drive_skimBalance0_cover {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SkimLocals} {owner : Adr} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (operation : request.operation = .balanceOf owner) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.skimBalance0 locals))
      transcript).status = .success returndata) :
    frame.current.state.reserve0.val ≤ transcript.firstWord.toNat ∧
      frame.current.state.reserve1.val ≤ transcript.ownTail.ownTail.firstWord.toNat := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, _⟩ :=
      drive_suspended_success successful
    have staticExternal : externalStatic frame request = true := by
      rw [externalStatic, kind]
      cases frame.context.isStatic <;> rfl
    have settled := Frame.settleExternal_static_frame frame fuel request result turns staticExternal
    rw [settled] at resumedSuccess
    cases decoded : decodeExternal request result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | address address =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance0 =>
        have observedWord := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded] at resumedSuccess
        by_cases backing : (frame.beginResume request).current.state.reserve0.val ≤ balance0.toNat
        · rw [ite_eq_left backing, Frame.suspend] at resumedSuccess
          have cover1 := drive_skimTransfer0_cover (frame := frame.beginResume request) locked
            resumedSuccess
          refine ⟨?_, ?_⟩
          · rw [shape, Transcript.firstWord, ← observedWord]
            exact backing
          · rw [shape, Transcript.ownTail]
            exact cover1
        · rw [ite_eq_right backing, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _
            (.sourceGuard "ds-math-sub-underflow") tail returndata resumedSuccess)

/-- **The model's acceptance gives the skim guards.**  Every skim the model accepts — whatever the
transcript — passes `SkimModelConditions` at the transcript's two balance answers (its first and
third words; the second is the first transfer). -/
theorem runTyped_skim_conditions {st : State} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {returndata : Bytes}
    (successful : (runTyped st ctx (.skim recipient) transcript).status = .success returndata) :
    SkimModelConditions st ctx transcript.firstWord transcript.ownTail.ownTail.firstWord := by
  let current : Checkpoint := { state := st, logs := [], updates := [] }
  change (drive (transcript.work + 2) (startTyped current ctx (.skim recipient)) transcript).status =
    .success returndata at successful
  by_cases paid : ctx.value ≠ 0
  · simp only [startTyped, startImmediate, ite_eq_left paid, Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _ .emptyRevert transcript returndata successful)
  by_cases unlocked : st.unlocked = 1
  swap
  · have enteredLocked : ¬(Frame.enter current ctx (.skim recipient)).current.state.unlocked = 1 :=
      unlocked
    have closed : (Frame.enter current ctx (.skim recipient)).lock =
        .error (.sourceGuard "UniswapV2: LOCKED") := by
      rw [Frame.lock, ite_eq_right enteredLocked]
    simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, closed,
      Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _
      (.sourceGuard "UniswapV2: LOCKED") transcript returndata successful)
  have unlockedCurrent : current.state.unlocked = 1 := unlocked
  by_cases staticContext : ctx.isStatic = true
  · simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, Frame.lock,
      Frame.enter, ite_eq_left unlockedCurrent, staticContext, ite_true, Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _ .staticWrite transcript returndata successful)
  let lockedFrame : Frame :=
    { Frame.enter current ctx (.skim recipient) with
      current := { current with state := { st with unlocked := 0 } } }
  let locals : SkimLocals := { recipient := recipient, token0 := st.token0, token1 := st.token1 }
  have enteredUnlocked : (Frame.enter current ctx (.skim recipient)).current.state.unlocked = 1 :=
    unlocked
  have enteredStatic : ¬(Frame.enter current ctx (.skim recipient)).context.isStatic = true :=
    staticContext
  have opened : (Frame.enter current ctx (.skim recipient)).lock = .ok lockedFrame := by
    rw [Frame.lock, ite_eq_left enteredUnlocked, ite_eq_right enteredStatic]
    rfl
  have stage : startTyped current ctx (.skim recipient) =
      lockedFrame.suspend .skimBalance0 locals.token0 (.balanceOf ctx.pair)
        (.skimBalance0 locals) := by
    simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, opened]
    rfl
  rw [stage] at successful
  simp only [Frame.suspend] at successful
  obtain ⟨cover0, cover1⟩ := drive_skimBalance0_cover (frame := lockedFrame) rfl rfl rfl successful
  have value : ctx.value = 0 := by
    by_contra h
    exact paid h
  have nonstatic : ctx.isStatic = false := by
    cases h : ctx.isStatic
    · rfl
    · exact absurd h staticContext
  exact ⟨value, nonstatic, unlocked, cover0, cover1⟩

end Blanc.Lift.UniswapV2Pair
