import Blanc.Lift.UniswapV2Pair.Properties

/-! Driver-level success facts for the source-model swap path. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

def SwapContextConditions (ctx : Context) : Prop :=
  ctx.value = 0 ∧ ctx.isStatic = false

def SwapModelConditions (st : State) (amount0Out amount1Out : B256)
    (recipient : Adr) (balance0 balance1 : B256) : Prop :=
  st.unlocked = 1 ∧
    (amount0Out > 0 ∨ amount1Out > 0) ∧
    amount0Out.toNat < st.reserve0.val ∧ amount1Out.toNat < st.reserve1.val ∧
    recipient ≠ st.token0 ∧ recipient ≠ st.token1 ∧
    balance0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 ∧
    let inputs := swapInputs balance0 balance1 amount0Out amount1Out
      st.reserve0.val st.reserve1.val
    (inputs.1 > 0 ∨ inputs.2 > 0) ∧
      swapCheck balance0 balance1 inputs.1 inputs.2 st.reserve0.val st.reserve1.val = .ok ()

def Transcript.HasDecodedWord (request : Request) (balance : B256) : Transcript → Prop
  | .done => False
  | .next result turns tail =>
      decodeExternal request result = .ok (.word balance) ∨
        Transcript.HasDecodedWord request balance turns ∨
          Transcript.HasDecodedWord request balance tail
  | .foreignLog _ _ _ tail => Transcript.HasDecodedWord request balance tail
  | .invoke _ _ _ _ turns tail =>
      Transcript.HasDecodedWord request balance turns ∨
        Transcript.HasDecodedWord request balance tail

theorem Transcript.hasDecodedWord_next_tail {request : Request} {balance : B256}
    {result : ExternalResult} {turns tail : Transcript}
    (found : Transcript.HasDecodedWord request balance tail) :
    Transcript.HasDecodedWord request balance (.next result turns tail) := by
  simp only [Transcript.HasDecodedWord]
  exact Or.inr (Or.inr found)

theorem driveTurns_context_pair {fuel : Nat} {frame : Frame} {request : Request}
    {turn : Nat} {turns : Transcript} :
    (driveTurns fuel frame request turn turns).frame.context.pair = frame.context.pair := by
  induction fuel generalizing frame turn turns with
  | zero => rfl
  | succ fuel ih =>
    cases turns with
    | done => rfl
    | next result nested tail => rfl
    | foreignLog emitter topics data tail =>
      cases static : externalStatic frame request with
      | false => simp only [driveTurns, static, Bool.false_eq_true, ite_false, ih]
      | true => simp only [driveTurns, static, ite_true]
    | invoke sender value isStatic entry nested tail =>
      cases child : drive fuel (startTyped frame.current
          (childContext frame request turn sender value isStatic) entry) nested with
      | mk status childFrame remaining childReturns =>
        cases status with
        | incomplete => simp only [driveTurns, child]
        | success returndata => simp only [driveTurns, child, ih]
        | failed failure => simp only [driveTurns, child, ih]

theorem Frame.settleExternal_context_pair {frame : Frame} {fuel : Nat}
    {request : Request} {result : ExternalResult} {turns : Transcript} :
    (frame.settleExternal fuel request result turns).context.pair = frame.context.pair := by
  rw [Frame.settleExternal]
  by_cases successful : result.success
  · simp only [successful, ite_true]
    exact driveTurns_context_pair
  · simp only [successful]
    exact driveTurns_context_pair

def SwapTranscriptAnswers (frame : Frame) (locals : SwapLocals) (transcript : Transcript)
    (balance0 balance1 : B256) : Prop :=
  Transcript.HasDecodedWord
      (requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair))
      balance0 transcript ∧
    Transcript.HasDecodedWord
      (requestFor .swapBalance1 locals.token1 (.balanceOf frame.context.pair))
      balance1 transcript

theorem SwapTranscriptAnswers.next_tail {frame : Frame} {locals : SwapLocals}
    {result : ExternalResult} {turns tail : Transcript} {balance0 balance1 : B256}
    (found : SwapTranscriptAnswers frame locals tail balance0 balance1) :
    SwapTranscriptAnswers frame locals (.next result turns tail) balance0 balance1 := by
  simp only [SwapTranscriptAnswers]
  exact ⟨Transcript.hasDecodedWord_next_tail found.1,
    Transcript.hasDecodedWord_next_tail found.2⟩

theorem Frame.finishUpdated_bounds {frame final : Frame} {balance0 balance1 : B256}
    {reserves : CachedReserves} {feeOn : Bool} {lastEvent : Option Event} {returndata output : Bytes}
    (accepted : frame.finishUpdated balance0 balance1 reserves feeOn lastEvent returndata =
      .finished final output) :
    balance0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 := by
  rw [Frame.finishUpdated] at accepted
  cases updated : frame.current.state.update frame.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val with
  | error failure =>
    simp only [updated, Frame.fail] at accepted
    cases accepted
  | ok result =>
    rcases result with ⟨post, event, update⟩
    simp only [updated] at accepted
    rw [State.update] at updated
    by_cases bound0 : balance0.toNat < 2 ^ 112
    · rw [dite_eq_left bound0] at updated
      by_cases bound1 : balance1.toNat < 2 ^ 112
      · exact ⟨bound0, bound1⟩
      · rw [dite_eq_right bound1] at updated
        cases updated
    · rw [dite_eq_right bound0] at updated
      cases updated

def SwapCheckWitness (locals : SwapLocals) (balance0 balance1 : B256) : Prop :=
  balance0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 ∧
    let inputs := swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
      locals.reserves.reserve0.val locals.reserves.reserve1.val
    (inputs.1 > 0 ∨ inputs.2 > 0) ∧
      swapCheck balance0 balance1 inputs.1 inputs.2
        locals.reserves.reserve0.val locals.reserves.reserve1.val = .ok ()

theorem drive_swapBalance1_reserves {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {balance0 : B256} {transcript : Transcript} {returndata : Bytes}
    (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.swapBalance1 locals balance0))
      transcript).status = .success returndata) :
    ∃ balance1, SwapCheckWitness locals balance0 balance1 ∧
      Transcript.HasDecodedWord request balance1 transcript ∧
      (drive fuel (.suspended frame request (.swapBalance1 locals balance0)) transcript).frame.current.state.reserve0.val =
        balance0.toNat ∧
      (drive fuel (.suspended frame request (.swapBalance1 locals balance0)) transcript).frame.current.state.reserve1.val =
        balance1.toNat := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have staticExternal : externalStatic frame request = true := by
      rw [externalStatic, kind]
      cases frame.context.isStatic <;> rfl
    have settled := Frame.settleExternal_static_frame frame fuel request result turns staticExternal
    rw [settled] at resumedSuccess frameEq
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
        let inputs := swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
          locals.reserves.reserve0.val locals.reserves.reserve1.val
        simp only [resumeSegment, decoded] at resumedSuccess frameEq
        cases checked : swapCheck balance0 balance1 inputs.1 inputs.2
            locals.reserves.reserve0.val locals.reserves.reserve1.val with
        | error failure =>
          dsimp only [inputs] at checked
          simp only [checked, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _ failure tail returndata resumedSuccess)
        | ok accepted =>
          cases accepted
          have positive : inputs.1 > 0 ∨ inputs.2 > 0 := by
            rw [swapCheck] at checked
            by_cases h : inputs.1 > 0 ∨ inputs.2 > 0
            · exact h
            · rw [ite_eq_right h] at checked
              cases checked
          dsimp only [inputs] at checked positive
          simp only [checked] at resumedSuccess frameEq
          have terminal := Frame.finishUpdated_terminal (frame.beginResume request)
            balance0 balance1 locals.reserves false
            (some (.swap (frame.beginResume request).context.sender
              (Nat.toB256 inputs.1) (Nat.toB256 inputs.2)
              locals.amount0Out locals.amount1Out locals.recipient)) []
          obtain ⟨final, finished, finalEq⟩ := drive_terminal_success terminal resumedSuccess
          have bounds := Frame.finishUpdated_bounds finished
          have fields := Frame.finishUpdated_supply_reserves finished
          have outputEq :
              (drive (fuel + 1) (.suspended frame request (.swapBalance1 locals balance0)) transcript).frame = final :=
            frameEq.trans finalEq
          refine ⟨balance1, ⟨bounds.1, bounds.2, positive, checked⟩, ?_, ?_, ?_⟩
          · rw [shape]
            exact Or.inl decoded
          · rw [outputEq]
            exact fields.2.1
          · rw [outputEq]
            exact fields.2.2

theorem drive_swapBalance0_reserves {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.swapBalance0 locals))
      transcript).status = .success returndata) :
    ∃ balance0 balance1, SwapCheckWitness locals balance0 balance1 ∧
      Transcript.HasDecodedWord request balance0 transcript ∧
      Transcript.HasDecodedWord
        (requestFor .swapBalance1 locals.token1 (.balanceOf frame.context.pair))
        balance1 transcript ∧
      (drive fuel (.suspended frame request (.swapBalance0 locals)) transcript).frame.current.state.reserve0.val =
        balance0.toNat ∧
      (drive fuel (.suspended frame request (.swapBalance0 locals)) transcript).frame.current.state.reserve1.val =
        balance1.toNat := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have staticExternal : externalStatic frame request = true := by
      rw [externalStatic, kind]
      cases frame.context.isStatic <;> rfl
    have settled := Frame.settleExternal_static_frame frame fuel request result turns staticExternal
    rw [settled] at resumedSuccess frameEq
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
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess frameEq
        rcases drive_swapBalance1_reserves (frame := frame.beginResume request)
          (request := requestFor .swapBalance1 locals.token1 (.balanceOf frame.context.pair))
          rfl resumedSuccess with ⟨balance1, witness, found1, res0, res1⟩
        refine ⟨balance0, balance1, witness, ?_, ?_, ?_, ?_⟩
        · rw [shape]
          exact Or.inl decoded
        · rw [shape]
          exact Transcript.hasDecodedWord_next_tail found1
        · rw [frameEq]
          exact res0
        · rw [frameEq]
          exact res1

theorem drive_swapCallback_reserves {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (.suspended frame request (.swapCallback locals))
      transcript).status = .success returndata) :
    ∃ balance0 balance1, SwapCheckWitness locals balance0 balance1 ∧
      SwapTranscriptAnswers frame locals transcript balance0 balance1 ∧
      (drive fuel (.suspended frame request (.swapCallback locals)) transcript).frame.current.state.reserve0.val =
        balance0.toNat ∧
      (drive fuel (.suspended frame request (.swapCallback locals)) transcript).frame.current.state.reserve1.val =
        balance1.toNat := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    cases decoded : decodeExternal request result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | address address =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess frameEq
        rcases drive_swapBalance0_reserves
          (frame := (frame.settleExternal fuel request result turns).beginResume request)
          (request := _) rfl resumedSuccess with
          ⟨balance0, balance1, witness, found0, found1, res0, res1⟩
        have pair :
            ((frame.settleExternal fuel request result turns).beginResume request).context.pair =
              frame.context.pair := by
          exact Frame.settleExternal_context_pair
        rw [pair] at found0 found1
        refine ⟨balance0, balance1, witness, ?_, ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · rw [shape]
            exact Transcript.hasDecodedWord_next_tail found0
          · rw [shape]
            exact Transcript.hasDecodedWord_next_tail found1
        · rw [frameEq]
          exact res0
        · rw [frameEq]
          exact res1

theorem Frame.afterSwapTransfer1_reserves {fuel : Nat} {frame : Frame}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (frame.afterSwapTransfer1 locals) transcript).status =
      .success returndata) :
    ∃ balance0 balance1, SwapCheckWitness locals balance0 balance1 ∧
      SwapTranscriptAnswers frame locals transcript balance0 balance1 ∧
      (drive fuel (frame.afterSwapTransfer1 locals) transcript).frame.current.state.reserve0.val =
        balance0.toNat ∧
      (drive fuel (frame.afterSwapTransfer1 locals) transcript).frame.current.state.reserve1.val =
        balance1.toNat := by
  by_cases data : locals.data.length > 0
  · simp only [Frame.afterSwapTransfer1, ite_eq_left data, Frame.suspend] at successful ⊢
    exact drive_swapCallback_reserves successful
  · simp only [Frame.afterSwapTransfer1, ite_eq_right data, Frame.suspend] at successful ⊢
    rcases drive_swapBalance0_reserves rfl successful with ⟨balance0, balance1, witness, found0, found1, res0, res1⟩
    exact ⟨balance0, balance1, witness, ⟨found0, found1⟩, res0, res1⟩

theorem drive_swapTransfer1_reserves {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (.suspended frame request (.swapTransfer1 locals))
      transcript).status = .success returndata) :
    ∃ balance0 balance1, SwapCheckWitness locals balance0 balance1 ∧
      SwapTranscriptAnswers frame locals transcript balance0 balance1 ∧
      (drive fuel (.suspended frame request (.swapTransfer1 locals)) transcript).frame.current.state.reserve0.val =
        balance0.toNat ∧
      (drive fuel (.suspended frame request (.swapTransfer1 locals)) transcript).frame.current.state.reserve1.val =
        balance1.toNat := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    cases decoded : decodeExternal request result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | address address =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded] at resumedSuccess frameEq
        rcases Frame.afterSwapTransfer1_reserves resumedSuccess with
          ⟨balance0, balance1, witness, found, res0, res1⟩
        have pair :
            ((frame.settleExternal fuel request result turns).beginResume request).context.pair =
              frame.context.pair := by
          exact Frame.settleExternal_context_pair
        simp only [SwapTranscriptAnswers] at found ⊢
        rw [pair] at found
        refine ⟨balance0, balance1, witness, ?_, ?_, ?_⟩
        · rw [shape]
          exact SwapTranscriptAnswers.next_tail found
        · rw [frameEq]
          exact res0
        · rw [frameEq]
          exact res1

theorem Frame.afterSwapTransfer0_reserves {fuel : Nat} {frame : Frame}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (frame.afterSwapTransfer0 locals) transcript).status =
      .success returndata) :
    ∃ balance0 balance1, SwapCheckWitness locals balance0 balance1 ∧
      SwapTranscriptAnswers frame locals transcript balance0 balance1 ∧
      (drive fuel (frame.afterSwapTransfer0 locals) transcript).frame.current.state.reserve0.val =
        balance0.toNat ∧
      (drive fuel (frame.afterSwapTransfer0 locals) transcript).frame.current.state.reserve1.val =
        balance1.toNat := by
  by_cases output1 : locals.amount1Out > 0
  · simp only [Frame.afterSwapTransfer0, ite_eq_left output1, Frame.suspend] at successful ⊢
    exact drive_swapTransfer1_reserves successful
  · simp only [Frame.afterSwapTransfer0, ite_eq_right output1] at successful ⊢
    exact Frame.afterSwapTransfer1_reserves successful

theorem drive_swapTransfer0_reserves {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (.suspended frame request (.swapTransfer0 locals))
      transcript).status = .success returndata) :
    ∃ balance0 balance1, SwapCheckWitness locals balance0 balance1 ∧
      SwapTranscriptAnswers frame locals transcript balance0 balance1 ∧
      (drive fuel (.suspended frame request (.swapTransfer0 locals)) transcript).frame.current.state.reserve0.val =
        balance0.toNat ∧
      (drive fuel (.suspended frame request (.swapTransfer0 locals)) transcript).frame.current.state.reserve1.val =
        balance1.toNat := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    cases decoded : decodeExternal request result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | address address =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded] at resumedSuccess frameEq
        rcases Frame.afterSwapTransfer0_reserves resumedSuccess with
          ⟨balance0, balance1, witness, found, res0, res1⟩
        have pair :
            ((frame.settleExternal fuel request result turns).beginResume request).context.pair =
              frame.context.pair := by
          exact Frame.settleExternal_context_pair
        simp only [SwapTranscriptAnswers] at found ⊢
        rw [pair] at found
        refine ⟨balance0, balance1, witness, ?_, ?_, ?_⟩
        · rw [shape]
          exact SwapTranscriptAnswers.next_tail found
        · rw [frameEq]
          exact res0
        · rw [frameEq]
          exact res1

theorem drive_startTyped_swap_reserves {fuel : Nat} {current : Checkpoint} {ctx : Context}
    {amount0Out amount1Out : B256} {recipient : Adr} {data : Bytes}
    {transcript : Transcript} {returndata : Bytes}
    (successful :
      (drive fuel (startTyped current ctx (.swap amount0Out amount1Out recipient data))
        transcript).status = .success returndata) :
    SwapContextConditions ctx ∧
      ∃ balance0 balance1,
        SwapModelConditions current.state amount0Out amount1Out recipient balance0 balance1 ∧
          SwapTranscriptAnswers
            (Frame.enter current ctx (.swap amount0Out amount1Out recipient data))
            { recipient := recipient, reserves := current.state.cachedReserves,
              token0 := current.state.token0, token1 := current.state.token1,
              amount0Out := amount0Out, amount1Out := amount1Out, data := data }
            transcript balance0 balance1 ∧
          (drive fuel (startTyped current ctx (.swap amount0Out amount1Out recipient data)) transcript).frame.current.state.reserve0.val =
            balance0.toNat ∧
          (drive fuel (startTyped current ctx (.swap amount0Out amount1Out recipient data)) transcript).frame.current.state.reserve1.val =
            balance1.toNat := by
  by_cases paid : ctx.value ≠ 0
  · simp only [startTyped, startImmediate, ite_eq_left paid, Frame.fail] at successful
    exact False.elim (drive_failed_not_success fuel _ .emptyRevert transcript returndata successful)
  · by_cases unlocked : current.state.unlocked = 1
    · by_cases staticContext : ctx.isStatic = true
      · simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, Frame.lock,
          Frame.enter, ite_eq_left unlocked, staticContext, ite_true, Frame.fail] at successful
        exact False.elim (drive_failed_not_success fuel _ .staticWrite transcript returndata successful)
      · let lockedFrame : Frame :=
          { Frame.enter current ctx (.swap amount0Out amount1Out recipient data) with
            current := { current with state := { current.state with unlocked := 0 } } }
        let locals : SwapLocals :=
          { recipient := recipient, reserves := current.state.cachedReserves,
            token0 := current.state.token0, token1 := current.state.token1,
            amount0Out := amount0Out, amount1Out := amount1Out, data := data }
        have enteredUnlocked :
            (Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).current.state.unlocked = 1 :=
          unlocked
        have enteredStatic :
            ¬(Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).context.isStatic = true :=
          staticContext
        have opened : (Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).lock =
            .ok lockedFrame := by
          rw [Frame.lock, ite_eq_left enteredUnlocked, ite_eq_right enteredStatic]
          rfl
        have stage : startTyped current ctx (.swap amount0Out amount1Out recipient data) =
            if amount0Out > 0 ∨ amount1Out > 0 then
              if amount0Out.toNat < current.state.reserve0.val ∧
                  amount1Out.toNat < current.state.reserve1.val then
                if recipient ≠ current.state.token0 ∧ recipient ≠ current.state.token1 then
                  if amount0Out > 0 then
                    lockedFrame.suspend .swapTransfer0 locals.token0 (.transfer recipient amount0Out)
                      (.swapTransfer0 locals)
                  else lockedFrame.afterSwapTransfer0 locals
                else lockedFrame.fail (.sourceGuard "UniswapV2: INVALID_TO")
              else lockedFrame.fail (.sourceGuard "UniswapV2: INSUFFICIENT_LIQUIDITY")
            else lockedFrame.fail (.sourceGuard "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT") := by
          simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, opened]
          rfl
        rw [stage] at successful ⊢
        by_cases positiveOutput : amount0Out > 0 ∨ amount1Out > 0
        · rw [ite_eq_left positiveOutput] at successful ⊢
          by_cases liquidity : amount0Out.toNat < current.state.reserve0.val ∧
              amount1Out.toNat < current.state.reserve1.val
          · rw [ite_eq_left liquidity] at successful ⊢
            by_cases validRecipient : recipient ≠ current.state.token0 ∧
                recipient ≠ current.state.token1
            · rw [ite_eq_left validRecipient] at successful ⊢
              by_cases payout0 : amount0Out > 0
              · rw [ite_eq_left payout0, Frame.suspend] at successful ⊢
                have witness := drive_swapTransfer0_reserves (frame := lockedFrame)
                  (request := _) successful
                rcases witness with ⟨balance0, balance1, witness, found, res0, res1⟩
                rcases witness with ⟨bound0, bound1, positiveInput, checked⟩
                refine ⟨?_, ⟨balance0, balance1, ?_, ?_, res0, res1⟩⟩
                · exact ⟨not_ne_iff.mp paid, by
                    cases h : ctx.isStatic with
                    | false => rfl
                    | true => exact False.elim (staticContext h)⟩
                · refine ⟨unlocked, positiveOutput, liquidity.1, liquidity.2, validRecipient.1,
                    validRecipient.2, bound0, bound1, ?_⟩
                  · change
                      ((swapInputs balance0 balance1 amount0Out amount1Out
                          current.state.reserve0.val current.state.reserve1.val).1 > 0 ∨
                        (swapInputs balance0 balance1 amount0Out amount1Out
                          current.state.reserve0.val current.state.reserve1.val).2 > 0) ∧
                        swapCheck balance0 balance1
                          (swapInputs balance0 balance1 amount0Out amount1Out
                            current.state.reserve0.val current.state.reserve1.val).1
                          (swapInputs balance0 balance1 amount0Out amount1Out
                            current.state.reserve0.val current.state.reserve1.val).2
                          current.state.reserve0.val current.state.reserve1.val = .ok ()
                    simpa only [locals, State.cachedReserves] using
                      And.intro positiveInput checked
                · simpa only [SwapTranscriptAnswers, lockedFrame, Frame.enter] using found
              · rw [ite_eq_right payout0] at successful ⊢
                have witness := Frame.afterSwapTransfer0_reserves successful
                rcases witness with ⟨balance0, balance1, witness, found, res0, res1⟩
                rcases witness with ⟨bound0, bound1, positiveInput, checked⟩
                refine ⟨?_, ⟨balance0, balance1, ?_, ?_, res0, res1⟩⟩
                · exact ⟨not_ne_iff.mp paid, by
                    cases h : ctx.isStatic with
                    | false => rfl
                    | true => exact False.elim (staticContext h)⟩
                · refine ⟨unlocked, positiveOutput, liquidity.1, liquidity.2, validRecipient.1,
                    validRecipient.2, bound0, bound1, ?_⟩
                  · change
                      ((swapInputs balance0 balance1 amount0Out amount1Out
                          current.state.reserve0.val current.state.reserve1.val).1 > 0 ∨
                        (swapInputs balance0 balance1 amount0Out amount1Out
                          current.state.reserve0.val current.state.reserve1.val).2 > 0) ∧
                        swapCheck balance0 balance1
                          (swapInputs balance0 balance1 amount0Out amount1Out
                            current.state.reserve0.val current.state.reserve1.val).1
                          (swapInputs balance0 balance1 amount0Out amount1Out
                            current.state.reserve0.val current.state.reserve1.val).2
                          current.state.reserve0.val current.state.reserve1.val = .ok ()
                    simpa only [locals, State.cachedReserves] using
                      And.intro positiveInput checked
                · simpa only [SwapTranscriptAnswers, lockedFrame, Frame.enter] using found
            · rw [ite_eq_right validRecipient] at successful
              exact False.elim (drive_failed_not_success fuel _
                (.sourceGuard "UniswapV2: INVALID_TO") transcript returndata successful)
          · rw [ite_eq_right liquidity] at successful
            exact False.elim (drive_failed_not_success fuel _
              (.sourceGuard "UniswapV2: INSUFFICIENT_LIQUIDITY") transcript returndata successful)
        · rw [ite_eq_right positiveOutput] at successful
          exact False.elim (drive_failed_not_success fuel _
            (.sourceGuard "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT") transcript returndata successful)
    · have enteredLocked :
          ¬(Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).current.state.unlocked = 1 :=
        unlocked
      have closed : (Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).lock =
          .error (.sourceGuard "UniswapV2: LOCKED") := by
        rw [Frame.lock, ite_eq_right enteredLocked]
      simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, closed, Frame.fail] at successful
      exact False.elim (drive_failed_not_success fuel _
        (.sourceGuard "UniswapV2: LOCKED") transcript returndata successful)

theorem runTyped_swap_success_reserves {st : State} {ctx : Context}
    {amount0Out amount1Out : B256} {recipient : Adr} {data : Bytes}
    {transcript : Transcript} {returndata : Bytes}
    (successful :
      (runTyped st ctx (.swap amount0Out amount1Out recipient data) transcript).status =
        .success returndata) :
    SwapContextConditions ctx ∧
      ∃ balance0 balance1,
        SwapModelConditions st amount0Out amount1Out recipient balance0 balance1 ∧
          SwapTranscriptAnswers
            (Frame.enter { state := st, logs := [], updates := [] }
              ctx (.swap amount0Out amount1Out recipient data))
            { recipient := recipient, reserves := st.cachedReserves,
              token0 := st.token0, token1 := st.token1,
              amount0Out := amount0Out, amount1Out := amount1Out, data := data }
            transcript balance0 balance1 ∧
          (runTyped st ctx (.swap amount0Out amount1Out recipient data) transcript).frame.current.state.reserve0.val =
            balance0.toNat ∧
          (runTyped st ctx (.swap amount0Out amount1Out recipient data) transcript).frame.current.state.reserve1.val =
            balance1.toNat := by
  exact drive_startTyped_swap_reserves
    (current := { state := st, logs := [], updates := [] })
    (ctx := ctx) (amount0Out := amount0Out) (amount1Out := amount1Out)
    (recipient := recipient) (data := data) (fuel := transcript.work + 2)
    (transcript := transcript) (returndata := returndata) successful

def swapOk : ExternalResult :=
  { success := true, returndata := [], codeExists := true, recoveryOutput := 0 }

def swapAnswer (balance : B256) : ExternalResult :=
  { success := true, returndata := encodeWords [balance], codeExists := true, recoveryOutput := 0 }

def swapCanonicalPostTransfers (balance0 balance1 : B256) (data : Bytes) : Transcript :=
  if data.length > 0 then
    .next swapOk .done
      (.next (swapAnswer balance0) .done (.next (swapAnswer balance1) .done .done))
  else
    .next (swapAnswer balance0) .done (.next (swapAnswer balance1) .done .done)

def swapCanonicalTail (amount1Out : B256) (balance0 balance1 : B256) (data : Bytes) : Transcript :=
  if amount1Out > 0 then
    .next swapOk .done (swapCanonicalPostTransfers balance0 balance1 data)
  else swapCanonicalPostTransfers balance0 balance1 data

def swapCanonicalTranscript (amount0Out amount1Out : B256) (balance0 balance1 : B256)
    (data : Bytes) : Transcript :=
  if amount0Out > 0 then
    .next swapOk .done (swapCanonicalTail amount1Out balance0 balance1 data)
  else if amount1Out > 0 then
    .next swapOk .done (swapCanonicalPostTransfers balance0 balance1 data)
  else swapCanonicalPostTransfers balance0 balance1 data

theorem decodeExternal_swapOk {site : CallSite} {target recipient : Adr} {value : B256} :
    decodeExternal (requestFor site target (.transfer recipient value)) swapOk = .ok .unit := by
  simp only [decodeExternal, requestFor, swapOk, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ite_true, ite_false, List.length_nil]

theorem decodeExternal_swapCallbackOk {site : CallSite} {target sender : Adr}
    {amount0Out amount1Out : B256} {data : Bytes} :
    decodeExternal (requestFor site target (.callback sender amount0Out amount1Out data)) swapOk =
      .ok .unit := by
  simp only [decodeExternal, requestFor, swapOk, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ite_true, ite_false]

theorem decodeExternal_swapAnswer {site : CallSite} {target owner : Adr} {balance : B256} :
    decodeExternal (requestFor site target (.balanceOf owner)) (swapAnswer balance) =
      .ok (.word balance) := by
  have word : Bytes.toB256 (List.take 32 balance.toBytes) = balance := by
    rw [List.take_of_length_le (show balance.toBytes.length ≤ 32 from
      Nat.le_of_eq (B256.length_toBytes balance))]
    exact B256.toB256_toBytes balance
  simp only [decodeExternal, requestFor, swapAnswer, encodeWords, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true,
    ite_true, ite_false, B256.length_toBytes, word, Nat.le_refl]

theorem State.update_ok_of_bounds {st : State} {ctx : Context}
    {balance0 balance1 : B256} {oldReserve0 oldReserve1 : Nat}
    (bound0 : balance0.toNat < 2 ^ 112) (bound1 : balance1.toNat < 2 ^ 112) :
    ∃ post event update,
      st.update ctx balance0 balance1 oldReserve0 oldReserve1 = .ok (post, event, update) := by
  unfold State.update
  rw [dite_eq_left bound0, dite_eq_left bound1]
  exact ⟨_, _, _, rfl⟩

theorem drive_swapFinish_success {frame : Frame} {balance0 balance1 : B256}
    {reserves : CachedReserves} {event : Event}
    (bound0 : balance0.toNat < 2 ^ 112) (bound1 : balance1.toNat < 2 ^ 112) :
    (drive 1
      (frame.finishUpdated balance0 balance1 reserves false (some event) []) .done).status =
        .success [] := by
  obtain ⟨_, _, _, updateOk⟩ :=
    State.update_ok_of_bounds bound0 bound1
  rw [Frame.finishUpdated, updateOk]
  simp only [Frame.withUpdate, Frame.finishLocked, Frame.finish, drive]

theorem drive_swapBalance1_canonical {frame : Frame}
    {locals : SwapLocals} {balance0 balance1 : B256}
    (witness : SwapCheckWitness locals balance0 balance1) :
    (drive 2
      (.suspended frame
        (requestFor .swapBalance1 locals.token1 (.balanceOf frame.context.pair))
        (.swapBalance1 locals balance0))
      (.next (swapAnswer balance1) .done .done)).status = .success [] := by
  rcases witness with ⟨bound0, bound1, _positiveInput, checked⟩
  have resumed :
      resumeSegment frame
          (requestFor .swapBalance1 locals.token1 (.balanceOf frame.context.pair))
          (.swapBalance1 locals balance0) (swapAnswer balance1) =
        (frame.beginResume
          (requestFor .swapBalance1 locals.token1 (.balanceOf frame.context.pair))).finishUpdated
          balance0 balance1 locals.reserves false
          (some (.swap frame.context.sender
            (Nat.toB256 (swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
              locals.reserves.reserve0.val locals.reserves.reserve1.val).1)
            (Nat.toB256 (swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
              locals.reserves.reserve0.val locals.reserves.reserve1.val).2)
            locals.amount0Out locals.amount1Out locals.recipient)) [] := by
    rw [resumeSegment, decodeExternal_swapAnswer]
    simp only [checked]
    simp only [Frame.beginResume]
  have guardFalse :
      ((requestFor .swapBalance1 locals.token1 (.balanceOf frame.context.pair)).requiresCode &&
        !(swapAnswer balance1).codeExists) = false := by
    rfl
  have successTrue : (swapAnswer balance1).success = true := by
    rfl
  rw [drive]
  simp only [driveTurns, eq_self, guardFalse, successTrue, Bool.false_eq_true,
    ite_false, ite_true]
  rw [resumed]
  rw [drive_swapFinish_success bound0 bound1]

theorem drive_swapBalance0_canonical {frame : Frame} {locals : SwapLocals}
    {balance0 balance1 : B256}
    (witness : SwapCheckWitness locals balance0 balance1) :
    (drive 3
      (.suspended frame
        (requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair))
        (.swapBalance0 locals))
      (.next (swapAnswer balance0) .done
        (.next (swapAnswer balance1) .done .done))).status = .success [] := by
  have resumed :
      resumeSegment frame
          (requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair))
          (.swapBalance0 locals) (swapAnswer balance0) =
        (frame.beginResume
          (requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair))).suspend
            .swapBalance1 locals.token1 (.balanceOf frame.context.pair)
            (.swapBalance1 locals balance0) := by
    rw [resumeSegment, decodeExternal_swapAnswer]
    rfl
  have guardFalse :
      ((requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair)).requiresCode &&
        !(swapAnswer balance0).codeExists) = false := by
    rfl
  have successTrue : (swapAnswer balance0).success = true := by
    rfl
  rw [drive]
  simp only [driveTurns, eq_self, guardFalse, successTrue, Bool.false_eq_true,
    ite_false, ite_true]
  rw [resumed]
  exact drive_swapBalance1_canonical
    (frame := frame.beginResume
      (requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair))) witness

theorem drive_swapBalance0_canonical4 {frame : Frame} {locals : SwapLocals}
    {balance0 balance1 : B256}
    (witness : SwapCheckWitness locals balance0 balance1) :
    (drive 4
      (.suspended frame
        (requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair))
        (.swapBalance0 locals))
      (.next (swapAnswer balance0) .done
        (.next (swapAnswer balance1) .done .done))).status = .success [] := by
  have resumed :
      resumeSegment frame
          (requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair))
          (.swapBalance0 locals) (swapAnswer balance0) =
        (frame.beginResume
          (requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair))).suspend
            .swapBalance1 locals.token1 (.balanceOf frame.context.pair)
            (.swapBalance1 locals balance0) := by
    rw [resumeSegment, decodeExternal_swapAnswer]
    rfl
  have guardFalse :
      ((requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair)).requiresCode &&
        !(swapAnswer balance0).codeExists) = false := by
    rfl
  have successTrue : (swapAnswer balance0).success = true := by
    rfl
  rw [drive]
  simp only [driveTurns, eq_self, guardFalse, successTrue, Bool.false_eq_true,
    ite_false, ite_true]
  rw [resumed]
  exact drive_swapBalance1_canonical
    (frame := frame.beginResume
      (requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair))) witness

theorem drive_swapCallback_canonical {frame : Frame} {locals : SwapLocals}
    {balance0 balance1 : B256} (witness : SwapCheckWitness locals balance0 balance1) :
    (drive 4
      (.suspended frame
        (requestFor .swapCallback locals.recipient
          (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data))
        (.swapCallback locals))
      (.next swapOk .done
        (.next (swapAnswer balance0) .done
          (.next (swapAnswer balance1) .done .done)))).status = .success [] := by
  have resumed :
      resumeSegment frame
          (requestFor .swapCallback locals.recipient
            (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data))
          (.swapCallback locals) swapOk =
        (frame.beginResume
          (requestFor .swapCallback locals.recipient
            (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data))).suspend
          .swapBalance0 locals.token0 (.balanceOf frame.context.pair) (.swapBalance0 locals) := by
    rw [resumeSegment, decodeExternal_swapCallbackOk]
    rfl
  have guardFalse :
      ((requestFor .swapCallback locals.recipient
        (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data)).requiresCode &&
        !swapOk.codeExists) = false := by
    rfl
  have successTrue : swapOk.success = true := by
    rfl
  rw [drive]
  simp only [driveTurns, eq_self, guardFalse, successTrue, Bool.false_eq_true,
    ite_false, ite_true]
  rw [resumed]
  exact drive_swapBalance0_canonical
    (frame := frame.beginResume
      (requestFor .swapCallback locals.recipient
        (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data))) witness

theorem drive_afterSwapTransfer1_noCallback {frame : Frame} {locals : SwapLocals}
    {balance0 balance1 : B256} (dataEmpty : locals.data.length = 0)
    (witness : SwapCheckWitness locals balance0 balance1) :
    (drive 4 (frame.afterSwapTransfer1 locals)
      (.next (swapAnswer balance0) .done
        (.next (swapAnswer balance1) .done .done))).status = .success [] := by
  rw [Frame.afterSwapTransfer1, ite_eq_right (by
    intro nonempty
    exact (Nat.ne_of_gt nonempty) dataEmpty)]
  exact drive_swapBalance0_canonical4 witness

theorem drive_afterSwapTransfer1_callback {frame : Frame} {locals : SwapLocals}
    {balance0 balance1 : B256} (dataNonempty : locals.data.length > 0)
    (witness : SwapCheckWitness locals balance0 balance1) :
    (drive 5 (frame.afterSwapTransfer1 locals)
      (.next swapOk .done
        (.next (swapAnswer balance0) .done
          (.next (swapAnswer balance1) .done .done)))).status = .success [] := by
  rw [Frame.afterSwapTransfer1, ite_eq_left dataNonempty]
  exact drive_swapCallback_canonical witness

theorem drive_swapTransfer1_noCallback {frame : Frame} {locals : SwapLocals}
    {balance0 balance1 : B256} (dataEmpty : locals.data.length = 0)
    (witness : SwapCheckWitness locals balance0 balance1) :
    (drive 5
      (.suspended frame
        (requestFor .swapTransfer1 locals.token1
          (.transfer locals.recipient locals.amount1Out))
        (.swapTransfer1 locals))
      (.next swapOk .done
        (.next (swapAnswer balance0) .done
          (.next (swapAnswer balance1) .done .done)))).status = .success [] := by
  have resumed :
      resumeSegment frame
          (requestFor .swapTransfer1 locals.token1
            (.transfer locals.recipient locals.amount1Out))
          (.swapTransfer1 locals) swapOk =
        (frame.beginResume
          (requestFor .swapTransfer1 locals.token1
            (.transfer locals.recipient locals.amount1Out))).afterSwapTransfer1 locals := by
    rw [resumeSegment, decodeExternal_swapOk]
  have guardFalse :
      ((requestFor .swapTransfer1 locals.token1
        (.transfer locals.recipient locals.amount1Out)).requiresCode &&
        !swapOk.codeExists) = false := by
    rfl
  have successTrue : swapOk.success = true := by
    rfl
  rw [drive]
  simp only [driveTurns, eq_self, guardFalse, successTrue, Bool.false_eq_true,
    ite_false, ite_true]
  rw [resumed]
  exact drive_afterSwapTransfer1_noCallback
    (frame := frame.beginResume
      (requestFor .swapTransfer1 locals.token1
        (.transfer locals.recipient locals.amount1Out))) dataEmpty witness

theorem drive_swapTransfer1_callback {frame : Frame} {locals : SwapLocals}
    {balance0 balance1 : B256} (dataNonempty : locals.data.length > 0)
    (witness : SwapCheckWitness locals balance0 balance1) :
    (drive 6
      (.suspended frame
        (requestFor .swapTransfer1 locals.token1
          (.transfer locals.recipient locals.amount1Out))
        (.swapTransfer1 locals))
      (.next swapOk .done
        (.next swapOk .done
          (.next (swapAnswer balance0) .done
            (.next (swapAnswer balance1) .done .done))))).status = .success [] := by
  have resumed :
      resumeSegment frame
          (requestFor .swapTransfer1 locals.token1
            (.transfer locals.recipient locals.amount1Out))
          (.swapTransfer1 locals) swapOk =
        (frame.beginResume
          (requestFor .swapTransfer1 locals.token1
            (.transfer locals.recipient locals.amount1Out))).afterSwapTransfer1 locals := by
    rw [resumeSegment, decodeExternal_swapOk]
  have guardFalse :
      ((requestFor .swapTransfer1 locals.token1
        (.transfer locals.recipient locals.amount1Out)).requiresCode &&
        !swapOk.codeExists) = false := by
    rfl
  have successTrue : swapOk.success = true := by
    rfl
  rw [drive]
  simp only [driveTurns, eq_self, guardFalse, successTrue, Bool.false_eq_true,
    ite_false, ite_true]
  rw [resumed]
  exact drive_afterSwapTransfer1_callback
    (frame := frame.beginResume
      (requestFor .swapTransfer1 locals.token1
        (.transfer locals.recipient locals.amount1Out))) dataNonempty witness

theorem drive_swapTransfer0_noAmount1_noCallback {frame : Frame} {locals : SwapLocals}
    {balance0 balance1 : B256} (amount1Empty : ¬locals.amount1Out > 0)
    (dataEmpty : locals.data.length = 0)
    (witness : SwapCheckWitness locals balance0 balance1) :
    (drive 5
      (.suspended frame
        (requestFor .swapTransfer0 locals.token0
          (.transfer locals.recipient locals.amount0Out))
        (.swapTransfer0 locals))
      (.next swapOk .done
        (.next (swapAnswer balance0) .done
          (.next (swapAnswer balance1) .done .done)))).status = .success [] := by
  have resumed :
      resumeSegment frame
          (requestFor .swapTransfer0 locals.token0
            (.transfer locals.recipient locals.amount0Out))
          (.swapTransfer0 locals) swapOk =
        (frame.beginResume
          (requestFor .swapTransfer0 locals.token0
            (.transfer locals.recipient locals.amount0Out))).afterSwapTransfer0 locals := by
    rw [resumeSegment, decodeExternal_swapOk]
  have guardFalse :
      ((requestFor .swapTransfer0 locals.token0
        (.transfer locals.recipient locals.amount0Out)).requiresCode &&
        !swapOk.codeExists) = false := by
    rfl
  have successTrue : swapOk.success = true := by
    rfl
  rw [drive]
  simp only [driveTurns, eq_self, guardFalse, successTrue, Bool.false_eq_true,
    ite_false, ite_true]
  rw [resumed, Frame.afterSwapTransfer0, ite_eq_right amount1Empty]
  exact drive_afterSwapTransfer1_noCallback
    (frame := frame.beginResume
      (requestFor .swapTransfer0 locals.token0
        (.transfer locals.recipient locals.amount0Out))) dataEmpty witness

theorem drive_swapTransfer0_noAmount1_callback {frame : Frame} {locals : SwapLocals}
    {balance0 balance1 : B256} (amount1Empty : ¬locals.amount1Out > 0)
    (dataNonempty : locals.data.length > 0)
    (witness : SwapCheckWitness locals balance0 balance1) :
    (drive 6
      (.suspended frame
        (requestFor .swapTransfer0 locals.token0
          (.transfer locals.recipient locals.amount0Out))
        (.swapTransfer0 locals))
      (.next swapOk .done
        (.next swapOk .done
          (.next (swapAnswer balance0) .done
            (.next (swapAnswer balance1) .done .done))))).status = .success [] := by
  have resumed :
      resumeSegment frame
          (requestFor .swapTransfer0 locals.token0
            (.transfer locals.recipient locals.amount0Out))
          (.swapTransfer0 locals) swapOk =
        (frame.beginResume
          (requestFor .swapTransfer0 locals.token0
            (.transfer locals.recipient locals.amount0Out))).afterSwapTransfer0 locals := by
    rw [resumeSegment, decodeExternal_swapOk]
  have guardFalse :
      ((requestFor .swapTransfer0 locals.token0
        (.transfer locals.recipient locals.amount0Out)).requiresCode &&
        !swapOk.codeExists) = false := by
    rfl
  have successTrue : swapOk.success = true := by
    rfl
  rw [drive]
  simp only [driveTurns, eq_self, guardFalse, successTrue, Bool.false_eq_true,
    ite_false, ite_true]
  rw [resumed, Frame.afterSwapTransfer0, ite_eq_right amount1Empty]
  exact drive_afterSwapTransfer1_callback
    (frame := frame.beginResume
      (requestFor .swapTransfer0 locals.token0
        (.transfer locals.recipient locals.amount0Out))) dataNonempty witness

theorem drive_swapTransfer0_amount1_noCallback {frame : Frame} {locals : SwapLocals}
    {balance0 balance1 : B256} (amount1Positive : locals.amount1Out > 0)
    (dataEmpty : locals.data.length = 0)
    (witness : SwapCheckWitness locals balance0 balance1) :
    (drive 6
      (.suspended frame
        (requestFor .swapTransfer0 locals.token0
          (.transfer locals.recipient locals.amount0Out))
        (.swapTransfer0 locals))
      (.next swapOk .done
        (.next swapOk .done
          (.next (swapAnswer balance0) .done
            (.next (swapAnswer balance1) .done .done))))).status = .success [] := by
  have resumed :
      resumeSegment frame
          (requestFor .swapTransfer0 locals.token0
            (.transfer locals.recipient locals.amount0Out))
          (.swapTransfer0 locals) swapOk =
        (frame.beginResume
          (requestFor .swapTransfer0 locals.token0
            (.transfer locals.recipient locals.amount0Out))).afterSwapTransfer0 locals := by
    rw [resumeSegment, decodeExternal_swapOk]
  have guardFalse :
      ((requestFor .swapTransfer0 locals.token0
        (.transfer locals.recipient locals.amount0Out)).requiresCode &&
        !swapOk.codeExists) = false := by
    rfl
  have successTrue : swapOk.success = true := by
    rfl
  rw [drive]
  simp only [driveTurns, eq_self, guardFalse, successTrue, Bool.false_eq_true,
    ite_false, ite_true]
  rw [resumed, Frame.afterSwapTransfer0, ite_eq_left amount1Positive]
  exact drive_swapTransfer1_noCallback
    (frame := frame.beginResume
      (requestFor .swapTransfer0 locals.token0
        (.transfer locals.recipient locals.amount0Out))) dataEmpty witness

theorem drive_swapTransfer0_amount1_callback {frame : Frame} {locals : SwapLocals}
    {balance0 balance1 : B256} (amount1Positive : locals.amount1Out > 0)
    (dataNonempty : locals.data.length > 0)
    (witness : SwapCheckWitness locals balance0 balance1) :
    (drive 7
      (.suspended frame
        (requestFor .swapTransfer0 locals.token0
          (.transfer locals.recipient locals.amount0Out))
        (.swapTransfer0 locals))
      (.next swapOk .done
        (.next swapOk .done
          (.next swapOk .done
            (.next (swapAnswer balance0) .done
              (.next (swapAnswer balance1) .done .done)))))).status = .success [] := by
  have resumed :
      resumeSegment frame
          (requestFor .swapTransfer0 locals.token0
            (.transfer locals.recipient locals.amount0Out))
          (.swapTransfer0 locals) swapOk =
        (frame.beginResume
          (requestFor .swapTransfer0 locals.token0
            (.transfer locals.recipient locals.amount0Out))).afterSwapTransfer0 locals := by
    rw [resumeSegment, decodeExternal_swapOk]
  have guardFalse :
      ((requestFor .swapTransfer0 locals.token0
        (.transfer locals.recipient locals.amount0Out)).requiresCode &&
        !swapOk.codeExists) = false := by
    rfl
  have successTrue : swapOk.success = true := by
    rfl
  rw [drive]
  simp only [driveTurns, eq_self, guardFalse, successTrue, Bool.false_eq_true,
    ite_false, ite_true]
  rw [resumed, Frame.afterSwapTransfer0, ite_eq_left amount1Positive]
  exact drive_swapTransfer1_callback
    (frame := frame.beginResume
      (requestFor .swapTransfer0 locals.token0
        (.transfer locals.recipient locals.amount0Out))) dataNonempty witness

theorem runTyped_swap_canonical_success {st : State} {ctx : Context}
    {amount0Out amount1Out : B256} {recipient : Adr} {data : Bytes}
    {balance0 balance1 : B256}
    (context : SwapContextConditions ctx)
    (conditions : SwapModelConditions st amount0Out amount1Out recipient balance0 balance1) :
    (runTyped st ctx (.swap amount0Out amount1Out recipient data)
      (swapCanonicalTranscript amount0Out amount1Out balance0 balance1 data)).status = .success [] := by
  rcases context with ⟨valueZero, staticFalse⟩
  rcases conditions with ⟨unlocked, positiveOutput, liquidity0, liquidity1,
    validRecipient0, validRecipient1, bound0, bound1, positiveInput, checked⟩
  have paid : ¬ctx.value ≠ 0 := by
    intro nonzero
    exact nonzero valueZero
  have staticContext : ¬ctx.isStatic = true := by
    intro staticTrue
    rw [staticFalse] at staticTrue
    cases staticTrue
  let current : Checkpoint := { state := st, logs := [], updates := [] }
  let lockedFrame : Frame :=
    { Frame.enter current ctx (.swap amount0Out amount1Out recipient data) with
      current := { current with state := { st with unlocked := 0 } } }
  let locals : SwapLocals :=
    { recipient := recipient, reserves := st.cachedReserves, token0 := st.token0,
      token1 := st.token1, amount0Out := amount0Out, amount1Out := amount1Out, data := data }
  have enteredUnlocked :
      (Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).current.state.unlocked = 1 :=
    unlocked
  have enteredStatic :
      ¬(Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).context.isStatic = true :=
    staticContext
  have opened : (Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).lock =
      .ok lockedFrame := by
    rw [Frame.lock, ite_eq_left enteredUnlocked, ite_eq_right enteredStatic]
    rfl
  have stage : startTyped current ctx (.swap amount0Out amount1Out recipient data) =
      if amount0Out > 0 ∨ amount1Out > 0 then
        if amount0Out.toNat < st.reserve0.val ∧ amount1Out.toNat < st.reserve1.val then
          if recipient ≠ st.token0 ∧ recipient ≠ st.token1 then
            if amount0Out > 0 then
              lockedFrame.suspend .swapTransfer0 locals.token0 (.transfer recipient amount0Out)
                (.swapTransfer0 locals)
            else lockedFrame.afterSwapTransfer0 locals
          else lockedFrame.fail (.sourceGuard "UniswapV2: INVALID_TO")
        else lockedFrame.fail (.sourceGuard "UniswapV2: INSUFFICIENT_LIQUIDITY")
      else lockedFrame.fail (.sourceGuard "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT") := by
    simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, opened]
    rfl
  have witness : SwapCheckWitness locals balance0 balance1 := by
    change balance0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 ∧
      (let inputs := swapInputs balance0 balance1 amount0Out amount1Out st.reserve0.val st.reserve1.val
       inputs.1 > 0 ∨ inputs.2 > 0) ∧
      swapCheck balance0 balance1
        (swapInputs balance0 balance1 amount0Out amount1Out st.reserve0.val st.reserve1.val).1
        (swapInputs balance0 balance1 amount0Out amount1Out st.reserve0.val st.reserve1.val).2
        st.reserve0.val st.reserve1.val = .ok ()
    simpa only [locals, State.cachedReserves] using
      ⟨bound0, bound1, positiveInput, checked⟩
  by_cases payout0 : amount0Out > 0
  · by_cases payout1 : amount1Out > 0
    · by_cases dataNonempty : data.length > 0
      · rw [runTyped, stage, ite_eq_left positiveOutput, ite_eq_left ⟨liquidity0, liquidity1⟩,
          ite_eq_left ⟨validRecipient0, validRecipient1⟩, ite_eq_left payout0,
          swapCanonicalTranscript, ite_eq_left payout0, swapCanonicalTail,
          ite_eq_left payout1, swapCanonicalPostTransfers, ite_eq_left dataNonempty]
        exact drive_swapTransfer0_amount1_callback payout1 dataNonempty witness
      · rw [runTyped, stage, ite_eq_left positiveOutput, ite_eq_left ⟨liquidity0, liquidity1⟩,
          ite_eq_left ⟨validRecipient0, validRecipient1⟩, ite_eq_left payout0,
          swapCanonicalTranscript, ite_eq_left payout0, swapCanonicalTail,
          ite_eq_left payout1, swapCanonicalPostTransfers, ite_eq_right dataNonempty]
        exact drive_swapTransfer0_amount1_noCallback payout1
          (Nat.eq_zero_of_not_pos dataNonempty) witness
    · by_cases dataNonempty : data.length > 0
      · rw [runTyped, stage, ite_eq_left positiveOutput, ite_eq_left ⟨liquidity0, liquidity1⟩,
          ite_eq_left ⟨validRecipient0, validRecipient1⟩, ite_eq_left payout0,
          swapCanonicalTranscript, ite_eq_left payout0, swapCanonicalTail,
          ite_eq_right payout1, swapCanonicalPostTransfers, ite_eq_left dataNonempty]
        exact drive_swapTransfer0_noAmount1_callback payout1 dataNonempty witness
      · rw [runTyped, stage, ite_eq_left positiveOutput, ite_eq_left ⟨liquidity0, liquidity1⟩,
          ite_eq_left ⟨validRecipient0, validRecipient1⟩, ite_eq_left payout0,
          swapCanonicalTranscript, ite_eq_left payout0, swapCanonicalTail,
          ite_eq_right payout1, swapCanonicalPostTransfers, ite_eq_right dataNonempty]
        exact drive_swapTransfer0_noAmount1_noCallback payout1
          (Nat.eq_zero_of_not_pos dataNonempty) witness
  · by_cases payout1 : amount1Out > 0
    · by_cases dataNonempty : data.length > 0
      · rw [runTyped, stage, ite_eq_left positiveOutput, ite_eq_left ⟨liquidity0, liquidity1⟩,
          ite_eq_left ⟨validRecipient0, validRecipient1⟩, ite_eq_right payout0,
          Frame.afterSwapTransfer0, ite_eq_left payout1,
          swapCanonicalTranscript, ite_eq_right payout0, ite_eq_left payout1,
          swapCanonicalPostTransfers, ite_eq_left dataNonempty]
        exact drive_swapTransfer1_callback dataNonempty witness
      · rw [runTyped, stage, ite_eq_left positiveOutput, ite_eq_left ⟨liquidity0, liquidity1⟩,
          ite_eq_left ⟨validRecipient0, validRecipient1⟩, ite_eq_right payout0,
          Frame.afterSwapTransfer0, ite_eq_left payout1,
          swapCanonicalTranscript, ite_eq_right payout0, ite_eq_left payout1,
          swapCanonicalPostTransfers, ite_eq_right dataNonempty]
        exact drive_swapTransfer1_noCallback
          (Nat.eq_zero_of_not_pos dataNonempty) witness
    · exact False.elim (positiveOutput.elim payout0 payout1)

def swapControlState : State :=
  { State.empty 0 0 with
    token0 := 100, token1 := 200, unlocked := 1,
    reserve0 := ⟨10, by decide⟩, reserve1 := ⟨10, by decide⟩ }

def swapControlContext : Context :=
  { pair := 0, sender := 400, value := 0, timestamp := 0,
    isStatic := false, invocation := [] }

theorem swap_uint112_control :
    SwapContextConditions swapControlContext ∧
      swapControlState.unlocked = 1 ∧
      ((1 : B256) > 0 ∨ (0 : B256) > 0) ∧
        (1 : B256).toNat < 10 ∧ (0 : B256).toNat < 10 ∧
        (300 : Adr) ≠ 100 ∧ (300 : Adr) ≠ 200 ∧
        (10 : B256).toNat < 2 ^ 112 ∧
        (let inputs := swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10
         inputs.1 > 0 ∨ inputs.2 > 0) ∧
        swapCheck (Nat.toB256 (2 ^ 112)) 10
          (swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10).1
          (swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10).2 10 10 = .ok () ∧
        (Nat.toB256 (2 ^ 112)).toNat = 2 ^ 112 ∧
        ¬((Nat.toB256 (2 ^ 112)).toNat < 2 ^ 112) ∧
        ¬((runTyped swapControlState swapControlContext
          (.swap 1 0 300 [])
          (swapCanonicalTranscript 1 0 (Nat.toB256 (2 ^ 112)) 10 [])).status = .success []) := by
  change
    (0 = (0 : B256) ∧ false = false) ∧
      ((1 : B256) = 1 ∧
        ((1 : B256) > 0 ∨ (0 : B256) > 0) ∧
          (1 : B256).toNat < 10 ∧ (0 : B256).toNat < 10 ∧
          (300 : Adr) ≠ 100 ∧ (300 : Adr) ≠ 200 ∧
          (10 : B256).toNat < 2 ^ 112 ∧
          (let inputs := swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10
           inputs.1 > 0 ∨ inputs.2 > 0) ∧
          swapCheck (Nat.toB256 (2 ^ 112)) 10
            (swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10).1
            (swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10).2 10 10 = .ok () ∧
          (Nat.toB256 (2 ^ 112)).toNat = 2 ^ 112 ∧
          ¬((Nat.toB256 (2 ^ 112)).toNat < 2 ^ 112) ∧
          ¬((runTyped swapControlState swapControlContext
            (.swap 1 0 300 [])
            (swapCanonicalTranscript 1 0 (Nat.toB256 (2 ^ 112)) 10 [])).status = .success []))
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · have bounded : 2 ^ 112 < 2 ^ 256 := by decide
    have word : (Nat.toB256 (2 ^ 112)).toNat = 2 ^ 112 :=
      B256.toNat_toB256_of_lt bounded
    simp only [swapCheck, swapInputs, word]
    decide
  constructor
  · rfl
  constructor
  · decide
  · change ¬(RunStatus.failed (.sourceGuard "UniswapV2: OVERFLOW") = .success [])
    intro impossible
    cases impossible

def driveRequests (fuel : Nat) (segment : SegmentResult) (transcript : Transcript) : List Request :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match segment with
    | .finished _ _ | .failed _ _ => []
    | .suspended frame request continuation =>
      match transcript with
      | .next result turns tail =>
        if request.requiresCode && !result.codeExists then
          request :: driveRequests fuel (resumeSegment frame request continuation result) tail
        else
          let executed := driveTurns fuel frame request 0 turns
          if executed.complete then
            let settled := if result.success then executed.frame
              else { executed.frame with current := frame.current }
            request :: driveRequests fuel (resumeSegment settled request continuation result) tail
          else [request]
      | _ => [request]

def runTypedRequests (st : State) (ctx : Context) (entry : Entry) (transcript : Transcript) : List Request :=
  let current : Checkpoint := { state := st, logs := [], updates := [] }
  driveRequests (transcript.work + 2) (startTyped current ctx entry) transcript

theorem driveTurns_context {fuel : Nat} {frame : Frame} {request : Request}
    {turn : Nat} {turns : Transcript} :
    (driveTurns fuel frame request turn turns).frame.context = frame.context := by
  induction fuel generalizing frame turn turns with
  | zero => rfl
  | succ fuel ih =>
    cases turns with
    | done => rfl
    | next result nested tail => rfl
    | foreignLog emitter topics data tail =>
      cases static : externalStatic frame request with
      | false => simp only [driveTurns, static, Bool.false_eq_true, ite_false, ih]
      | true => simp only [driveTurns, static, ite_true]
    | invoke sender value isStatic entry nested tail =>
      cases child : drive fuel (startTyped frame.current
          (childContext frame request turn sender value isStatic) entry) nested with
      | mk status childFrame remaining childReturns =>
        cases status with
        | incomplete => simp only [driveTurns, child]
        | success returndata => simp only [driveTurns, child, ih]
        | failed failure => simp only [driveTurns, child, ih]

theorem Frame.settleExternal_context {frame : Frame} {fuel : Nat}
    {request : Request} {result : ExternalResult} {turns : Transcript} :
    (frame.settleExternal fuel request result turns).context = frame.context := by
  rw [Frame.settleExternal]
  cases result.success
  · exact driveTurns_context
  · exact driveTurns_context

theorem driveRequests_terminal {fuel : Nat} {segment : SegmentResult} {transcript : Transcript}
    {returndata : Bytes} (terminal : segment.Terminal)
    (successful : (drive fuel segment transcript).status = .success returndata) :
    driveRequests fuel segment transcript = [] := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    cases segment with
    | finished frame output => rfl
    | failed frame failure =>
      exact False.elim (drive_failed_not_success (fuel + 1) frame failure transcript returndata successful)
    | suspended frame request continuation => cases terminal

theorem driveRequests_suspended_success {fuel : Nat} {frame : Frame} {request : Request}
    {continuation : Continuation} {transcript : Transcript} {returndata : Bytes}
    (successful : (drive (fuel + 1) (.suspended frame request continuation) transcript).status =
      .success returndata) :
    ∃ result turns tail, transcript = .next result turns tail ∧
      driveRequests (fuel + 1) (.suspended frame request continuation) transcript =
        request :: driveRequests fuel
          (resumeSegment (frame.settleExternal fuel request result turns)
            request continuation result) tail := by
  cases transcript with
  | done => cases successful
  | foreignLog emitter topics data tail => cases successful
  | invoke sender value isStatic entry child tail => cases successful
  | next result turns tail =>
    by_cases missing : (request.requiresCode && !result.codeExists) = true
    · have failed : resumeSegment frame request continuation result =
          (frame.beginResume request).fail .emptyRevert := by
        simp only [resumeSegment, decodeExternal, missing, ite_true]
      simp only [drive, missing, ite_true, failed, Frame.fail] at successful
      exact False.elim (drive_failed_not_success fuel _ .emptyRevert tail returndata successful)
    · by_cases complete : (driveTurns fuel frame request 0 turns).complete = true
      · refine ⟨result, turns, tail, rfl, ?_⟩
        simp only [driveRequests, ite_eq_right missing, ite_eq_left complete, Frame.settleExternal]
      · simp only [drive, ite_eq_right missing, ite_eq_right complete] at successful
        cases successful

theorem drive_swapBalance1_callback_requests {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {balance0 : B256} {transcript : Transcript} {returndata : Bytes}
    (siteEq : request.site = .swapBalance1) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.swapBalance1 locals balance0))
      transcript).status = .success returndata) :
    (driveRequests fuel (.suspended frame request (.swapBalance1 locals balance0)) transcript).filter
      (fun r => r.site == .swapCallback) = [] := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, reqEq⟩ := driveRequests_suspended_success successful
    obtain ⟨result', turns', tail', shape', _complete, resumedSuccess, _frameEq⟩ :=
      drive_suspended_success successful
    cases shape.symm.trans shape'
    have staticExternal : externalStatic frame request = true := by
      rw [externalStatic, kind]
      cases frame.context.isStatic <;> rfl
    have settled := Frame.settleExternal_static_frame frame fuel request result turns staticExternal
    rw [settled] at resumedSuccess reqEq
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
        let inputs := swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
          locals.reserves.reserve0.val locals.reserves.reserve1.val
        simp only [resumeSegment, decoded] at resumedSuccess reqEq
        cases checked : swapCheck balance0 balance1 inputs.1 inputs.2
            locals.reserves.reserve0.val locals.reserves.reserve1.val with
        | error failure =>
          dsimp only [inputs] at checked
          simp only [checked, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _ failure tail returndata resumedSuccess)
        | ok accepted =>
          cases accepted
          dsimp only [inputs] at checked
          simp only [checked] at resumedSuccess reqEq
          have terminal := Frame.finishUpdated_terminal (frame.beginResume request)
            balance0 balance1 locals.reserves false
            (some (.swap (frame.beginResume request).context.sender
              (Nat.toB256 inputs.1) (Nat.toB256 inputs.2)
              locals.amount0Out locals.amount1Out locals.recipient)) []
          have emptyTail := driveRequests_terminal terminal resumedSuccess
          have notTrue : ¬((request.site == .swapCallback) = true) := by
            rw [siteEq]
            decide
          rw [reqEq, List.filter_cons, ite_eq_right notTrue, emptyTail, List.filter_nil]

theorem drive_swapBalance0_callback_requests {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (siteEq : request.site = .swapBalance0) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.swapBalance0 locals))
      transcript).status = .success returndata) :
    (driveRequests fuel (.suspended frame request (.swapBalance0 locals)) transcript).filter
      (fun r => r.site == .swapCallback) = [] := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, reqEq⟩ := driveRequests_suspended_success successful
    obtain ⟨result', turns', tail', shape', _complete, resumedSuccess, _frameEq⟩ :=
      drive_suspended_success successful
    cases shape.symm.trans shape'
    have staticExternal : externalStatic frame request = true := by
      rw [externalStatic, kind]
      cases frame.context.isStatic <;> rfl
    have settled := Frame.settleExternal_static_frame frame fuel request result turns staticExternal
    rw [settled] at resumedSuccess reqEq
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
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess reqEq
        have emptyTail := drive_swapBalance1_callback_requests
          (frame := frame.beginResume request)
          (request := requestFor .swapBalance1 locals.token1
            (.balanceOf (frame.beginResume request).context.pair))
          rfl rfl resumedSuccess
        have notTrue : ¬((request.site == .swapCallback) = true) := by
          rw [siteEq]
          decide
        rw [reqEq, List.filter_cons, ite_eq_right notTrue]
        exact emptyTail

theorem drive_swapCallback_requests {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (reqDef : request = requestFor .swapCallback locals.recipient
      (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data))
    (successful : (drive fuel (.suspended frame request (.swapCallback locals))
      transcript).status = .success returndata) :
    (driveRequests fuel (.suspended frame request (.swapCallback locals)) transcript).filter
      (fun r => r.site == .swapCallback) =
      [requestFor .swapCallback locals.recipient
        (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data)] := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, reqEq⟩ := driveRequests_suspended_success successful
    obtain ⟨result', turns', tail', shape', _complete, resumedSuccess, _frameEq⟩ :=
      drive_suspended_success successful
    cases shape.symm.trans shape'
    cases decoded : decodeExternal request result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | address address =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess reqEq
        have emptyTail := drive_swapBalance0_callback_requests
          (frame := (frame.settleExternal fuel request result turns).beginResume request)
          (request := requestFor .swapBalance0 locals.token0
            (.balanceOf ((frame.settleExternal fuel request result turns).beginResume request).context.pair))
          rfl rfl resumedSuccess
        have isTrue : ((request.site == .swapCallback) = true) := by
          rw [reqDef]
          rfl
        rw [reqEq, List.filter_cons, ite_eq_left isTrue, emptyTail, reqDef]

theorem Frame.afterSwapTransfer1_callback_requests {fuel : Nat} {frame : Frame}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (frame.afterSwapTransfer1 locals) transcript).status =
      .success returndata) :
    (driveRequests fuel (frame.afterSwapTransfer1 locals) transcript).filter
      (fun r => r.site == .swapCallback) =
      if locals.data.length > 0 then
        [requestFor .swapCallback locals.recipient
          (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data)]
      else [] := by
  by_cases data : locals.data.length > 0
  · simp only [Frame.afterSwapTransfer1, ite_eq_left data, Frame.suspend] at successful ⊢
    exact drive_swapCallback_requests rfl successful
  · simp only [Frame.afterSwapTransfer1, ite_eq_right data, Frame.suspend] at successful ⊢
    exact drive_swapBalance0_callback_requests rfl rfl successful

theorem drive_swapTransfer1_callback_requests {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (siteEq : request.site = .swapTransfer1)
    (successful : (drive fuel (.suspended frame request (.swapTransfer1 locals))
      transcript).status = .success returndata) :
    (driveRequests fuel (.suspended frame request (.swapTransfer1 locals)) transcript).filter
      (fun r => r.site == .swapCallback) =
      if locals.data.length > 0 then
        [requestFor .swapCallback locals.recipient
          (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data)]
      else [] := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, reqEq⟩ := driveRequests_suspended_success successful
    obtain ⟨result', turns', tail', shape', _complete, resumedSuccess, _frameEq⟩ :=
      drive_suspended_success successful
    cases shape.symm.trans shape'
    cases decoded : decodeExternal request result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | address address =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded] at resumedSuccess reqEq
        have tailFilter := Frame.afterSwapTransfer1_callback_requests
          (frame := (frame.settleExternal fuel request result turns).beginResume request)
          (locals := locals) (transcript := tail) (returndata := returndata) resumedSuccess
        have senderEq :
            ((frame.settleExternal fuel request result turns).beginResume request).context.sender =
              frame.context.sender := by
          change ((frame.settleExternal fuel request result turns).context).sender = frame.context.sender
          rw [Frame.settleExternal_context]
        rw [senderEq] at tailFilter
        have notTrue : ¬((request.site == .swapCallback) = true) := by
          rw [siteEq]
          decide
        rw [reqEq, List.filter_cons, ite_eq_right notTrue, tailFilter]

theorem Frame.afterSwapTransfer0_callback_requests {fuel : Nat} {frame : Frame}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (frame.afterSwapTransfer0 locals) transcript).status =
      .success returndata) :
    (driveRequests fuel (frame.afterSwapTransfer0 locals) transcript).filter
      (fun r => r.site == .swapCallback) =
      if locals.data.length > 0 then
        [requestFor .swapCallback locals.recipient
          (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data)]
      else [] := by
  by_cases amount1 : locals.amount1Out > 0
  · simp only [Frame.afterSwapTransfer0, ite_eq_left amount1, Frame.suspend] at successful ⊢
    exact drive_swapTransfer1_callback_requests rfl successful
  · simp only [Frame.afterSwapTransfer0, ite_eq_right amount1] at successful ⊢
    exact Frame.afterSwapTransfer1_callback_requests successful

theorem drive_swapTransfer0_callback_requests {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (siteEq : request.site = .swapTransfer0)
    (successful : (drive fuel (.suspended frame request (.swapTransfer0 locals))
      transcript).status = .success returndata) :
    (driveRequests fuel (.suspended frame request (.swapTransfer0 locals)) transcript).filter
      (fun r => r.site == .swapCallback) =
      if locals.data.length > 0 then
        [requestFor .swapCallback locals.recipient
          (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data)]
      else [] := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, reqEq⟩ := driveRequests_suspended_success successful
    obtain ⟨result', turns', tail', shape', _complete, resumedSuccess, _frameEq⟩ :=
      drive_suspended_success successful
    cases shape.symm.trans shape'
    cases decoded : decodeExternal request result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | address address =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded] at resumedSuccess reqEq
        have tailFilter := Frame.afterSwapTransfer0_callback_requests
          (frame := (frame.settleExternal fuel request result turns).beginResume request)
          (locals := locals) (transcript := tail) (returndata := returndata) resumedSuccess
        have senderEq :
            ((frame.settleExternal fuel request result turns).beginResume request).context.sender =
              frame.context.sender := by
          change ((frame.settleExternal fuel request result turns).context).sender = frame.context.sender
          rw [Frame.settleExternal_context]
        rw [senderEq] at tailFilter
        have notTrue : ¬((request.site == .swapCallback) = true) := by
          rw [siteEq]
          decide
        rw [reqEq, List.filter_cons, ite_eq_right notTrue, tailFilter]

theorem drive_startTyped_swap_callback_request {fuel : Nat} {current : Checkpoint} {ctx : Context}
    {amount0Out amount1Out : B256} {recipient : Adr} {data : Bytes}
    {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (startTyped current ctx (.swap amount0Out amount1Out recipient data))
      transcript).status = .success returndata) :
    (driveRequests fuel (startTyped current ctx (.swap amount0Out amount1Out recipient data))
      transcript).filter (fun r => r.site == .swapCallback) =
      if data.length > 0 then
        [requestFor .swapCallback recipient (.callback ctx.sender amount0Out amount1Out data)]
      else [] := by
  by_cases paid : ctx.value ≠ 0
  · simp only [startTyped, startImmediate, ite_eq_left paid, Frame.fail] at successful
    exact False.elim (drive_failed_not_success fuel _ .emptyRevert transcript returndata successful)
  · by_cases unlocked : current.state.unlocked = 1
    · by_cases staticContext : ctx.isStatic = true
      · simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, Frame.lock,
          Frame.enter, ite_eq_left unlocked, staticContext, ite_true, Frame.fail] at successful
        exact False.elim (drive_failed_not_success fuel _ .staticWrite transcript returndata successful)
      · let lockedFrame : Frame :=
          { Frame.enter current ctx (.swap amount0Out amount1Out recipient data) with
            current := { current with state := { current.state with unlocked := 0 } } }
        let locals : SwapLocals :=
          { recipient := recipient, reserves := current.state.cachedReserves,
            token0 := current.state.token0, token1 := current.state.token1,
            amount0Out := amount0Out, amount1Out := amount1Out, data := data }
        have enteredUnlocked :
            (Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).current.state.unlocked = 1 :=
          unlocked
        have enteredStatic :
            ¬(Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).context.isStatic = true :=
          staticContext
        have opened : (Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).lock =
            .ok lockedFrame := by
          rw [Frame.lock, ite_eq_left enteredUnlocked, ite_eq_right enteredStatic]
          rfl
        have stage : startTyped current ctx (.swap amount0Out amount1Out recipient data) =
            if amount0Out > 0 ∨ amount1Out > 0 then
              if amount0Out.toNat < current.state.reserve0.val ∧ amount1Out.toNat < current.state.reserve1.val then
                if recipient ≠ current.state.token0 ∧ recipient ≠ current.state.token1 then
                  if amount0Out > 0 then
                    lockedFrame.suspend .swapTransfer0 current.state.token0
                      (.transfer recipient amount0Out) (.swapTransfer0 locals)
                  else lockedFrame.afterSwapTransfer0 locals
                else lockedFrame.fail (.sourceGuard "UniswapV2: INVALID_TO")
              else lockedFrame.fail (.sourceGuard "UniswapV2: INSUFFICIENT_LIQUIDITY")
            else lockedFrame.fail (.sourceGuard "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT") := by
          simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, opened]
          rfl
        by_cases positiveOutput : amount0Out > 0 ∨ amount1Out > 0
        · by_cases liquidity : amount0Out.toNat < current.state.reserve0.val ∧
              amount1Out.toNat < current.state.reserve1.val
          · by_cases validRecipient : recipient ≠ current.state.token0 ∧ recipient ≠ current.state.token1
            · by_cases payout0 : amount0Out > 0
              · rw [stage, ite_eq_left positiveOutput, ite_eq_left liquidity,
                  ite_eq_left validRecipient, ite_eq_left payout0] at successful ⊢
                rw [Frame.suspend] at successful ⊢
                have res := drive_swapTransfer0_callback_requests (frame := lockedFrame)
                  (locals := locals) rfl successful
                simpa only [lockedFrame, Frame.enter, locals] using res
              · rw [stage, ite_eq_left positiveOutput, ite_eq_left liquidity,
                  ite_eq_left validRecipient, ite_eq_right payout0] at successful ⊢
                have res := Frame.afterSwapTransfer0_callback_requests (frame := lockedFrame)
                  (locals := locals) successful
                simpa only [lockedFrame, Frame.enter, locals] using res
            · rw [stage, ite_eq_left positiveOutput, ite_eq_left liquidity,
                ite_eq_right validRecipient] at successful
              exact False.elim (drive_failed_not_success fuel _
                (.sourceGuard "UniswapV2: INVALID_TO") transcript returndata successful)
          · rw [stage, ite_eq_left positiveOutput, ite_eq_right liquidity] at successful
            exact False.elim (drive_failed_not_success fuel _
              (.sourceGuard "UniswapV2: INSUFFICIENT_LIQUIDITY") transcript returndata successful)
        · rw [stage, ite_eq_right positiveOutput] at successful
          exact False.elim (drive_failed_not_success fuel _
            (.sourceGuard "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT") transcript returndata successful)
    · have enteredLocked :
          ¬(Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).current.state.unlocked = 1 :=
        unlocked
      have closed : (Frame.enter current ctx (.swap amount0Out amount1Out recipient data)).lock =
          .error (.sourceGuard "UniswapV2: LOCKED") := by
        rw [Frame.lock, ite_eq_right enteredLocked]
      simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, closed, Frame.fail] at successful
      exact False.elim (drive_failed_not_success fuel _
        (.sourceGuard "UniswapV2: LOCKED") transcript returndata successful)

theorem runTyped_swap_callback_request {st : State} {ctx : Context}
    {amount0Out amount1Out : B256} {recipient : Adr} {data : Bytes}
    {transcript : Transcript} {returndata : Bytes}
    (successful :
      (runTyped st ctx (.swap amount0Out amount1Out recipient data) transcript).status =
        .success returndata) :
    (runTypedRequests st ctx (.swap amount0Out amount1Out recipient data) transcript).filter
      (fun r => r.site == .swapCallback) =
      if data.length > 0 then
        [requestFor .swapCallback recipient (.callback ctx.sender amount0Out amount1Out data)]
      else [] := by
  exact drive_startTyped_swap_callback_request
    (current := { state := st, logs := [], updates := [] })
    (ctx := ctx) (amount0Out := amount0Out) (amount1Out := amount1Out)
    (recipient := recipient) (data := data) (fuel := transcript.work + 2)
    (transcript := transcript) (returndata := returndata) successful

end Blanc.Lift.UniswapV2Pair
