import Blanc.Lift.UniswapV2Pair.BurnForwardBody

/-!
# Burn forward guards from the model's acceptance

`BurnForwardGuards` (`BurnForwardBody.lean`) is what the forward Burn construction needs beyond its
callee-only environment.  This module states the model's Burn guards at the actual answers
(`BurnModelConditions`), proves that every Burn the model accepts passes them
(`runTyped_burn_conditions`), and turns them into `BurnForwardGuards` at a frame whose storage
represents the entry state (`BurnForwardEnv.accepted`).
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- **The model's Burn guards** at the initial token answers `balance0`, `balance1`, the factory
answer `feeTo` and the final answers `final0`, `final1`, from the state `st` the frame enters: the
call is non-payable and non-static, the lock is open, the protocol fee mints at the locked state,
the burn pricing at the Pair's own LP balance accepts with both amounts positive, the LP debit
accepts, and the reserve update accepts both final answers (they fit `uint112`). -/
def BurnModelConditions (st : State) (ctx : Context) (balance0 balance1 : B256) (feeTo : Adr)
    (final0 final1 : B256) : Prop :=
  ctx.value = 0 ∧ ctx.isStatic = false ∧ st.unlocked = 1 ∧
  ∃ (fee : FeeResult) (amount0 amount1 : Nat) (post : State) (events : List Event),
    mintFee { st with unlocked := 0 } feeTo st.reserve0.val st.reserve1.val = .ok fee ∧
    burnAmounts (st.balanceOf ctx.pair) balance0 balance1 fee.state.totalSupply =
      .ok (amount0, amount1) ∧
    0 < amount0 ∧ 0 < amount1 ∧
    fee.state.burnLP ctx.pair (st.balanceOf ctx.pair) = .ok (post, events) ∧
    final0.toNat < 2 ^ 112 ∧ final1.toNat < 2 ^ 112

/-! ## Model acceptance gives the Burn guards -/

/-- A successful second final balance query leaves both final answers inside `uint112`. -/
theorem drive_burnFinalBalance1_bounds {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {balance0 : B256} {owner : Adr} {transcript : Transcript}
    {returndata : Bytes} (operation : request.operation = .balanceOf owner)
    (successful : (drive fuel (.suspended frame request (.burnFinalBalance1 priced balance0))
      transcript).status = .success returndata) :
    balance0.toNat < 2 ^ 112 ∧ transcript.firstWord.toNat < 2 ^ 112 := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, _⟩ :=
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
      | unit =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance1 =>
        have observedWord := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded] at resumedSuccess
        unfold Frame.finishUpdated at resumedSuccess
        split at resumedSuccess
        · simp only [Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _ _ tail returndata resumedSuccess)
        · next post event update updated =>
          have bounds := State.update_bounds updated
          refine ⟨bounds.1, ?_⟩
          rw [shape, Transcript.firstWord, ← observedWord]
          exact bounds.2

/-- A successful first final balance query leaves both final answers inside `uint112`. -/
theorem drive_burnFinalBalance0_bounds {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {owner : Adr} {transcript : Transcript} {returndata : Bytes}
    (operation : request.operation = .balanceOf owner)
    (successful : (drive fuel (.suspended frame request (.burnFinalBalance0 priced))
      transcript).status = .success returndata) :
    transcript.firstWord.toNat < 2 ^ 112 ∧ transcript.ownTail.firstWord.toNat < 2 ^ 112 := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, _⟩ :=
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
      | unit =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance0 =>
        have observedWord := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess
        have bounds := drive_burnFinalBalance1_bounds rfl resumedSuccess
        rw [shape, Transcript.firstWord, Transcript.ownTail, ← observedWord]
        exact bounds

/-- A successful second transfer leaves both final answers inside `uint112`. -/
theorem drive_burnTransfer1_bounds {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (.suspended frame request (.burnTransfer1 priced))
      transcript).status = .success returndata) :
    transcript.ownTail.firstWord.toNat < 2 ^ 112 ∧
      transcript.ownTail.ownTail.firstWord.toNat < 2 ^ 112 := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, _⟩ :=
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
      | word value =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess
        rw [shape, Transcript.ownTail]
        exact drive_burnFinalBalance0_bounds rfl resumedSuccess

/-- A successful first transfer leaves both final answers inside `uint112`. -/
theorem drive_burnTransfer0_bounds {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (.suspended frame request (.burnTransfer0 priced))
      transcript).status = .success returndata) :
    transcript.ownTail.ownTail.firstWord.toNat < 2 ^ 112 ∧
      transcript.ownTail.ownTail.ownTail.firstWord.toNat < 2 ^ 112 := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, _⟩ :=
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
      | word value =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess
        rw [shape, Transcript.ownTail]
        exact drive_burnTransfer1_bounds resumedSuccess

/-- The guards of the model's post-fee Burn continuation (`Frame.burnAfterFee`), over the transcript
`rest` that starts at the first transfer. -/
def BurnAfterFeeGuards (pair : Adr) (liquidity balance0 balance1 : B256) (fee : FeeResult)
    (rest : Transcript) : Prop :=
  ∃ (amount0 amount1 : Nat) (post : State) (events : List Event),
    burnAmounts liquidity balance0 balance1 fee.state.totalSupply = .ok (amount0, amount1) ∧
    0 < amount0 ∧ 0 < amount1 ∧
    fee.state.burnLP pair liquidity = .ok (post, events) ∧
    rest.ownTail.ownTail.firstWord.toNat < 2 ^ 112 ∧
    rest.ownTail.ownTail.ownTail.firstWord.toNat < 2 ^ 112

/-- A successful post-fee Burn continuation passes all of its guards. -/
theorem Frame.burnAfterFee_guards {fuel : Nat} {frame : Frame} {observed : BurnObserved}
    {fee : FeeResult} {rest : Transcript} {returndata : Bytes}
    (successful : (drive fuel (frame.burnAfterFee observed fee) rest).status = .success returndata) :
    BurnAfterFeeGuards frame.context.pair observed.liquidity observed.balance0 observed.balance1 fee
      rest := by
  unfold Frame.burnAfterFee at successful
  cases priced : burnAmounts observed.liquidity observed.balance0 observed.balance1
      fee.state.totalSupply with
  | error failure =>
    simp only [priced, Frame.fail] at successful
    exact False.elim (drive_failed_not_success fuel _ failure rest returndata successful)
  | ok amounts =>
    rcases amounts with ⟨amount0, amount1⟩
    simp only [priced] at successful
    by_cases positive : amount0 > 0 ∧ amount1 > 0
    · rw [ite_eq_left positive] at successful
      cases burned : fee.state.burnLP frame.context.pair observed.liquidity with
      | error failure =>
        simp only [burned, Frame.fail] at successful
        exact False.elim (drive_failed_not_success fuel _ failure rest returndata successful)
      | ok result =>
        rcases result with ⟨post, events⟩
        simp only [burned, Frame.suspend] at successful
        have bounds := drive_burnTransfer0_bounds successful
        exact ⟨amount0, amount1, post, events, priced, positive.1, positive.2, burned, bounds.1,
          bounds.2⟩
    · simp only [ite_eq_right positive, Frame.fail] at successful
      exact False.elim (drive_failed_not_success fuel _
        (.sourceGuard "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED") rest returndata successful)

/-- A successful Burn fee query passes the fee mint at its decoded recipient and every later guard. -/
theorem drive_burnFee_guards {fuel : Nat} {frame : Frame} {request : Request}
    {observed : BurnObserved} {transcript : Transcript} {returndata : Bytes}
    (operation : request.operation = .feeTo) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.burnFee observed))
      transcript).status = .success returndata) :
    ∃ fee, mintFee frame.current.state transcript.firstWord.toAdr
        observed.locals.reserves.reserve0.val observed.locals.reserves.reserve1.val = .ok fee ∧
      BurnAfterFeeGuards frame.context.pair observed.liquidity observed.balance0 observed.balance1
        fee transcript.ownTail := by
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
      | word value =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | address feeTo =>
        have recipientEq := decodeExternal_feeTo_address operation decoded
        cases charged : mintFee (frame.beginResume request).current.state feeTo
            observed.locals.reserves.reserve0.val observed.locals.reserves.reserve1.val with
        | error failure =>
          simp only [resumeSegment, decoded, charged, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _ failure tail returndata resumedSuccess)
        | ok fee =>
          simp only [resumeSegment, decoded, charged] at resumedSuccess
          refine ⟨fee, ?_, ?_⟩
          · rw [shape, Transcript.firstWord, ← recipientEq]
            exact charged
          · rw [shape, Transcript.ownTail]
            exact Frame.burnAfterFee_guards (frame := frame.beginResume request) resumedSuccess

/-- A successful second initial balance query passes the fee mint and every later guard. -/
theorem drive_burnInitialBalance1_guards {fuel : Nat} {frame : Frame} {request : Request}
    {locals : BurnLocals} {owner : Adr} {balance0 : B256} {transcript : Transcript}
    {returndata : Bytes}
    (operation : request.operation = .balanceOf owner) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.burnInitialBalance1 locals balance0))
      transcript).status = .success returndata) :
    ∃ fee, mintFee frame.current.state transcript.ownTail.firstWord.toAdr
        locals.reserves.reserve0.val locals.reserves.reserve1.val = .ok fee ∧
      BurnAfterFeeGuards frame.context.pair (frame.current.state.balanceOf frame.context.pair)
        balance0 transcript.firstWord fee transcript.ownTail.ownTail := by
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
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess
        obtain ⟨fee, charged, guards⟩ := drive_burnFee_guards rfl rfl resumedSuccess
        have firstEq : transcript.firstWord = balance1 := by
          rw [shape, Transcript.firstWord, ← observedWord]
        have tailEq : transcript.ownTail = tail := by rw [shape, Transcript.ownTail]
        rw [firstEq, tailEq]
        exact ⟨fee, charged, guards⟩

/-- A successful first initial balance query passes the fee mint and every later guard at the
transcript's answers. -/
theorem drive_burnInitialBalance0_guards {fuel : Nat} {frame : Frame} {request : Request}
    {locals : BurnLocals} {owner : Adr} {transcript : Transcript} {returndata : Bytes}
    (operation : request.operation = .balanceOf owner) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.burnInitialBalance0 locals))
      transcript).status = .success returndata) :
    ∃ fee, mintFee frame.current.state transcript.ownTail.ownTail.firstWord.toAdr
        locals.reserves.reserve0.val locals.reserves.reserve1.val = .ok fee ∧
      BurnAfterFeeGuards frame.context.pair (frame.current.state.balanceOf frame.context.pair)
        transcript.firstWord transcript.ownTail.firstWord fee
        transcript.ownTail.ownTail.ownTail := by
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
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess
        have guards := drive_burnInitialBalance1_guards rfl rfl resumedSuccess
        have firstEq : transcript.firstWord = balance0 := by
          rw [shape, Transcript.firstWord, ← observedWord]
        have tailEq : transcript.ownTail = tail := by rw [shape, Transcript.ownTail]
        rw [firstEq, tailEq]
        exact guards

/-- **The model's acceptance gives the Burn guards.**  Every Burn the model accepts — whatever the
transcript — passes `BurnModelConditions` at the transcript's answers: the two initial token
balances (its first two words), the factory's `feeTo` answer (its third word), and the two final
balances (its sixth and seventh words, after the two transfers). -/
theorem runTyped_burn_conditions {st : State} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {returndata : Bytes}
    (successful : (runTyped st ctx (.burn recipient) transcript).status = .success returndata) :
    BurnModelConditions st ctx transcript.firstWord transcript.ownTail.firstWord
      transcript.ownTail.ownTail.firstWord.toAdr
      transcript.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord
      transcript.ownTail.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord := by
  let current : Checkpoint := { state := st, logs := [], updates := [] }
  change (drive (transcript.work + 2) (startTyped current ctx (.burn recipient)) transcript).status =
    .success returndata at successful
  by_cases paid : ctx.value ≠ 0
  · simp only [startTyped, startImmediate, ite_eq_left paid, Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _ .emptyRevert transcript returndata successful)
  by_cases unlocked : st.unlocked = 1
  swap
  · have enteredLocked : ¬(Frame.enter current ctx (.burn recipient)).current.state.unlocked = 1 :=
      unlocked
    have closed : (Frame.enter current ctx (.burn recipient)).lock =
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
    { Frame.enter current ctx (.burn recipient) with
      current := { current with state := { st with unlocked := 0 } } }
  let locals : BurnLocals :=
    { recipient := recipient, reserves := st.cachedReserves, token0 := st.token0,
      token1 := st.token1 }
  have enteredUnlocked : (Frame.enter current ctx (.burn recipient)).current.state.unlocked = 1 :=
    unlocked
  have enteredStatic : ¬(Frame.enter current ctx (.burn recipient)).context.isStatic = true :=
    staticContext
  have opened : (Frame.enter current ctx (.burn recipient)).lock = .ok lockedFrame := by
    rw [Frame.lock, ite_eq_left enteredUnlocked, ite_eq_right enteredStatic]
    rfl
  have stage : startTyped current ctx (.burn recipient) =
      lockedFrame.suspend .burnInitialBalance0 locals.token0 (.balanceOf ctx.pair)
        (.burnInitialBalance0 locals) := by
    simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, opened]
    rfl
  rw [stage] at successful
  simp only [Frame.suspend] at successful
  obtain ⟨fee, charged, amount0, amount1, post, events, priced, positive0, positive1, burned,
    bound0, bound1⟩ := drive_burnInitialBalance0_guards rfl rfl successful
  have value : ctx.value = 0 := by
    by_contra h
    exact paid h
  have nonstatic : ctx.isStatic = false := by
    cases h : ctx.isStatic
    · rfl
    · exact absurd h staticContext
  exact ⟨value, nonstatic, unlocked, fee, amount0, amount1, post, events, charged, priced,
    positive0, positive1, burned, bound0, bound1⟩

/-! ## The model's guards give the forward guards -/

/-- **The Burn forward guards from the model.**  At a frame whose storage represents `st` over rows
inside a separated universe holding the LP row of the factory's actual `feeTo` answer, the model's
Burn guards at the callee environment's actual answers (`BurnModelConditions`) give
`BurnForwardGuards`. -/
theorem BurnForwardEnv.guards_of_model {U K : WriterKey → Prop} {st : State}
    {pre : Nat → B256 → Nat} {post : Nat → B256 → Bytes → Nat}
    {sevm : Sevm} {b : Devm} {g : Nat} (env : BurnForwardEnv pre post sevm b g)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (rowFee : U (.balance env.feeTo))
    (conditions : BurnModelConditions st (writerContext sevm []) env.balance0 env.balance1
      env.feeTo env.final0 env.final1) :
    BurnForwardGuards K st sevm b env.d0 env.d1 env.dF env.back.e0 env.back.e1 := by
  obtain ⟨_, nonstatic, unlocked, fee, amount0, amount1, burnPost, events, feeAccepted, priced,
    positive0, positive1, burned, final0, final1⟩ := conditions
  have lockedRep := rep.burn_locked_world (sevm := sevm) (b := b)
  rcases lockedRep.fixed with ⟨_, _, _, _, _, cache0, cache1, _, _, _, _, _⟩
  change burnR0 sevm b = Nat.toB256 st.reserve0.val at cache0
  change burnR1 sevm b = Nat.toB256 st.reserve1.val at cache1
  have natCache0 : (burnR0 sevm b).toNat = st.reserve0.val := by
    rw [cache0]
    exact B256.toNat_toB256_of_lt (lt_trans st.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))
  have natCache1 : (burnR1 sevm b).toNat = st.reserve1.val := by
    rw [cache1]
    exact B256.toNat_toB256_of_lt (lt_trans st.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))
  have reply0 := balanceReplyMemory_ptr env.d0.returnData
    (balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget)
  have answer1 : feeBurnBalance1 (burnMem2 sevm env.d0 env.d1) = env.balance1 :=
    balanceReplyMemory_word reply0.wf sevm.currentTarget env.d1.returnData env.initial.long1
  refine ⟨unlocked, nonstatic, ⟨fee, ?_, amount0, amount1, burnPost, events, ?_, positive0,
    positive1, burned⟩, ?_, final0, final1⟩
  · rw [natCache0, natCache1]
    exact feeAccepted
  · rw [answer1]
    exact priced
  · exact fun _ _ _ _ => Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub
      (fun k member => by rw [List.mem_singleton.mp member]; exact rowFee)

end Blanc.Lift.UniswapV2Pair
