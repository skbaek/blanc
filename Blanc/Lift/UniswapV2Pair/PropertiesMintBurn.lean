import Blanc.Lift.UniswapV2Pair.PropertiesSwap

/-!
# RunTyped-level later-mint and burn-payout formulas for Uniswap V2 Pair

Driver-level execution proofs for later mint issuance and burn token payouts.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Exact later-mint economics: issues min(⌊a0·T/r0⌋, ⌊a1·T/r1⌋) LP tokens to recipient. -/
def LaterMintResult (_prior : State) (observed : MintObserved) (fee : FeeResult) (post : State)
    (returndata : Bytes) : Prop :=
  let liquidity := AMMArithmetic.mintLiquidity observed.amount0.toNat observed.amount1.toNat
    fee.state.totalSupply.toNat observed.reserves.reserve0.val observed.reserves.reserve1.val
  liquidity > 0 ∧
    liquidity < 2 ^ 256 ∧
    post.totalSupply.toNat = fee.state.totalSupply.toNat + liquidity ∧
    post.balanceOf = Blanc.ledgerCredit fee.state.balanceOf observed.recipient (Nat.toB256 liquidity) ∧
    post.reserve0.val = observed.balance0.toNat ∧
    post.reserve1.val = observed.balance1.toNat ∧
    returndata = encodeWords [Nat.toB256 liquidity]

/-- A successful later-mint continuation realizes its floor issuance, credit and return. -/
theorem Frame.mintAfterFee_later {frame final : Frame} {observed : MintObserved}
    {fee : FeeResult} {returndata : Bytes}
    (positiveSupply : fee.state.totalSupply ≠ 0)
    (accepted : frame.mintAfterFee observed fee = .finished final returndata) :
    LaterMintResult frame.current.state observed fee final.current.state returndata := by
  rw [Frame.mintAfterFee] at accepted
  cases priced : mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val with
  | error failure =>
    simp only [priced, Frame.fail] at accepted
    cases accepted
  | ok liquidity =>
    simp only [priced, ite_eq_right positiveSupply] at accepted
    by_cases positive : liquidity > 0
    · rw [ite_eq_left positive] at accepted
      cases minted : fee.state.mintLP observed.recipient (Nat.toB256 liquidity) with
      | error failure =>
        simp only [minted, Frame.fail] at accepted
        cases accepted
      | ok result =>
        rcases result with ⟨post, events⟩
        simp only [minted] at accepted
        have spec := mintAmount_later_spec positiveSupply priced
        have issued := State.mintLP_supply minted
        rw [B256.toNat_toB256_of_lt spec.2] at issued
        have ledger := State.mintLP_ledger minted
        have finalFields := Frame.finishUpdated_supply_reserves accepted
        have finalLedger := Frame.finishUpdated_ledger_output accepted
        have postState : (((frame.withEvents fee.state fee.events).withEvents fee.state []).withEvents post events).current.state = post := rfl
        rw [postState] at finalFields finalLedger
        rw [LaterMintResult]
        have bound := spec.2
        rw [spec.1] at bound
        refine ⟨?_, bound, ?_, ?_, finalFields.2.1, finalFields.2.2, ?_⟩
        · rw [spec.1] at positive
          exact positive
        · rw [finalFields.1, issued, spec.1]
        · rw [finalLedger.1, ledger.1, spec.1]
        · rw [finalLedger.2, spec.1]
    · simp only [ite_eq_right positive, Frame.fail] at accepted
      cases accepted

/-- The finite driver consumes the actual later-mint completion. -/
theorem Frame.mintAfterFee_driver_later {fuel : Nat} {frame : Frame} {observed : MintObserved}
    {fee : FeeResult} {transcript : Transcript} {returndata : Bytes}
    (positiveSupply : fee.state.totalSupply ≠ 0)
    (successful : (drive fuel (frame.mintAfterFee observed fee) transcript).status = .success returndata) :
    LaterMintResult frame.current.state observed fee
      (drive fuel (frame.mintAfterFee observed fee) transcript).frame.current.state returndata := by
  obtain ⟨final, finished, frameEq⟩ :=
    drive_terminal_success (Frame.mintAfterFee_terminal_later frame observed fee positiveSupply) successful
  rw [frameEq]
  exact Frame.mintAfterFee_later positiveSupply finished

/-- A successful later-mint fee query consumes the actual decoded recipient and completion. -/
theorem drive_mintFee_later {fuel : Nat} {frame : Frame} {request : Request}
    {observed : MintObserved} {transcript : Transcript} {returndata : Bytes}
    {fee : FeeResult}
    (feeAccepted : mintFee frame.current.state transcript.firstWord.toAdr
      observed.reserves.reserve0.val observed.reserves.reserve1.val = .ok fee)
    (positiveSupply : fee.state.totalSupply ≠ 0)
    (operation : request.operation = .feeTo) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.mintFee observed))
      transcript).status = .success returndata) :
    LaterMintResult frame.current.state observed fee
      (drive fuel (.suspended frame request (.mintFee observed))
        transcript).frame.current.state returndata := by
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
        rw [shape, Transcript.firstWord, ← recipientEq] at feeAccepted
        cases charged : mintFee (frame.beginResume request).current.state feeTo
            observed.reserves.reserve0.val observed.reserves.reserve1.val with
        | error failure =>
          simp only [resumeSegment, decoded, charged, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _ failure tail returndata resumedSuccess)
        | ok fee' =>
          simp only [resumeSegment, decoded, charged] at resumedSuccess frameEq
          have frameState : (frame.beginResume request).current.state = frame.current.state := rfl
          rw [← frameState, charged] at feeAccepted
          have feeEq : fee' = fee := Except.ok.inj feeAccepted
          subst feeEq
          have later := Frame.mintAfterFee_driver_later positiveSupply resumedSuccess
          rw [frameEq]
          exact later

/-- Later mint's checked second observation reaches the exact source fee/completion result. -/
theorem drive_mintBalance1_later {fuel : Nat} {frame : Frame} {request : Request}
    {recipient owner : Adr} {reserves : CachedReserves} {balance0 : B256}
    {transcript : Transcript} {returndata : Bytes}
    {fee : FeeResult}
    (feeAccepted : mintFee frame.current.state transcript.ownTail.firstWord.toAdr
      reserves.reserve0.val reserves.reserve1.val = .ok fee)
    (positiveSupply : fee.state.totalSupply ≠ 0)
    (operation : request.operation = .balanceOf owner) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.mintBalance1 recipient reserves balance0))
      transcript).status = .success returndata) :
    LaterMintResult frame.current.state
      (mintObservation recipient reserves balance0 transcript.firstWord)
      fee
      (drive fuel (.suspended frame request (.mintBalance1 recipient reserves balance0))
        transcript).frame.current.state returndata := by
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
        have observedWord := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded] at resumedSuccess frameEq
        by_cases backing : reserves.reserve0.val ≤ balance0.toNat ∧
            reserves.reserve1.val ≤ balance1.toNat
        · rw [ite_eq_left backing] at resumedSuccess frameEq
          simp only [Frame.suspend] at resumedSuccess frameEq
          have frameState : (frame.beginResume request).current.state = frame.current.state := rfl
          have feeAccepted' : mintFee (frame.beginResume request).current.state tail.firstWord.toAdr
              reserves.reserve0.val reserves.reserve1.val = .ok fee := by
            rw [frameState]
            simpa only [shape, Transcript.ownTail] using feeAccepted
          have later := drive_mintFee_later feeAccepted' positiveSupply rfl rfl resumedSuccess
          rw [frameEq]
          simpa only [shape, Transcript.firstWord, ← observedWord, mintObservation,
            Frame.beginResume] using later
        · simp only [ite_eq_right backing, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _
            (.sourceGuard "ds-math-sub-underflow") tail returndata resumedSuccess)

/-- The first mint balance query preserves its ledger and selects both actual returned words. -/
theorem drive_mintBalance0_later {fuel : Nat} {frame : Frame} {request : Request}
    {recipient owner : Adr} {reserves : CachedReserves}
    {transcript : Transcript} {returndata : Bytes}
    {fee : FeeResult}
    (feeAccepted : mintFee frame.current.state transcript.ownTail.ownTail.firstWord.toAdr
      reserves.reserve0.val reserves.reserve1.val = .ok fee)
    (positiveSupply : fee.state.totalSupply ≠ 0)
    (operation : request.operation = .balanceOf owner) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.mintBalance0 recipient reserves))
      transcript).status = .success returndata) :
    LaterMintResult frame.current.state
      (mintObservation recipient reserves transcript.firstWord transcript.ownTail.firstWord)
      fee
      (drive fuel (.suspended frame request (.mintBalance0 recipient reserves))
        transcript).frame.current.state returndata := by
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
        have observedWord := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess frameEq
        have frameState : (frame.beginResume request).current.state = frame.current.state := rfl
        have feeAccepted' : mintFee (frame.beginResume request).current.state tail.ownTail.firstWord.toAdr
            reserves.reserve0.val reserves.reserve1.val = .ok fee := by
          rw [frameState]
          simpa only [shape, Transcript.ownTail] using feeAccepted
        have later := drive_mintBalance1_later (frame := frame.beginResume request)
          feeAccepted' positiveSupply rfl rfl resumedSuccess
        rw [frameEq]
        simpa only [shape, Transcript.firstWord, Transcript.ownTail, ← observedWord,
          Frame.beginResume] using later

/-- Successful positive-supply entries derive their source guards and complete the later-mint formula. -/
theorem drive_startTyped_mint_later {fuel : Nat} {current : Checkpoint} {ctx : Context}
    {recipient : Adr} {transcript : Transcript} {returndata : Bytes}
    {fee : FeeResult}
    (feeAccepted : mintFee { current.state with unlocked := 0 }
      transcript.ownTail.ownTail.firstWord.toAdr
      current.state.reserve0.val current.state.reserve1.val = .ok fee)
    (positiveSupply : fee.state.totalSupply ≠ 0)
    (successful : (drive fuel (startTyped current ctx (.mint recipient)) transcript).status =
      .success returndata) :
    LaterMintResult current.state
      (mintObservation recipient current.state.cachedReserves
        transcript.firstWord transcript.ownTail.firstWord)
      fee
      (drive fuel (startTyped current ctx (.mint recipient))
        transcript).frame.current.state returndata := by
  by_cases paid : ctx.value ≠ 0
  · simp only [startTyped, startImmediate, ite_eq_left paid, Frame.fail] at successful
    exact False.elim (drive_failed_not_success fuel _ .emptyRevert transcript returndata successful)
  · by_cases unlocked : current.state.unlocked = 1
    · by_cases staticContext : ctx.isStatic = true
      · simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, Frame.lock,
          Frame.enter, ite_eq_left unlocked, staticContext, ite_true, Frame.fail] at successful
        exact False.elim (drive_failed_not_success fuel _ .staticWrite transcript returndata successful)
      · let lockedFrame : Frame :=
          { Frame.enter current ctx (.mint recipient) with
            current := { current with state := { current.state with unlocked := 0 } } }
        let reserves := current.state.cachedReserves
        have enteredUnlocked : (Frame.enter current ctx (.mint recipient)).current.state.unlocked = 1 :=
          unlocked
        have enteredStatic : ¬(Frame.enter current ctx (.mint recipient)).context.isStatic = true :=
          staticContext
        have opened : (Frame.enter current ctx (.mint recipient)).lock = .ok lockedFrame := by
          rw [Frame.lock, ite_eq_left enteredUnlocked, ite_eq_right enteredStatic]
          rfl
        have stage : startTyped current ctx (.mint recipient) =
            lockedFrame.suspend .mintBalance0 current.state.token0 (.balanceOf ctx.pair)
              (.mintBalance0 recipient reserves) := by
          simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, opened]
          rfl
        have suspendedSuccess :
            (drive fuel (.suspended lockedFrame
              (requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair))
              (.mintBalance0 recipient reserves)) transcript).status = .success returndata := by
          simpa only [stage, Frame.suspend] using successful
        have feeAccepted' : mintFee lockedFrame.current.state transcript.ownTail.ownTail.firstWord.toAdr
            reserves.reserve0.val reserves.reserve1.val = .ok fee := by
          exact feeAccepted
        have later := drive_mintBalance0_later (frame := lockedFrame)
          feeAccepted' positiveSupply rfl rfl suspendedSuccess
        rw [stage, Frame.suspend]
        simpa only [LaterMintResult, lockedFrame, Frame.enter, reserves] using later
    · have enteredLocked : ¬(Frame.enter current ctx (.mint recipient)).current.state.unlocked = 1 :=
        unlocked
      have closed : (Frame.enter current ctx (.mint recipient)).lock =
          .error (.sourceGuard "UniswapV2: LOCKED") := by
        rw [Frame.lock, ite_eq_right enteredLocked]
      simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, closed, Frame.fail] at successful
      exact False.elim (drive_failed_not_success fuel _
        (.sourceGuard "UniswapV2: LOCKED") transcript returndata successful)

/-- A successful mint with totalSupply (after the fee mint) T > 0 issues exactly
min(⌊a0·T/r0⌋, ⌊a1·T/r1⌋) LP tokens to the recipient, where a_i = balance_i − reserve_i. -/
theorem runTyped_mint_later {st : State} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {returndata : Bytes}
    {fee : FeeResult}
    (feeAccepted : mintFee { st with unlocked := 0 }
      transcript.ownTail.ownTail.firstWord.toAdr
      st.reserve0.val st.reserve1.val = .ok fee)
    (positiveSupply : fee.state.totalSupply ≠ 0)
    (successful : (runTyped st ctx (.mint recipient) transcript).status = .success returndata) :
    LaterMintResult st
      (mintObservation recipient st.cachedReserves transcript.firstWord transcript.ownTail.firstWord)
      fee (runTyped st ctx (.mint recipient) transcript).frame.current.state returndata := by
  exact drive_startTyped_mint_later
    (current := { state := st, logs := [], updates := [] })
    (ctx := ctx) (recipient := recipient)
    (fuel := transcript.work + 2) (transcript := transcript) (returndata := returndata)
    feeAccepted positiveSupply successful

/-- The initial burn observation captures the pair's cached LP balance and two token balances. -/
def burnObservation (recipient : Adr) (st : State) (pair : Adr)
    (balance0 balance1 : B256) : BurnObserved :=
  { locals := { recipient := recipient, reserves := st.cachedReserves, token0 := st.token0, token1 := st.token1 },
    balance0 := balance0,
    balance1 := balance1,
    liquidity := st.balanceOf pair }

/-- Exact burn payout: pays exactly ⌊L·b_i/T⌋ of each token via transfer requests and returns them. -/
def BurnPayoutResult (prior : State) (ctx : Context) (recipient : Adr) (observed : BurnObserved)
    (fee : FeeResult) (returndata : Bytes) (requests : List Request) : Prop :=
  let supply := fee.state.totalSupply
  let amount0 := AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance0.toNat supply.toNat
  let amount1 := AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance1.toNat supply.toNat
  amount0 > 0 ∧ amount1 > 0 ∧
    amount0 < 2 ^ 256 ∧ amount1 < 2 ^ 256 ∧
    observed.liquidity = prior.balanceOf ctx.pair ∧
    requests.filter (fun r => r.site == .burnTransfer0) =
      [requestFor .burnTransfer0 prior.token0 (.transfer recipient (Nat.toB256 amount0))] ∧
    requests.filter (fun r => r.site == .burnTransfer1) =
      [requestFor .burnTransfer1 prior.token1 (.transfer recipient (Nat.toB256 amount1))] ∧
    returndata = encodeWords [Nat.toB256 amount0, Nat.toB256 amount1]

/-- The second final balance query completes the burn driver and returns the exact payout words. -/
theorem drive_burnFinalBalance1_payout {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {balance0 : B256} {owner : Adr} {transcript : Transcript}
    {returndata : Bytes}
    (siteEq : request.site = .burnFinalBalance1) (kind : request.kind = .staticCall)
    (operation : request.operation = .balanceOf owner)
    (successful : (drive fuel (.suspended frame request (.burnFinalBalance1 priced balance0))
      transcript).status = .success returndata) :
    returndata = encodeWords [priced.amount0, priced.amount1] ∧
      (driveRequests fuel (.suspended frame request (.burnFinalBalance1 priced balance0)) transcript).filter
        (fun r => r.site == .burnTransfer0) = [] ∧
      (driveRequests fuel (.suspended frame request (.burnFinalBalance1 priced balance0)) transcript).filter
        (fun r => r.site == .burnTransfer1) = [] := by
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
        have _observedWord := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded] at resumedSuccess reqEq
        have terminal := Frame.finishUpdated_terminal
          (frame.beginResume request)
          balance0 balance1 priced.observed.locals.reserves priced.feeOn
          (some (.burn (frame.beginResume request).context.sender
            priced.amount0 priced.amount1 priced.observed.locals.recipient))
          (encodeWords [priced.amount0, priced.amount1])
        obtain ⟨final, finished, _finalEq⟩ := drive_terminal_success terminal resumedSuccess
        have retEq : returndata = encodeWords [priced.amount0, priced.amount1] :=
          (Frame.finishUpdated_ledger_output finished).2
        have emptyTail := driveRequests_terminal terminal resumedSuccess
        have not0 : ¬((request.site == .burnTransfer0) = true) := by
          rw [siteEq]
          decide
        have not1 : ¬((request.site == .burnTransfer1) = true) := by
          rw [siteEq]
          decide
        refine ⟨retEq, ?_, ?_⟩
        · rw [reqEq, List.filter_cons, ite_eq_right not0, emptyTail, List.filter_nil]
        · rw [reqEq, List.filter_cons, ite_eq_right not1, emptyTail, List.filter_nil]

/-- The first final balance query completes with zero transfer requests and exact return bytes. -/
theorem drive_burnFinalBalance0_payout {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {owner : Adr} {transcript : Transcript}
    {returndata : Bytes} (locked : frame.current.state.unlocked = 0)
    (siteEq : request.site = .burnFinalBalance0) (_kind : request.kind = .staticCall)
    (operation : request.operation = .balanceOf owner)
    (successful : (drive fuel (.suspended frame request (.burnFinalBalance0 priced))
      transcript).status = .success returndata) :
    returndata = encodeWords [priced.amount0, priced.amount1] ∧
      (driveRequests fuel (.suspended frame request (.burnFinalBalance0 priced)) transcript).filter
        (fun r => r.site == .burnTransfer0) = [] ∧
      (driveRequests fuel (.suspended frame request (.burnFinalBalance0 priced)) transcript).filter
        (fun r => r.site == .burnTransfer1) = [] := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, reqEq⟩ := driveRequests_suspended_success successful
    obtain ⟨result', turns', tail', shape', _complete, resumedSuccess, _frameEq⟩ :=
      drive_suspended_success successful
    cases shape.symm.trans shape'
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    let resumed := (frame.settleExternal fuel request result turns).beginResume request
    have resumeLocked : resumed.current.state.unlocked = 0 :=
      (congrArg (fun c => c.2.2.2.2.2) core).trans locked
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
        have _observedWord := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess reqEq
        have tailPayout := drive_burnFinalBalance1_payout rfl rfl rfl resumedSuccess
        have not0 : ¬((request.site == .burnTransfer0) = true) := by
          rw [siteEq]
          decide
        have not1 : ¬((request.site == .burnTransfer1) = true) := by
          rw [siteEq]
          decide
        refine ⟨tailPayout.1, ?_, ?_⟩
        · rw [reqEq, List.filter_cons, ite_eq_right not0, tailPayout.2.1]
        · rw [reqEq, List.filter_cons, ite_eq_right not1, tailPayout.2.2]

/-- The second transfer records its request and returns the exact payout words. -/
theorem drive_burnTransfer1_payout {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {transcript : Transcript}
    {returndata : Bytes} (locked : frame.current.state.unlocked = 0)
    (reqDef : request = requestFor .burnTransfer1 priced.observed.locals.token1
      (.transfer priced.observed.locals.recipient priced.amount1))
    (successful : (drive fuel (.suspended frame request (.burnTransfer1 priced))
      transcript).status = .success returndata) :
    returndata = encodeWords [priced.amount0, priced.amount1] ∧
      (driveRequests fuel (.suspended frame request (.burnTransfer1 priced)) transcript).filter
        (fun r => r.site == .burnTransfer0) = [] ∧
      (driveRequests fuel (.suspended frame request (.burnTransfer1 priced)) transcript).filter
        (fun r => r.site == .burnTransfer1) = [request] := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, reqEq⟩ := driveRequests_suspended_success successful
    obtain ⟨result', turns', tail', shape', _complete, resumedSuccess, _frameEq⟩ :=
      drive_suspended_success successful
    cases shape.symm.trans shape'
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    let resumed := (frame.settleExternal fuel request result turns).beginResume request
    have resumeLocked : resumed.current.state.unlocked = 0 :=
      (congrArg (fun c => c.2.2.2.2.2) core).trans locked
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
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess reqEq
        have tailPayout := drive_burnFinalBalance0_payout resumeLocked rfl rfl rfl resumedSuccess
        have not0 : ¬((request.site == .burnTransfer0) = true) := by
          rw [reqDef]
          intro h; cases h
        have is1 : (request.site == .burnTransfer1) = true := by
          rw [reqDef]
          rfl
        refine ⟨tailPayout.1, ?_, ?_⟩
        · rw [reqEq, List.filter_cons, ite_eq_right not0, tailPayout.2.1]
        · rw [reqEq, List.filter_cons, ite_eq_left is1, tailPayout.2.2]

/-- The first transfer records both requests and returns the exact payout words. -/
theorem drive_burnTransfer0_payout {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {transcript : Transcript}
    {returndata : Bytes} (locked : frame.current.state.unlocked = 0)
    (reqDef : request = requestFor .burnTransfer0 priced.observed.locals.token0
      (.transfer priced.observed.locals.recipient priced.amount0))
    (successful : (drive fuel (.suspended frame request (.burnTransfer0 priced))
      transcript).status = .success returndata) :
    returndata = encodeWords [priced.amount0, priced.amount1] ∧
      (driveRequests fuel (.suspended frame request (.burnTransfer0 priced)) transcript).filter
        (fun r => r.site == .burnTransfer0) = [request] ∧
      (driveRequests fuel (.suspended frame request (.burnTransfer0 priced)) transcript).filter
        (fun r => r.site == .burnTransfer1) =
          [requestFor .burnTransfer1 priced.observed.locals.token1
            (.transfer priced.observed.locals.recipient priced.amount1)] := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, reqEq⟩ := driveRequests_suspended_success successful
    obtain ⟨result', turns', tail', shape', _complete, resumedSuccess, _frameEq⟩ :=
      drive_suspended_success successful
    cases shape.symm.trans shape'
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    let resumed := (frame.settleExternal fuel request result turns).beginResume request
    have resumeLocked : resumed.current.state.unlocked = 0 :=
      (congrArg (fun c => c.2.2.2.2.2) core).trans locked
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
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess reqEq
        have tailPayout := drive_burnTransfer1_payout resumeLocked rfl resumedSuccess
        have is0 : (request.site == .burnTransfer0) = true := by
          rw [reqDef]
          rfl
        have not1 : ¬((request.site == .burnTransfer1) = true) := by
          rw [reqDef]
          intro h; cases h
        refine ⟨tailPayout.1, ?_, ?_⟩
        · rw [reqEq, List.filter_cons, ite_eq_left is0, tailPayout.2.1]
        · rw [reqEq, List.filter_cons, ite_eq_right not1, tailPayout.2.2]

/-- The post-fee burn segment yields the exact calculated payout amounts and requests. -/
theorem Frame.burnAfterFee_driver_payout {fuel : Nat} {frame : Frame}
    {observed : BurnObserved} {fee : FeeResult} {feeTo : Adr} {transcript : Transcript}
    {returndata : Bytes} (locked : frame.current.state.unlocked = 0)
    (feeAccepted : mintFee frame.current.state feeTo observed.locals.reserves.reserve0.val
      observed.locals.reserves.reserve1.val = .ok fee)
    (successful : (drive fuel (frame.burnAfterFee observed fee) transcript).status = .success returndata) :
    let supply := fee.state.totalSupply
    let amount0 := AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance0.toNat supply.toNat
    let amount1 := AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance1.toNat supply.toNat
    amount0 > 0 ∧ amount1 > 0 ∧
      amount0 < 2 ^ 256 ∧ amount1 < 2 ^ 256 ∧
      (driveRequests fuel (frame.burnAfterFee observed fee) transcript).filter
        (fun r => r.site == .burnTransfer0) =
        [requestFor .burnTransfer0 observed.locals.token0 (.transfer observed.locals.recipient (Nat.toB256 amount0))] ∧
      (driveRequests fuel (frame.burnAfterFee observed fee) transcript).filter
        (fun r => r.site == .burnTransfer1) =
        [requestFor .burnTransfer1 observed.locals.token1 (.transfer observed.locals.recipient (Nat.toB256 amount1))] ∧
      returndata = encodeWords [Nat.toB256 amount0, Nat.toB256 amount1] := by
  rw [Frame.burnAfterFee] at successful ⊢
  cases priced : burnAmounts observed.liquidity observed.balance0 observed.balance1 fee.state.totalSupply with
  | error failure =>
    simp only [priced, Frame.fail] at successful
    exact False.elim (drive_failed_not_success fuel _ failure transcript returndata successful)
  | ok amounts =>
    rcases amounts with ⟨amount0, amount1⟩
    simp only [priced] at successful ⊢
    have prices := burnAmounts_spec priced
    by_cases positive : amount0 > 0 ∧ amount1 > 0
    · rw [ite_eq_left positive] at successful ⊢
      cases burned : fee.state.burnLP frame.context.pair observed.liquidity with
      | error failure =>
        simp only [burned, Frame.fail] at successful
        exact False.elim (drive_failed_not_success fuel _ failure transcript returndata successful)
      | ok result =>
        rcases result with ⟨post, events⟩
        simp only [burned, Frame.suspend] at successful ⊢
        let pricedState : BurnPriced :=
          { observed := observed, feeOn := fee.feeOn, feeMinted := fee.minted,
            supply := fee.state.totalSupply, amount0 := Nat.toB256 amount0, amount1 := Nat.toB256 amount1 }
        let transferFrame := (frame.withEvents fee.state fee.events).withEvents post events
        have supplySpec := State.burnLP_supply_unlocked burned
        have feeSpec := mintFee_spec feeAccepted
        have transferLocked : transferFrame.current.state.unlocked = 0 :=
          supplySpec.2.2.trans (feeSpec.2.1.trans locked)
        have payout := drive_burnTransfer0_payout (frame := transferFrame)
          (priced := pricedState) transferLocked rfl successful
        have h0 : AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance0.toNat fee.state.totalSupply.toNat = amount0 := prices.1.symm
        have h1 : AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance1.toNat fee.state.totalSupply.toNat = amount1 := prices.2.1.symm
        dsimp only [pricedState] at payout ⊢
        rw [h0, h1]
        exact ⟨positive.1, positive.2, prices.2.2.1, prices.2.2.2, payout.2.1, payout.2.2, payout.1⟩
    · simp only [ite_eq_right positive, Frame.fail] at successful
      exact False.elim
        (drive_failed_not_success fuel _ (.sourceGuard "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED")
          transcript returndata successful)

/-- The fee query passes through to the payout results without generating transfer requests. -/
theorem drive_burnFee_payout {fuel : Nat} {frame : Frame} {request : Request}
    {observed : BurnObserved} {transcript : Transcript} {returndata : Bytes}
    {fee : FeeResult}
    (locked : frame.current.state.unlocked = 0)
    (siteEq : request.site = .burnFeeTo) (kind : request.kind = .staticCall)
    (operation : request.operation = .feeTo)
    (feeAccepted : mintFee frame.current.state transcript.firstWord.toAdr observed.locals.reserves.reserve0.val
      observed.locals.reserves.reserve1.val = .ok fee)
    (successful : (drive fuel (.suspended frame request (.burnFee observed))
      transcript).status = .success returndata) :
    let supply := fee.state.totalSupply
    let amount0 := AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance0.toNat supply.toNat
    let amount1 := AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance1.toNat supply.toNat
    amount0 > 0 ∧ amount1 > 0 ∧
      amount0 < 2 ^ 256 ∧ amount1 < 2 ^ 256 ∧
      (driveRequests fuel (.suspended frame request (.burnFee observed)) transcript).filter
        (fun r => r.site == .burnTransfer0) =
        [requestFor .burnTransfer0 observed.locals.token0 (.transfer observed.locals.recipient (Nat.toB256 amount0))] ∧
      (driveRequests fuel (.suspended frame request (.burnFee observed)) transcript).filter
        (fun r => r.site == .burnTransfer1) =
        [requestFor .burnTransfer1 observed.locals.token1 (.transfer observed.locals.recipient (Nat.toB256 amount1))] ∧
      returndata = encodeWords [Nat.toB256 amount0, Nat.toB256 amount1] := by
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
      | word value =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | address decodedFeeTo =>
        have recipientEq := decodeExternal_feeTo_address operation decoded
        cases charged : mintFee (frame.beginResume request).current.state decodedFeeTo
            observed.locals.reserves.reserve0.val observed.locals.reserves.reserve1.val with
        | error failure =>
          simp only [resumeSegment, decoded, charged, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _ failure tail returndata resumedSuccess)
        | ok fee' =>
          simp only [resumeSegment, decoded, charged] at resumedSuccess reqEq
          have frameState : (frame.beginResume request).current.state = frame.current.state := rfl
          rw [shape, Transcript.firstWord, ← recipientEq] at feeAccepted
          rw [← frameState, charged] at feeAccepted
          have feeEq : fee' = fee := Except.ok.inj feeAccepted
          subst feeEq
          have resumeLocked : (frame.beginResume request).current.state.unlocked = 0 := locked
          have payout := Frame.burnAfterFee_driver_payout (frame := frame.beginResume request)
            resumeLocked charged resumedSuccess
          have not0 : ¬((request.site == .burnTransfer0) = true) := by
            rw [siteEq]
            decide
          have not1 : ¬((request.site == .burnTransfer1) = true) := by
            rw [siteEq]
            decide
          refine ⟨payout.1, payout.2.1, payout.2.2.1, payout.2.2.2.1, ?_, ?_, payout.2.2.2.2.2.2⟩
          · rw [reqEq, List.filter_cons, ite_eq_right not0, payout.2.2.2.2.1]
          · rw [reqEq, List.filter_cons, ite_eq_right not1, payout.2.2.2.2.2.1]

/-- The second initial balance query passes through to the payout results. -/
theorem drive_burnInitialBalance1_payout {fuel : Nat} {frame : Frame} {request : Request}
    {locals : BurnLocals} {owner : Adr} {balance0 : B256} {transcript : Transcript}
    {returndata : Bytes} {fee : FeeResult}
    (locked : frame.current.state.unlocked = 0)
    (siteEq : request.site = .burnInitialBalance1) (kind : request.kind = .staticCall)
    (operation : request.operation = .balanceOf owner)
    (feeAccepted : mintFee frame.current.state transcript.ownTail.firstWord.toAdr
      locals.reserves.reserve0.val locals.reserves.reserve1.val = .ok fee)
    (successful : (drive fuel (.suspended frame request (.burnInitialBalance1 locals balance0))
      transcript).status = .success returndata) :
    let observed : BurnObserved :=
      { locals := locals, balance0 := balance0, balance1 := transcript.firstWord,
        liquidity := frame.current.state.balanceOf frame.context.pair }
    let supply := fee.state.totalSupply
    let amount0 := AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance0.toNat supply.toNat
    let amount1 := AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance1.toNat supply.toNat
    amount0 > 0 ∧ amount1 > 0 ∧
      amount0 < 2 ^ 256 ∧ amount1 < 2 ^ 256 ∧
      (driveRequests fuel (.suspended frame request (.burnInitialBalance1 locals balance0)) transcript).filter
        (fun r => r.site == .burnTransfer0) =
        [requestFor .burnTransfer0 locals.token0 (.transfer locals.recipient (Nat.toB256 amount0))] ∧
      (driveRequests fuel (.suspended frame request (.burnInitialBalance1 locals balance0)) transcript).filter
        (fun r => r.site == .burnTransfer1) =
        [requestFor .burnTransfer1 locals.token1 (.transfer locals.recipient (Nat.toB256 amount1))] ∧
      returndata = encodeWords [Nat.toB256 amount0, Nat.toB256 amount1] := by
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
        have observedWord := decodeExternal_balance_word operation decoded
        have wordEq : balance1 = transcript.firstWord := by
          rw [shape, Transcript.firstWord]
          exact observedWord
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess reqEq
        rw [wordEq] at resumedSuccess reqEq
        have frameState : (frame.beginResume request).current.state = frame.current.state := rfl
        have feeAccepted' : mintFee (frame.beginResume request).current.state tail.firstWord.toAdr
            locals.reserves.reserve0.val locals.reserves.reserve1.val = .ok fee := by
          rw [frameState]
          simpa only [shape, Transcript.ownTail] using feeAccepted
        have resumeLocked : (frame.beginResume request).current.state.unlocked = 0 := locked
        have payout := drive_burnFee_payout resumeLocked rfl rfl rfl feeAccepted' resumedSuccess
        have not0 : ¬((request.site == .burnTransfer0) = true) := by
          rw [siteEq]
          decide
        have not1 : ¬((request.site == .burnTransfer1) = true) := by
          rw [siteEq]
          decide
        refine ⟨payout.1, payout.2.1, payout.2.2.1, payout.2.2.2.1, ?_, ?_, payout.2.2.2.2.2.2⟩
        · rw [reqEq, List.filter_cons, ite_eq_right not0, payout.2.2.2.2.1]
          rfl
        · rw [reqEq, List.filter_cons, ite_eq_right not1, payout.2.2.2.2.2.1]
          rfl

/-- The first initial balance query passes through to the payout results. -/
theorem drive_burnInitialBalance0_payout {fuel : Nat} {frame : Frame} {request : Request}
    {locals : BurnLocals} {owner : Adr} {transcript : Transcript}
    {returndata : Bytes} {fee : FeeResult}
    (locked : frame.current.state.unlocked = 0)
    (siteEq : request.site = .burnInitialBalance0) (kind : request.kind = .staticCall)
    (operation : request.operation = .balanceOf owner)
    (feeAccepted : mintFee frame.current.state transcript.ownTail.ownTail.firstWord.toAdr
      locals.reserves.reserve0.val locals.reserves.reserve1.val = .ok fee)
    (successful : (drive fuel (.suspended frame request (.burnInitialBalance0 locals))
      transcript).status = .success returndata) :
    let observed : BurnObserved :=
      { locals := locals, balance0 := transcript.firstWord, balance1 := transcript.ownTail.firstWord,
        liquidity := frame.current.state.balanceOf frame.context.pair }
    let supply := fee.state.totalSupply
    let amount0 := AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance0.toNat supply.toNat
    let amount1 := AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance1.toNat supply.toNat
    amount0 > 0 ∧ amount1 > 0 ∧
      amount0 < 2 ^ 256 ∧ amount1 < 2 ^ 256 ∧
      (driveRequests fuel (.suspended frame request (.burnInitialBalance0 locals)) transcript).filter
        (fun r => r.site == .burnTransfer0) =
        [requestFor .burnTransfer0 locals.token0 (.transfer locals.recipient (Nat.toB256 amount0))] ∧
      (driveRequests fuel (.suspended frame request (.burnInitialBalance0 locals)) transcript).filter
        (fun r => r.site == .burnTransfer1) =
        [requestFor .burnTransfer1 locals.token1 (.transfer locals.recipient (Nat.toB256 amount1))] ∧
      returndata = encodeWords [Nat.toB256 amount0, Nat.toB256 amount1] := by
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
        have observedWord := decodeExternal_balance_word operation decoded
        have wordEq : balance0 = transcript.firstWord := by
          rw [shape, Transcript.firstWord]
          exact observedWord
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess reqEq
        rw [wordEq] at resumedSuccess reqEq
        have frameState : (frame.beginResume request).current.state = frame.current.state := rfl
        have feeAccepted' : mintFee (frame.beginResume request).current.state tail.ownTail.firstWord.toAdr
            locals.reserves.reserve0.val locals.reserves.reserve1.val = .ok fee := by
          rw [frameState]
          simpa only [shape, Transcript.ownTail] using feeAccepted
        have resumeLocked : (frame.beginResume request).current.state.unlocked = 0 := locked
        have payout := drive_burnInitialBalance1_payout resumeLocked rfl rfl rfl feeAccepted' resumedSuccess
        have not0 : ¬((request.site == .burnTransfer0) = true) := by
          rw [siteEq]
          decide
        have not1 : ¬((request.site == .burnTransfer1) = true) := by
          rw [siteEq]
          decide
        have tailWord : tail.firstWord = transcript.ownTail.firstWord := by
          rw [shape, Transcript.ownTail]
        have frameBalance : (frame.beginResume request).current.state.balanceOf
            (frame.beginResume request).context.pair =
          frame.current.state.balanceOf frame.context.pair := rfl
        rw [tailWord, frameBalance] at payout
        refine ⟨payout.1, payout.2.1, payout.2.2.1, payout.2.2.2.1, ?_, ?_, payout.2.2.2.2.2.2⟩
        · rw [reqEq, List.filter_cons, ite_eq_right not0, payout.2.2.2.2.1]
        · rw [reqEq, List.filter_cons, ite_eq_right not1, payout.2.2.2.2.2.1]

/-- Starting typed burn establishes the full payout formula and transfer requests. -/
theorem drive_startTyped_burn_payout {fuel : Nat} {current : Checkpoint} {ctx : Context}
    {recipient : Adr} {transcript : Transcript} {returndata : Bytes}
    {fee : FeeResult}
    (feeAccepted : mintFee { current.state with unlocked := 0 }
      transcript.ownTail.ownTail.firstWord.toAdr
      current.state.reserve0.val current.state.reserve1.val = .ok fee)
    (successful : (drive fuel (startTyped current ctx (.burn recipient)) transcript).status =
      .success returndata) :
    BurnPayoutResult current.state ctx recipient
      (burnObservation recipient current.state ctx.pair
        transcript.firstWord transcript.ownTail.firstWord)
      fee returndata
      (driveRequests fuel (startTyped current ctx (.burn recipient)) transcript) := by
  by_cases paid : ctx.value ≠ 0
  · simp only [startTyped, startImmediate, ite_eq_left paid, Frame.fail] at successful
    exact False.elim (drive_failed_not_success fuel _ .emptyRevert transcript returndata successful)
  · by_cases unlocked : current.state.unlocked = 1
    · by_cases staticContext : ctx.isStatic = true
      · simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, Frame.lock,
          Frame.enter, ite_eq_left unlocked, staticContext, ite_true, Frame.fail] at successful
        exact False.elim (drive_failed_not_success fuel _ .staticWrite transcript returndata successful)
      · let lockedFrame : Frame :=
          { Frame.enter current ctx (.burn recipient) with
            current := { current with state := { current.state with unlocked := 0 } } }
        let locals : BurnLocals :=
          { recipient := recipient, reserves := current.state.cachedReserves,
            token0 := current.state.token0, token1 := current.state.token1 }
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
        have suspendedSuccess :
            (drive fuel (.suspended lockedFrame
              (requestFor .burnInitialBalance0 locals.token0 (.balanceOf ctx.pair))
              (.burnInitialBalance0 locals)) transcript).status = .success returndata := by
          simpa only [stage, Frame.suspend] using successful
        have feeAccepted' : mintFee lockedFrame.current.state transcript.ownTail.ownTail.firstWord.toAdr
            locals.reserves.reserve0.val locals.reserves.reserve1.val = .ok fee := by
          exact feeAccepted
        have payout := drive_burnInitialBalance0_payout (frame := lockedFrame)
          (locals := locals) rfl rfl rfl rfl feeAccepted' suspendedSuccess
        rw [stage, Frame.suspend]
        rw [BurnPayoutResult]
        dsimp only [burnObservation]
        have frameBalance : lockedFrame.current.state.balanceOf lockedFrame.context.pair =
            current.state.balanceOf ctx.pair := rfl
        have frameToken0 : locals.token0 = current.state.token0 := rfl
        have frameToken1 : locals.token1 = current.state.token1 := rfl
        have frameRecipient : locals.recipient = recipient := rfl
        rw [frameBalance, frameToken0, frameToken1, frameRecipient] at payout
        refine ⟨payout.1, payout.2.1, payout.2.2.1, payout.2.2.2.1, rfl, payout.2.2.2.2.1, payout.2.2.2.2.2.1, payout.2.2.2.2.2.2⟩
    · have enteredLocked : ¬(Frame.enter current ctx (.burn recipient)).current.state.unlocked = 1 :=
        unlocked
      have closed : (Frame.enter current ctx (.burn recipient)).lock =
          .error (.sourceGuard "UniswapV2: LOCKED") := by
        rw [Frame.lock, ite_eq_right enteredLocked]
      simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, closed, Frame.fail] at successful
      exact False.elim (drive_failed_not_success fuel _
        (.sourceGuard "UniswapV2: LOCKED") transcript returndata successful)

/-- A successful burn pays exactly ⌊L·b_i/T⌋ of each token via transfer requests and returns them. -/
theorem runTyped_burn_payout {st : State} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {returndata : Bytes}
    {fee : FeeResult}
    (feeAccepted : mintFee { st with unlocked := 0 }
      transcript.ownTail.ownTail.firstWord.toAdr
      st.reserve0.val st.reserve1.val = .ok fee)
    (successful : (runTyped st ctx (.burn recipient) transcript).status = .success returndata) :
    BurnPayoutResult st ctx recipient
      (burnObservation recipient st ctx.pair transcript.firstWord transcript.ownTail.firstWord)
      fee returndata (runTypedRequests st ctx (.burn recipient) transcript) := by
  exact drive_startTyped_burn_payout
    (current := { state := st, logs := [], updates := [] })
    (ctx := ctx) (recipient := recipient)
    (fuel := transcript.work + 2) (transcript := transcript) (returndata := returndata)
    feeAccepted successful

end Blanc.Lift.UniswapV2Pair
