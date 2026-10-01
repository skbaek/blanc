import Blanc.Lift.UniswapV2Pair.Execution

/-! Successful checked-helper laws; frame/bytecode closure is separate. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Successful later-mint pricing consumes the exact minimum-of-floors share law. -/
theorem mintAmount_product {amount0 amount1 supply : B256} {reserve0 reserve1 liquidity : Nat}
    (positiveSupply : supply ≠ 0)
    (accepted : mintAmount amount0 amount1 supply reserve0 reserve1 = .ok liquidity) :
    reserve0 * reserve1 * (supply.toNat + liquidity) ^ 2 ≤
      (reserve0 + amount0.toNat) * (reserve1 + amount1.toNat) * supply.toNat ^ 2 := by
  rw [mintAmount, ite_eq_right positiveSupply] at accepted
  by_cases product0 : amount0.toNat * supply.toNat < 2 ^ 256
  · rw [ite_eq_left product0] at accepted
    by_cases zero0 : reserve0 = 0
    · rw [ite_eq_left zero0] at accepted
      cases accepted
    · rw [ite_eq_right zero0] at accepted
      by_cases product1 : amount1.toNat * supply.toNat < 2 ^ 256
      · rw [ite_eq_left product1] at accepted
        by_cases zero1 : reserve1 = 0
        · rw [ite_eq_left zero1] at accepted
          cases accepted
        · rw [ite_eq_right zero1] at accepted
          rw [← Except.ok.inj accepted]
          exact AMMArithmetic.mint_product_bound reserve0 reserve1 amount0.toNat
            amount1.toNat supply.toNat
      · rw [ite_eq_right product1] at accepted
        cases accepted
  · rw [ite_eq_right product0] at accepted
    cases accepted

/-- Successful burn floors imply the share law under precisely transfer-aware backing. -/
theorem burnAmounts_product {liquidity balance0 balance1 supply : B256}
    {reserve0 reserve1 final0 final1 amount0 amount1 : Nat}
    (accepted : burnAmounts liquidity balance0 balance1 supply = .ok (amount0, amount1))
    (backing0 : reserve0 ≤ balance0.toNat) (backing1 : reserve1 ≤ balance1.toNat)
    (covered : liquidity.toNat ≤ supply.toNat)
    (debit0 : balance0.toNat ≤ final0 + amount0)
    (debit1 : balance1.toNat ≤ final1 + amount1) :
    reserve0 * reserve1 * (supply.toNat - liquidity.toNat) ^ 2 ≤
      final0 * final1 * supply.toNat ^ 2 := by
  rw [burnAmounts] at accepted
  by_cases product0 : liquidity.toNat * balance0.toNat < 2 ^ 256
  · rw [ite_eq_left product0] at accepted
    by_cases zeroSupply : supply = 0
    · rw [ite_eq_left zeroSupply] at accepted
      cases accepted
    · rw [ite_eq_right zeroSupply] at accepted
      by_cases product1 : liquidity.toNat * balance1.toNat < 2 ^ 256
      · rw [ite_eq_left product1] at accepted
        have payout0 : AMMArithmetic.burnPayment liquidity.toNat balance0.toNat supply.toNat = amount0 :=
          congrArg Prod.fst (Except.ok.inj accepted)
        have payout1 : AMMArithmetic.burnPayment liquidity.toNat balance1.toNat supply.toNat = amount1 :=
          congrArg Prod.snd (Except.ok.inj accepted)
        apply AMMArithmetic.burn_product_bound backing0 backing1 covered
        · rw [payout0]
          exact debit0
        · rw [payout1]
          exact debit1
      · rw [ite_eq_right product1] at accepted
        cases accepted
  · rw [ite_eq_right product0] at accepted
    cases accepted

/-- The accepted checked adjusted-product guard implies growth without an answer premise. -/
theorem swapCheck_product {balance0 balance1 : B256} {amount0In amount1In reserve0 reserve1 : Nat}
    (accepted : swapCheck balance0 balance1 amount0In amount1In reserve0 reserve1 = .ok ()) :
    reserve0 * reserve1 ≤ balance0.toNat * balance1.toNat := by
  rw [swapCheck] at accepted
  by_cases positiveInput : amount0In > 0 ∨ amount1In > 0
  · rw [ite_eq_left positiveInput] at accepted
    by_cases products0 : balance0.toNat * 1000 < 2 ^ 256 ∧ amount0In * 3 < 2 ^ 256
    · rw [ite_eq_left products0] at accepted
      by_cases covered0 : amount0In * 3 ≤ balance0.toNat * 1000
      · rw [ite_eq_left covered0] at accepted
        by_cases products1 : balance1.toNat * 1000 < 2 ^ 256 ∧ amount1In * 3 < 2 ^ 256
        · rw [ite_eq_left products1] at accepted
          by_cases covered1 : amount1In * 3 ≤ balance1.toNat * 1000
          · rw [ite_eq_left covered1] at accepted
            by_cases product : (balance0.toNat * 1000 - amount0In * 3) *
                (balance1.toNat * 1000 - amount1In * 3) < 2 ^ 256
            · rw [ite_eq_left product] at accepted
              by_cases invariant : reserve0 * reserve1 * 1000 ^ 2 ≤
                  (balance0.toNat * 1000 - amount0In * 3) *
                    (balance1.toNat * 1000 - amount1In * 3)
              · apply AMMArithmetic.swap_product_bound (scale := 1000)
                    (adjusted0 := balance0.toNat * 1000 - amount0In * 3)
                    (adjusted1 := balance1.toNat * 1000 - amount1In * 3)
                · exact Nat.zero_lt_succ 999
                · simpa only [Nat.mul_comm] using
                    Nat.sub_le (balance0.toNat * 1000) (amount0In * 3)
                · simpa only [Nat.mul_comm] using
                    Nat.sub_le (balance1.toNat * 1000) (amount1In * 3)
                · simpa only [Nat.mul_comm] using invariant
              · rw [ite_eq_right invariant] at accepted
                cases accepted
            · rw [ite_eq_right product] at accepted
              cases accepted
          · rw [ite_eq_right covered1] at accepted
            cases accepted
        · rw [ite_eq_right products1] at accepted
          cases accepted
      · rw [ite_eq_right covered0] at accepted
        cases accepted
    · rw [ite_eq_right products0] at accepted
      cases accepted
  · rw [ite_eq_right positiveInput] at accepted
    cases accepted

/-- A terminal owned segment has no pending external observation. -/
def SegmentResult.Terminal : SegmentResult → Prop
  | .finished _ _ | .failed _ _ => True
  | .suspended _ _ _ => False

/-- The static lock attempt always fails before changing storage. -/
theorem Frame.lock_static {frame : Frame} (staticContext : frame.context.isStatic = true) :
    frame.lock = .error (if frame.current.state.unlocked = 1 then Failure.staticWrite
      else .sourceGuard "UniswapV2: LOCKED") := by
  rw [Frame.lock, staticContext]
  by_cases unlocked : frame.current.state.unlocked = 1
  · simp only [ite_eq_left unlocked, ite_true]
  · simp only [ite_eq_right unlocked]

/-- Static typed entries neither suspend nor change any part of the checkpoint. -/
theorem startTyped_static {current : Checkpoint} {ctx : Context} (entry : Entry)
    (staticContext : ctx.isStatic = true) :
    (startTyped current ctx entry).Terminal ∧
      (startTyped current ctx entry).frame.current = current := by
  by_cases paid : ctx.value ≠ 0
  · simp only [startTyped, startImmediate, ite_eq_left paid, Frame.enter, Frame.fail,
      SegmentResult.Terminal, SegmentResult.frame, and_self]
  · cases entry <;>
      simp only [startTyped, startImmediate, getterResult, ite_eq_right paid,
        State.approveLP, State.transferLP, State.transferFromLP, Frame.enter,
        Frame.lock_static, staticContext, ite_true, Frame.finishLP,
        Frame.fail, Frame.finish, SegmentResult.Terminal, SegmentResult.frame,
        and_self]
    case transfer recipient value =>
      by_cases covered : value ≤ current.state.balanceOf ctx.sender
      · simp only [ite_eq_left covered, and_self]
      · simp only [ite_eq_right covered, and_self]
    case transferFrom source recipient value =>
      by_cases unlimited : current.state.allowance source ctx.sender = B256.max
      · by_cases covered : value ≤ current.state.balanceOf source
        · simp only [ite_eq_left unlimited, ite_eq_left covered, and_self]
        · simp only [ite_eq_left unlimited, ite_eq_right covered, and_self]
      · by_cases covered : value ≤ current.state.allowance source ctx.sender
        · simp only [ite_eq_right unlimited, ite_eq_left covered, and_self]
        · simp only [ite_eq_right unlimited, ite_eq_right covered, and_self]
    case permit owner spender value deadline v r s =>
      by_cases timely : ctx.timestamp ≤ deadline
      · simp only [ite_eq_left timely, and_self]
      · simp only [ite_eq_right timely, and_self]
    case «initialize» token0 token1 =>
      by_cases authorized : ctx.sender = current.state.factory
      · simp only [ite_eq_left authorized, and_self]
      · simp only [ite_eq_right authorized, and_self]

/-- A terminal segment preserves its checkpoint through every driver fuel choice. -/
theorem drive_terminal_current (fuel : Nat) (segment : SegmentResult) (transcript : Transcript)
    (terminal : segment.Terminal) :
    (drive fuel segment transcript).frame.current = segment.frame.current := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases segment with
    | finished frame returndata => rfl
    | failed frame failure => cases failure <;> rfl
    | suspended frame request continuation => cases terminal

/-- The driver retains the whole checkpoint of every static typed call. -/
theorem drive_static_current {current : Checkpoint} {ctx : Context} (entry : Entry)
    (staticContext : ctx.isStatic = true) (fuel : Nat) (transcript : Transcript) :
    (drive fuel (startTyped current ctx entry) transcript).frame.current = current := by
  have start := startTyped_static (current := current) entry staticContext
  exact (drive_terminal_current fuel (startTyped current ctx entry) transcript start.1).trans start.2

/-- Static external execution preserves the full checkpoint across every nested turn. -/
theorem driveTurns_static_frame (fuel : Nat) (frame : Frame) (request : Request)
    (turn : Nat) (turns : Transcript) (staticExternal : externalStatic frame request = true) :
    (driveTurns fuel frame request turn turns).frame = frame := by
  induction fuel generalizing frame turn turns with
  | zero => rfl
  | succ fuel ih =>
    cases turns with
    | done => rfl
    | next result children tail => rfl
    | foreignLog emitter topics data tail =>
      simp only [driveTurns, staticExternal, ite_true]
    | invoke sender value isStatic entry transcript tail =>
      have childStatic :
          (childContext frame request turn sender value isStatic).isStatic = true := by
        change (externalStatic frame request || isStatic) = true
        rw [staticExternal]
        rfl
      have childCurrent := drive_static_current (current := frame.current) entry
        childStatic fuel transcript
      rw [driveTurns]
      cases childStatus : (drive fuel
          (startTyped frame.current (childContext frame request turn sender value isStatic) entry)
          transcript).status with
      | incomplete => rfl
      | success returndata =>
        simpa only [childCurrent] using ih frame (turn + 1) tail staticExternal
      | failed failure =>
        simpa only [childCurrent] using ih frame (turn + 1) tail staticExternal

/-- Static external execution cannot change storage, logs, or oracle receipts. -/
theorem driveTurns_static_current (fuel : Nat) (frame : Frame) (request : Request)
    (turn : Nat) (turns : Transcript) (staticExternal : externalStatic frame request = true) :
    (driveTurns fuel frame request turn turns).frame.current = frame.current := by
  exact congrArg Frame.current (driveTurns_static_frame fuel frame request turn turns staticExternal)

/-- The liquidity and oracle fields protected while an invocation holds the lock. -/
def State.economicCore (st : State) :
    B256 × (Fin (2 ^ 112) × Fin (2 ^ 112)) × UInt32 × (B256 × B256) × B256 × B256 :=
  (st.totalSupply, (st.reserve0, st.reserve1), st.blockTimestampLast,
    (st.price0CumulativeLast, st.price1CumulativeLast), st.kLast, st.unlocked)

/-- Recovery either changes only allowance or restores the invocation checkpoint. -/
theorem resumeSegment_permit_core (prior : Frame) (request : Request)
    (owner spender : Adr) (value : B256) (result : ExternalResult)
    (checkpointCore : prior.checkpoint.state.economicCore = prior.current.state.economicCore) :
    (resumeSegment prior request (.permitRecovery owner spender value) result).Terminal ∧
      (resumeSegment prior request (.permitRecovery owner spender value) result).frame.current.state.economicCore =
        prior.current.state.economicCore := by
  cases decoded : decodeExternal request result with
  | error failure =>
    simpa only [resumeSegment, decoded, Frame.beginResume, Frame.fail, SegmentResult.frame, SegmentResult.Terminal] using And.intro True.intro checkpointCore
  | ok decodedResult =>
    cases decodedResult with
    | word recovered =>
      simpa only [resumeSegment, decoded, Frame.beginResume, Frame.fail, SegmentResult.frame, SegmentResult.Terminal] using And.intro True.intro checkpointCore
    | unit =>
      simpa only [resumeSegment, decoded, Frame.beginResume, Frame.fail, SegmentResult.frame, SegmentResult.Terminal] using And.intro True.intro checkpointCore
    | address recovered =>
      by_cases signed : recovered ≠ 0 ∧ recovered = owner
      · by_cases staticContext : prior.context.isStatic = true
        · simpa only [resumeSegment, decoded, ite_eq_left signed, Frame.beginResume,
            State.approveLP, staticContext, ite_true, Frame.finishLP, Frame.fail,
            SegmentResult.frame, SegmentResult.Terminal] using And.intro True.intro checkpointCore
        · simp only [resumeSegment, decoded, ite_eq_left signed, Frame.beginResume,
            State.approveLP, staticContext, Frame.finishLP, Frame.withEvents,
            Frame.finish, SegmentResult.frame, State.economicCore, SegmentResult.Terminal]
          exact ⟨True.intro, rfl⟩
      · simpa only [resumeSegment, decoded, ite_eq_right signed, Frame.beginResume,
          Frame.fail, SegmentResult.frame, SegmentResult.Terminal] using And.intro True.intro checkpointCore

/-- A permit recovery call cannot change the protected liquidity/oracle fields. -/
theorem drive_permit_core (fuel : Nat) (prior : Frame) (request : Request)
    (owner spender : Adr) (value : B256) (transcript : Transcript)
    (staticExternal : externalStatic prior request = true)
    (checkpointCore : prior.checkpoint.state.economicCore = prior.current.state.economicCore) :
    (drive fuel (.suspended prior request (.permitRecovery owner spender value))
      transcript).frame.current.state.economicCore = prior.current.state.economicCore := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases transcript with
    | done => rfl
    | foreignLog emitter topics data tail => rfl
    | invoke sender callValue isStatic entry child tail => rfl
    | next result turns tail =>
      have resumed := resumeSegment_permit_core prior request owner spender value result checkpointCore
      have resumedCore :
          (drive fuel (resumeSegment prior request (.permitRecovery owner spender value) result)
            tail).frame.current.state.economicCore = prior.current.state.economicCore :=
        (congrArg (fun current : Checkpoint => current.state.economicCore)
          (drive_terminal_current fuel
            (resumeSegment prior request (.permitRecovery owner spender value) result) tail resumed.1)).trans resumed.2
      have staticFrame := driveTurns_static_frame fuel prior request 0 turns staticExternal
      rw [drive]
      cases noCode : request.requiresCode && !result.codeExists with
      | true => exact resumedCore
      | false =>
        dsimp only
        cases complete : (driveTurns fuel prior request 0 turns).complete with
        | false =>
          rw [staticFrame]
          rfl
        | true =>
          rw [staticFrame]
          cases result.success <;> exact resumedCore

/-- Approval changes only the allowance map on success. -/
theorem State.approveLP_core {st : State} {ctx : Context} {owner spender : Adr}
    {value : B256} {post : State} {events : List Event}
    (accepted : st.approveLP ctx owner spender value = .ok (post, events)) :
    post.economicCore = st.economicCore := by
  rw [State.approveLP] at accepted
  cases staticContext : ctx.isStatic with
  | true =>
    rw [staticContext] at accepted
    cases accepted
  | false =>
    rw [staticContext] at accepted
    have postState := congrArg Prod.fst (Except.ok.inj accepted)
    dsimp only at postState
    rw [← postState]
    rfl

/-- LP transfer changes only balances on success, including aliased accounts. -/
theorem State.transferLP_core {st : State} {ctx : Context} {source recipient : Adr}
    {value : B256} {post : State} {events : List Event}
    (accepted : st.transferLP ctx source recipient value = .ok (post, events)) :
    post.economicCore = st.economicCore := by
  rw [State.transferLP] at accepted
  by_cases covered : value ≤ st.balanceOf source
  · rw [ite_eq_left covered] at accepted
    cases staticContext : ctx.isStatic with
    | true =>
      rw [staticContext] at accepted
      cases accepted
    | false =>
      rw [staticContext] at accepted
      dsimp only at accepted
      by_cases credit : (Blanc.ledgerDebit st.balanceOf source value recipient).toNat + value.toNat < 2 ^ 256
      · rw [ite_eq_left credit] at accepted
        have postState := congrArg Prod.fst (Except.ok.inj accepted)
        dsimp only at postState
        rw [← postState]
        rfl
      · rw [ite_eq_right credit] at accepted
        cases accepted
  · rw [ite_eq_right covered] at accepted
    cases accepted

/-- Finite allowance debit and the maximum sentinel both retain the economic core. -/
theorem State.transferFromLP_core {st : State} {ctx : Context} {source recipient : Adr}
    {value : B256} {post : State} {events : List Event}
    (accepted : st.transferFromLP ctx source recipient value = .ok (post, events)) :
    post.economicCore = st.economicCore := by
  rw [State.transferFromLP] at accepted
  by_cases unlimited : st.allowance source ctx.sender = B256.max
  · rw [ite_eq_left unlimited] at accepted
    exact State.transferLP_core accepted
  · rw [ite_eq_right unlimited] at accepted
    by_cases covered : value ≤ st.allowance source ctx.sender
    · rw [ite_eq_left covered] at accepted
      cases staticContext : ctx.isStatic with
      | true =>
        rw [staticContext] at accepted
        cases accepted
      | false =>
        rw [staticContext] at accepted
        let reduced : State := { st with allowance := Function.update st.allowance source (Function.update (st.allowance source) ctx.sender (st.allowance source ctx.sender - value)) }
        exact State.transferLP_core (st := reduced) accepted
    · rw [ite_eq_right covered] at accepted
      cases accepted

/-- Successful LP effects preserve the core; failed effects restore its checkpoint anchor. -/
theorem Frame.finishLP_core (frame : Frame) (result : Except Failure (State × List Event))
    (returndata : Bytes)
    (checkpointCore : frame.checkpoint.state.economicCore = frame.current.state.economicCore)
    (successfulCore : ∀ post events, result = .ok (post, events) →
      post.economicCore = frame.current.state.economicCore) :
    (frame.finishLP result returndata).Terminal ∧
      (frame.finishLP result returndata).frame.current.state.economicCore = frame.current.state.economicCore := by
  cases result with
  | error failure => exact ⟨True.intro, checkpointCore⟩
  | ok postEvents =>
    rcases postEvents with ⟨post, events⟩
    exact ⟨True.intro, successfulCore post events rfl⟩

/-- Every immediate typed entry preserves the liquidity and oracle core. -/
theorem startImmediate_core {current : Checkpoint} {ctx : Context} (entry : Entry)
    {result : SegmentResult} (immediate : startImmediate current ctx entry = some result) :
    result.Terminal ∧ result.frame.current.state.economicCore = current.state.economicCore := by
  rw [startImmediate] at immediate
  by_cases paid : ctx.value ≠ 0
  · rw [ite_eq_left paid] at immediate
    rw [← Option.some.inj immediate]
    exact ⟨True.intro, rfl⟩
  · rw [ite_eq_right paid] at immediate
    cases getter : getterResult current.state entry with
    | some returndata =>
      rw [getter] at immediate
      rw [← Option.some.inj immediate]
      exact ⟨True.intro, rfl⟩
    | none =>
      rw [getter] at immediate
      cases entry
      case approve spender value =>
        rw [← Option.some.inj immediate]
        apply Frame.finishLP_core _ _ _ rfl
        intro post events accepted
        exact State.approveLP_core accepted
      case transfer recipient value =>
        rw [← Option.some.inj immediate]
        apply Frame.finishLP_core _ _ _ rfl
        intro post events accepted
        exact State.transferLP_core accepted
      case transferFrom source recipient value =>
        rw [← Option.some.inj immediate]
        apply Frame.finishLP_core _ _ _ rfl
        intro post events accepted
        exact State.transferFromLP_core accepted
      case «initialize» token0 token1 =>
        dsimp only at immediate
        by_cases authorized : ctx.sender = current.state.factory
        · rw [ite_eq_left authorized] at immediate
          cases staticContext : ctx.isStatic with
          | true =>
            rw [staticContext] at immediate
            rw [← Option.some.inj immediate]
            exact ⟨True.intro, rfl⟩
          | false =>
            rw [staticContext] at immediate
            rw [← Option.some.inj immediate]
            exact ⟨True.intro, rfl⟩
        · rw [ite_eq_right authorized] at immediate
          rw [← Option.some.inj immediate]
          exact ⟨True.intro, rfl⟩
      all_goals cases immediate

/-- Calls entered while the Pair is locked preserve the liquidity and oracle core. -/
theorem drive_locked_core {current : Checkpoint} {ctx : Context} (entry : Entry)
    (fuel : Nat) (transcript : Transcript) (locked : current.state.unlocked = 0) :
    (drive fuel (startTyped current ctx entry) transcript).frame.current.state.economicCore =
      current.state.economicCore := by
  have terminalCore (segment : SegmentResult)
      (laws : segment.Terminal ∧ segment.frame.current.state.economicCore = current.state.economicCore) :
      (drive fuel segment transcript).frame.current.state.economicCore = current.state.economicCore :=
    (congrArg (fun checkpoint : Checkpoint => checkpoint.state.economicCore)
      (drive_terminal_current fuel segment transcript laws.1)).trans laws.2
  cases immediate : startImmediate current ctx entry with
  | some result =>
    rw [startTyped, immediate]
    exact terminalCore result (startImmediate_core entry immediate)
  | none =>
    have notUnlocked : current.state.unlocked ≠ 1 := by
      intro opened
      have impossible : (0 : Nat) = 1 := congrArg B256.toNat (locked.symm.trans opened)
      cases impossible
    rw [startTyped, immediate]
    cases entry
    case permit owner spender value deadline v r s =>
      dsimp only
      by_cases timely : ctx.timestamp ≤ deadline
      · rw [ite_eq_left timely]
        cases staticContext : ctx.isStatic with
        | true =>
          exact terminalCore _ ⟨True.intro, rfl⟩
        | false =>
          apply drive_permit_core
          · change (ctx.isStatic || true) = true
            rw [staticContext]
            rfl
          · rfl
      · rw [ite_eq_right timely]
        exact terminalCore _ ⟨True.intro, rfl⟩
    all_goals
      apply terminalCore
      simp only [Frame.lock, Frame.enter, notUnlocked, ite_false, Frame.fail,
        SegmentResult.Terminal, SegmentResult.frame, and_self]

/-- Transfer/callback turns retain the locked parent's supply, reserves and oracle core. -/
theorem driveTurns_locked_core (fuel : Nat) (frame : Frame) (request : Request)
    (turn : Nat) (turns : Transcript) (locked : frame.current.state.unlocked = 0) :
    (driveTurns fuel frame request turn turns).frame.current.state.economicCore =
      frame.current.state.economicCore := by
  induction fuel generalizing frame turn turns with
  | zero => rfl
  | succ fuel ih =>
    cases turns with
    | done => rfl
    | next result children tail => rfl
    | foreignLog emitter topics data tail =>
      rw [driveTurns]
      cases staticExternal : externalStatic frame request with
      | true => rfl
      | false => exact ih _ (turn + 1) tail locked
    | invoke sender value isStatic entry transcript tail =>
      have childCore := drive_locked_core (current := frame.current)
        (ctx := childContext frame request turn sender value isStatic) entry fuel transcript locked
      have childLocked :
          (drive fuel (startTyped frame.current (childContext frame request turn sender value isStatic) entry)
            transcript).frame.current.state.unlocked = 0 :=
        (congrArg (fun core => core.2.2.2.2.2) childCore).trans locked
      let settled : Frame := { frame with current :=
        (drive fuel (startTyped frame.current (childContext frame request turn sender value isStatic) entry)
          transcript).frame.current }
      have tailCore := ih settled (turn + 1) tail childLocked
      rw [driveTurns]
      cases childStatus : (drive fuel
          (startTyped frame.current (childContext frame request turn sender value isStatic) entry)
          transcript).status with
      | incomplete => rfl
      | success returndata => exact tailCore.trans childCore
      | failed failure => exact tailCore.trans childCore

end Blanc.Lift.UniswapV2Pair
