import Blanc.Lift.UniswapV2Pair.Execution

/-! Successful checked-helper laws; frame/bytecode closure is separate. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- A successful later mint has the exact floor formula and a bounded LP amount. -/
theorem mintAmount_later_spec {amount0 amount1 supply : B256}
    {reserve0 reserve1 liquidity : Nat} (positiveSupply : supply ≠ 0)
    (accepted : mintAmount amount0 amount1 supply reserve0 reserve1 = .ok liquidity) :
    liquidity = AMMArithmetic.mintLiquidity amount0.toNat amount1.toNat supply.toNat reserve0 reserve1 ∧
      liquidity < 2 ^ 256 := by
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
          refine ⟨(Except.ok.inj accepted).symm, ?_⟩
          rw [← Except.ok.inj accepted]
          change min (amount0.toNat * supply.toNat / reserve0)
            (amount1.toNat * supply.toNat / reserve1) < 2 ^ 256
          exact Nat.lt_of_le_of_lt ((min_le_left _ _).trans (Nat.div_le_self _ _)) product0
      · rw [ite_eq_right product1] at accepted
        cases accepted
  · rw [ite_eq_right product0] at accepted
    cases accepted

/-- Successful later-mint pricing consumes the exact minimum-of-floors share law. -/
theorem mintAmount_product {amount0 amount1 supply : B256} {reserve0 reserve1 liquidity : Nat}
    (positiveSupply : supply ≠ 0)
    (accepted : mintAmount amount0 amount1 supply reserve0 reserve1 = .ok liquidity) :
    reserve0 * reserve1 * (supply.toNat + liquidity) ^ 2 ≤
      (reserve0 + amount0.toNat) * (reserve1 + amount1.toNat) * supply.toNat ^ 2 := by
  rw [(mintAmount_later_spec positiveSupply accepted).1]
  exact AMMArithmetic.mint_product_bound reserve0 reserve1 amount0.toNat amount1.toNat supply.toNat

/-- Accepted burn prices are both exact floors and fit the transfer words. -/
theorem burnAmounts_spec {liquidity balance0 balance1 supply : B256} {amount0 amount1 : Nat}
    (accepted : burnAmounts liquidity balance0 balance1 supply = .ok (amount0, amount1)) :
    amount0 = AMMArithmetic.burnPayment liquidity.toNat balance0.toNat supply.toNat ∧
      amount1 = AMMArithmetic.burnPayment liquidity.toNat balance1.toNat supply.toNat ∧
      amount0 < 2 ^ 256 ∧ amount1 < 2 ^ 256 := by
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
        refine ⟨payout0.symm, payout1.symm, ?_, ?_⟩
        · rw [← payout0]
          change liquidity.toNat * balance0.toNat / supply.toNat < 2 ^ 256
          exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) product0
        · rw [← payout1]
          change liquidity.toNat * balance1.toNat / supply.toNat < 2 ^ 256
          exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) product1
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
  have prices := burnAmounts_spec accepted
  apply AMMArithmetic.burn_product_bound backing0 backing1 covered
  · rw [← prices.1]
    exact debit0
  · rw [← prices.2.1]
    exact debit1

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


/-- Checked LP minting adds exact supply while preserving the held lock. -/
theorem State.mintLP_supply_unlocked {st post : State} {recipient : Adr} {value : B256}
    {events : List Event} (accepted : st.mintLP recipient value = .ok (post, events)) :
    post.totalSupply.toNat = st.totalSupply.toNat + value.toNat ∧ post.unlocked = st.unlocked := by
  rw [State.mintLP] at accepted
  by_cases supplyBound : st.totalSupply.toNat + value.toNat < 2 ^ 256
  · rw [ite_eq_left supplyBound] at accepted
    by_cases balanceBound : (st.balanceOf recipient).toNat + value.toNat < 2 ^ 256
    · rw [ite_eq_left balanceBound] at accepted
      have supplyEq := congrArg (fun result : State × List Event => result.1.totalSupply.toNat)
        (Except.ok.inj accepted)
      have lockEq := congrArg (fun result : State × List Event => result.1.unlocked)
        (Except.ok.inj accepted)
      exact ⟨supplyEq.symm.trans (B256.toNat_add_eq_of_nof st.totalSupply value supplyBound),
        lockEq.symm⟩
    · rw [ite_eq_right balanceBound] at accepted
      cases accepted
  · rw [ite_eq_right supplyBound] at accepted
    cases accepted

/-- Successful LP minting exposes its exact checked supply increase. -/
theorem State.mintLP_supply {st post : State} {recipient : Adr} {value : B256}
    {events : List Event} (accepted : st.mintLP recipient value = .ok (post, events)) :
    post.totalSupply.toNat = st.totalSupply.toNat + value.toNat := by
  exact (State.mintLP_supply_unlocked accepted).1

/-- Checked LP burning covers its debit, subtracts exact supply and preserves the lock. -/
theorem State.burnLP_supply_unlocked {st post : State} {source : Adr} {value : B256}
    {events : List Event} (accepted : st.burnLP source value = .ok (post, events)) :
    value.toNat ≤ st.totalSupply.toNat ∧
      post.totalSupply.toNat = st.totalSupply.toNat - value.toNat ∧ post.unlocked = st.unlocked := by
  rw [State.burnLP] at accepted
  by_cases balanceCovered : value ≤ st.balanceOf source
  · rw [ite_eq_left balanceCovered] at accepted
    by_cases supplyCovered : value ≤ st.totalSupply
    · rw [ite_eq_left supplyCovered] at accepted
      have supplyEq := congrArg (fun result : State × List Event => result.1.totalSupply.toNat)
        (Except.ok.inj accepted)
      have lockEq := congrArg (fun result : State × List Event => result.1.unlocked)
        (Except.ok.inj accepted)
      exact ⟨B256.toNat_le_toNat supplyCovered,
        supplyEq.symm.trans (B256.toNat_sub_eq_of_le st.totalSupply value supplyCovered), lockEq.symm⟩
    · rw [ite_eq_right supplyCovered] at accepted
      cases accepted
  · rw [ite_eq_right balanceCovered] at accepted
    cases accepted


/-- Successful LP burning exposes cover and the exact checked supply decrease. -/
theorem State.burnLP_supply {st post : State} {source : Adr} {value : B256}
    {events : List Event} (accepted : st.burnLP source value = .ok (post, events)) :
    value.toNat ≤ st.totalSupply.toNat ∧
      post.totalSupply.toNat = st.totalSupply.toNat - value.toNat := by
  have spec := State.burnLP_supply_unlocked accepted
  exact ⟨spec.1, spec.2.1⟩

/-- The exact separately-floored-root integer fee, with source fee-off and kLast branches. -/
def feeAmount (st : State) (feeTo : Adr) (reserve0 reserve1 : Nat) : Nat :=
  if feeTo = 0 ∨ st.kLast = 0 then 0
  else if Nat.sqrt st.kLast.toNat < Nat.sqrt (reserve0 * reserve1) then
    st.totalSupply.toNat * (Nat.sqrt (reserve0 * reserve1) - Nat.sqrt st.kLast.toNat) /
      (Nat.sqrt (reserve0 * reserve1) * 5 + Nat.sqrt st.kLast.toNat)
  else 0

/-- Successful fee minting fixes supply, retains the lock and realizes the exact fee formula. -/
theorem mintFee_spec {st : State} {feeTo : Adr} {reserve0 reserve1 : Nat}
    {fee : FeeResult} (accepted : mintFee st feeTo reserve0 reserve1 = .ok fee) :
    fee.state.totalSupply.toNat = st.totalSupply.toNat + fee.minted ∧
      fee.state.unlocked = st.unlocked ∧ fee.minted = feeAmount st feeTo reserve0 reserve1 := by
  rw [mintFee] at accepted
  by_cases feeOff : feeTo = 0
  · rw [ite_eq_left feeOff] at accepted
    rw [← Except.ok.inj accepted]
    rw [feeAmount, ite_eq_left (Or.inl feeOff)]
    exact ⟨(Nat.add_zero st.totalSupply.toNat).symm, rfl, rfl⟩
  · rw [ite_eq_right feeOff] at accepted
    by_cases noLast : st.kLast = 0
    · rw [ite_eq_left noLast] at accepted
      rw [← Except.ok.inj accepted]
      rw [feeAmount, ite_eq_left (Or.inr noLast)]
      exact ⟨(Nat.add_zero st.totalSupply.toNat).symm, rfl, rfl⟩
    · rw [ite_eq_right noLast] at accepted
      have noShortcut : ¬(feeTo = 0 ∨ st.kLast = 0) := fun h => h.elim feeOff noLast
      rw [feeAmount, ite_eq_right noShortcut]
      by_cases growing : Nat.sqrt st.kLast.toNat < Nat.sqrt (reserve0 * reserve1)
      · rw [ite_eq_left growing] at accepted
        rw [ite_eq_left growing]
        by_cases numeratorBound :
            st.totalSupply.toNat * (Nat.sqrt (reserve0 * reserve1) - Nat.sqrt st.kLast.toNat) < 2 ^ 256
        · rw [ite_eq_left numeratorBound] at accepted
          by_cases scaledRootBound : Nat.sqrt (reserve0 * reserve1) * 5 < 2 ^ 256
          · rw [ite_eq_left scaledRootBound] at accepted
            by_cases denominatorBound :
                Nat.sqrt (reserve0 * reserve1) * 5 + Nat.sqrt st.kLast.toNat < 2 ^ 256
            · rw [ite_eq_left denominatorBound] at accepted
              by_cases positiveFee : st.totalSupply.toNat *
                  (Nat.sqrt (reserve0 * reserve1) - Nat.sqrt st.kLast.toNat) /
                  (Nat.sqrt (reserve0 * reserve1) * 5 + Nat.sqrt st.kLast.toNat) > 0
              · rw [ite_eq_left positiveFee] at accepted
                obtain ⟨⟨post, events⟩, minted, feeEq⟩ := Except.bind_eq_ok accepted
                have feeBound : st.totalSupply.toNat *
                    (Nat.sqrt (reserve0 * reserve1) - Nat.sqrt st.kLast.toNat) /
                    (Nat.sqrt (reserve0 * reserve1) * 5 + Nat.sqrt st.kLast.toNat) < 2 ^ 256 :=
                  Nat.lt_of_le_of_lt (Nat.div_le_self _ _) numeratorBound
                have supply := State.mintLP_supply_unlocked minted
                rw [B256.toNat_toB256_of_lt feeBound] at supply
                rw [← Except.ok.inj feeEq]
                exact ⟨supply.1, supply.2, rfl⟩
              · rw [ite_eq_right positiveFee] at accepted
                rw [← Except.ok.inj accepted]
                exact ⟨(Nat.add_zero st.totalSupply.toNat).symm, rfl,
                  (Nat.eq_zero_of_not_pos positiveFee).symm⟩
            · rw [ite_eq_right denominatorBound] at accepted
              cases accepted
          · rw [ite_eq_right scaledRootBound] at accepted
            cases accepted
        · rw [ite_eq_right numeratorBound] at accepted
          cases accepted
      · rw [ite_eq_right growing] at accepted
        rw [ite_eq_right growing]
        rw [← Except.ok.inj accepted]
        exact ⟨(Nat.add_zero st.totalSupply.toNat).symm, rfl, rfl⟩


/-- Successful fee minting exposes the exact post-fee supply T+F. -/
theorem mintFee_supply {st : State} {feeTo : Adr} {reserve0 reserve1 : Nat}
    {fee : FeeResult} (accepted : mintFee st feeTo reserve0 reserve1 = .ok fee) :
    fee.state.totalSupply.toNat = st.totalSupply.toNat + fee.minted := by
  exact (mintFee_spec accepted).1

/-- An accepted reserve update retains supply and stores the exact observed balances. -/
theorem State.update_supply_reserves {st post : State} {ctx : Context}
    {balance0 balance1 : B256} {reserve0 reserve1 : Nat} {event : Event} {update : OracleUpdate}
    (accepted : st.update ctx balance0 balance1 reserve0 reserve1 = .ok (post, event, update)) :
    post.totalSupply = st.totalSupply ∧
      post.reserve0.val = balance0.toNat ∧ post.reserve1.val = balance1.toNat := by
  rw [State.update] at accepted
  by_cases bound0 : balance0.toNat < 2 ^ 112
  · rw [dite_eq_left bound0] at accepted
    by_cases bound1 : balance1.toNat < 2 ^ 112
    · rw [dite_eq_left bound1] at accepted
      have postEq := Except.ok.inj accepted
      exact ⟨(congrArg (fun result : State × Event × OracleUpdate => result.1.totalSupply) postEq).symm,
        (congrArg (fun result : State × Event × OracleUpdate => result.1.reserve0.val) postEq).symm,
        (congrArg (fun result : State × Event × OracleUpdate => result.1.reserve1.val) postEq).symm⟩
    · rw [dite_eq_right bound1] at accepted
      cases accepted
  · rw [dite_eq_right bound0] at accepted
    cases accepted

/-- Successful update/fee/event/unlock completion preserves supply and exact reserves. -/
theorem Frame.finishUpdated_supply_reserves {frame final : Frame} {balance0 balance1 : B256}
    {reserves : CachedReserves} {feeOn : Bool} {lastEvent : Option Event} {returndata output : Bytes}
    (accepted : frame.finishUpdated balance0 balance1 reserves feeOn lastEvent returndata =
      .finished final output) :
    final.current.state.totalSupply = frame.current.state.totalSupply ∧
      final.current.state.reserve0.val = balance0.toNat ∧
      final.current.state.reserve1.val = balance1.toNat := by
  rw [Frame.finishUpdated] at accepted
  cases updated : frame.current.state.update frame.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val with
  | error failure =>
    simp only [updated, Frame.fail] at accepted
    cases accepted
  | ok result =>
    rcases result with ⟨post, event, update⟩
    simp only [updated] at accepted
    have fields := State.update_supply_reserves updated
    cases feeOn <;> cases lastEvent <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, Frame.withUpdate, Frame.withEvents,
        Frame.finishLocked, Frame.finish, SegmentResult.finished.injEq] at accepted
    all_goals
      rw [← accepted.1]
      exact fields


/-- The actual later-mint continuation consumes fee supply, checked issuance and reserve update. -/
theorem Frame.mintAfterFee_product {frame final : Frame} {observed : MintObserved}
    {fee : FeeResult} {feeTo : Adr} {returndata : Bytes}
    (feeAccepted : mintFee frame.current.state feeTo observed.reserves.reserve0.val
      observed.reserves.reserve1.val = .ok fee)
    (positiveSupply : fee.state.totalSupply ≠ 0)
    (amount0 : observed.reserves.reserve0.val + observed.amount0.toNat = observed.balance0.toNat)
    (amount1 : observed.reserves.reserve1.val + observed.amount1.toNat = observed.balance1.toNat)
    (accepted : frame.mintAfterFee observed fee = .finished final returndata) :
    observed.reserves.reserve0.val * observed.reserves.reserve1.val *
        final.current.state.totalSupply.toNat ^ 2 ≤
      final.current.state.reserve0.val * final.current.state.reserve1.val *
        (frame.current.state.totalSupply.toNat +
          feeAmount frame.current.state feeTo observed.reserves.reserve0.val observed.reserves.reserve1.val) ^ 2 := by
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
        have pricing := mintAmount_product positiveSupply priced
        have amountBound := (mintAmount_later_spec positiveSupply priced).2
        have issued := State.mintLP_supply minted
        rw [B256.toNat_toB256_of_lt amountBound] at issued
        have fields := Frame.finishUpdated_supply_reserves accepted
        have finalSupply : final.current.state.totalSupply.toNat =
            fee.state.totalSupply.toNat + liquidity :=
          (congrArg B256.toNat fields.1).trans issued
        rw [finalSupply, fields.2.1, fields.2.2, ← (mintFee_spec feeAccepted).2.2,
          ← mintFee_supply feeAccepted, ← amount0, ← amount1]
        exact pricing
    · simp only [ite_eq_right positive, Frame.fail] at accepted
      cases accepted


/-- The burn continuation's successful transfer suspension fixes its post-burn supply. -/
theorem Frame.burnAfterFee_supply {frame final : Frame} {observed : BurnObserved}
    {fee : FeeResult} {feeTo : Adr} {request : Request} {continuation : Continuation}
    (feeAccepted : mintFee frame.current.state feeTo observed.locals.reserves.reserve0.val
      observed.locals.reserves.reserve1.val = .ok fee)
    (accepted : frame.burnAfterFee observed fee = .suspended final request continuation) :
    observed.liquidity.toNat ≤ fee.state.totalSupply.toNat ∧
      final.current.state.totalSupply.toNat =
        frame.current.state.totalSupply.toNat + fee.minted - observed.liquidity.toNat := by
  rw [Frame.burnAfterFee] at accepted
  cases priced : burnAmounts observed.liquidity observed.balance0 observed.balance1
      fee.state.totalSupply with
  | error failure =>
    simp only [priced, Frame.fail] at accepted
    cases accepted
  | ok amounts =>
    rcases amounts with ⟨amount0, amount1⟩
    simp only [priced] at accepted
    by_cases positive : amount0 > 0 ∧ amount1 > 0
    · rw [ite_eq_left positive] at accepted
      cases burned : fee.state.burnLP frame.context.pair observed.liquidity with
      | error failure =>
        simp only [burned, Frame.fail] at accepted
        cases accepted
      | ok result =>
        rcases result with ⟨post, events⟩
        simp only [burned, Frame.withEvents, Frame.suspend, SegmentResult.suspended.injEq] at accepted
        have supply := State.burnLP_supply burned
        have finalSupply := congrArg (fun result : Frame => result.current.state.totalSupply.toNat)
          accepted.1
        rw [← mintFee_supply feeAccepted]
        exact ⟨supply.1, finalSupply.symm.trans supply.2⟩
    · simp only [ite_eq_right positive, Frame.fail] at accepted
      cases accepted

/-- A failed owned segment cannot become a successful return at any driver fuel. -/
theorem drive_failed_not_success (fuel : Nat) (frame : Frame) (failure : Failure)
    (transcript : Transcript) (returndata : Bytes) :
    (drive fuel (.failed frame failure) transcript).status ≠ .success returndata := by
  cases fuel with
  | zero => intro impossible; cases impossible
  | succ fuel => cases failure <;> intro impossible <;> cases impossible

/-- The external checkpoint is settled only from the actual nested-turn driver. -/
def Frame.settleExternal (frame : Frame) (fuel : Nat) (request : Request)
    (result : ExternalResult) (turns : Transcript) : Frame :=
  let executed := driveTurns fuel frame request 0 turns
  if result.success then executed.frame else { executed.frame with current := frame.current }

/-- Every successful suspended driver step exposes its actual complete external execution. -/
theorem drive_suspended_success {fuel : Nat} {frame : Frame} {request : Request}
    {continuation : Continuation} {transcript : Transcript} {returndata : Bytes}
    (successful : (drive (fuel + 1) (.suspended frame request continuation) transcript).status =
      .success returndata) :
    ∃ result turns tail, transcript = .next result turns tail ∧
      (driveTurns fuel frame request 0 turns).complete = true ∧
      (drive fuel (resumeSegment (frame.settleExternal fuel request result turns)
        request continuation result) tail).status = .success returndata ∧
      (drive (fuel + 1) (.suspended frame request continuation) transcript).frame =
        (drive fuel (resumeSegment (frame.settleExternal fuel request result turns)
          request continuation result) tail).frame := by
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
      · refine ⟨result, turns, tail, rfl, complete, ?_, ?_⟩
        · simpa only [drive, ite_eq_right missing, ite_eq_left complete, Frame.settleExternal] using successful
        · simp only [drive, ite_eq_right missing, ite_eq_left complete, Frame.settleExternal]
      · simp only [drive, ite_eq_right missing, ite_eq_right complete] at successful
        cases successful

/-- External settlement retains the economic core protected by the actual parent lock. -/
theorem Frame.settleExternal_locked_core {frame : Frame}
    (locked : frame.current.state.unlocked = 0)
    (fuel : Nat) (request : Request) (result : ExternalResult) (turns : Transcript) :
    (frame.settleExternal fuel request result turns).current.state.economicCore =
      frame.current.state.economicCore := by
  by_cases successful : result.success = true
  · rw [Frame.settleExternal, ite_eq_left successful]
    exact driveTurns_locked_core fuel frame request 0 turns locked
  · rw [Frame.settleExternal, ite_eq_right successful]


/-- A successful terminal driver exposes the same finished Frame and return bytes. -/
theorem drive_terminal_success {fuel : Nat} {segment : SegmentResult} {transcript : Transcript}
    {returndata : Bytes} (terminal : segment.Terminal)
    (successful : (drive fuel segment transcript).status = .success returndata) :
    ∃ final, segment = .finished final returndata ∧ (drive fuel segment transcript).frame = final := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    cases segment with
    | finished frame output =>
      have returned : output = returndata := RunStatus.success.inj successful
      subst output
      exact ⟨frame, rfl, rfl⟩
    | failed frame failure =>
      exact False.elim (drive_failed_not_success (fuel + 1) frame failure transcript returndata successful)
    | suspended frame request continuation => cases terminal

/-- Final reserve update, optional owned event and unlock have no further suspension. -/
theorem Frame.finishUpdated_terminal (frame : Frame) (balance0 balance1 : B256)
    (reserves : CachedReserves) (feeOn : Bool) (lastEvent : Option Event) (returndata : Bytes) :
    (frame.finishUpdated balance0 balance1 reserves feeOn lastEvent returndata).Terminal := by
  cases updated : frame.current.state.update frame.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val with
  | error failure =>
    simp only [Frame.finishUpdated, updated, Frame.fail, SegmentResult.Terminal]
  | ok result =>
    rcases result with ⟨post, event, update⟩
    cases feeOn <;> cases lastEvent <;>
      simp only [Frame.finishUpdated, updated, Bool.false_eq_true, ite_false, ite_true,
        Frame.finishLocked, Frame.finish, SegmentResult.Terminal]

/-- An error decoded at the call boundary cannot later yield a successful Pair return. -/
theorem resumeSegment_error_not_success {frame : Frame} {request : Request}
    {continuation : Continuation} {result : ExternalResult} {failure : Failure}
    (decoded : decodeExternal request result = .error failure)
    (fuel : Nat) (tail : Transcript) (returndata : Bytes) :
    (drive fuel (resumeSegment frame request continuation result) tail).status ≠ .success returndata := by
  rw [resumeSegment, decoded]
  exact drive_failed_not_success fuel _ failure tail returndata

/-- A successful balance observation is precisely its first returned word. -/
theorem decodeExternal_balance_word {request : Request} {result : ExternalResult}
    {owner : Adr} {balance : B256} (operation : request.operation = .balanceOf owner)
    (accepted : decodeExternal request result = .ok (.word balance)) :
    balance = Bytes.toB256 (result.returndata.take 32) := by
  simp only [decodeExternal, operation] at accepted
  by_cases missing : (request.requiresCode && !result.codeExists) = true
  · rw [ite_eq_left missing] at accepted
    cases accepted
  · rw [ite_eq_right missing] at accepted
    by_cases success : result.success = true
    · rw [ite_eq_left success] at accepted
      by_cases length : 32 ≤ result.returndata.length
      · rw [ite_eq_left length] at accepted
        exact (DecodedResult.word.inj (Except.ok.inj accepted)).symm
      · rw [ite_eq_right length] at accepted
        cases accepted
    · rw [ite_eq_right success] at accepted
      cases accepted


/-- Burn's final observed word is stored at the actual successful driver checkpoint. -/
theorem drive_burnFinalBalance1_values {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {balance0 : B256} {owner : Adr} {transcript : Transcript}
    {returndata : Bytes} (locked : frame.current.state.unlocked = 0)
    (operation : request.operation = .balanceOf owner)
    (successful : (drive fuel (.suspended frame request (.burnFinalBalance1 priced balance0))
      transcript).status = .success returndata) :
    ∃ result turns tail, transcript = .next result turns tail ∧
      (drive fuel (.suspended frame request (.burnFinalBalance1 priced balance0))
        transcript).frame.current.state.totalSupply = frame.current.state.totalSupply ∧
      (drive fuel (.suspended frame request (.burnFinalBalance1 priced balance0))
        transcript).frame.current.state.reserve0.val = balance0.toNat ∧
      (drive fuel (.suspended frame request (.burnFinalBalance1 priced balance0))
        transcript).frame.current.state.reserve1.val =
          (Bytes.toB256 (result.returndata.take 32)).toNat := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    have supply : (frame.settleExternal fuel request result turns).current.state.totalSupply =
        frame.current.state.totalSupply := congrArg (fun core => core.1) core
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
        have wordEq := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded] at resumedSuccess frameEq
        have terminal := Frame.finishUpdated_terminal
          ((frame.settleExternal fuel request result turns).beginResume request)
          balance0 balance1 priced.observed.locals.reserves priced.feeOn
          (some (.burn ((frame.settleExternal fuel request result turns).beginResume request).context.sender
            priced.amount0 priced.amount1 priced.observed.locals.recipient))
          (encodeWords [priced.amount0, priced.amount1])
        obtain ⟨final, finished, finalEq⟩ := drive_terminal_success terminal resumedSuccess
        have fields := Frame.finishUpdated_supply_reserves finished
        have outputEq := frameEq.trans finalEq
        refine ⟨result, turns, tail, shape, ?_, ?_, ?_⟩
        · rw [outputEq]
          exact fields.1.trans supply
        · rw [outputEq]
          exact fields.2.1
        · rw [outputEq]
          exact fields.2.2.trans (congrArg B256.toNat wordEq)


/-- Source-ordered final burn balance answers, separate from admission and nested turns. -/
def burnTailBalances : Continuation → Transcript → Option (B256 × B256)
  | .burnTransfer0 priced, .next _ _ tail => burnTailBalances (.burnTransfer1 priced) tail
  | .burnTransfer1 priced, .next _ _ tail => burnTailBalances (.burnFinalBalance0 priced) tail
  | .burnFinalBalance0 priced, .next result _ tail =>
      burnTailBalances (.burnFinalBalance1 priced (Bytes.toB256 (result.returndata.take 32))) tail
  | .burnFinalBalance1 _ balance0, .next result _ _ =>
      some (balance0, Bytes.toB256 (result.returndata.take 32))
  | _, _ => none

/-- The actual driver stores the projected burn answers and keeps post-burn supply. -/
def BurnTailOutcome (fuel : Nat) (frame : Frame) (request : Request)
    (continuation : Continuation) (transcript : Transcript) : Prop :=
  ∃ balance0 balance1, burnTailBalances continuation transcript = some (balance0, balance1) ∧
    (drive fuel (.suspended frame request continuation) transcript).frame.current.state.totalSupply =
      frame.current.state.totalSupply ∧
    (drive fuel (.suspended frame request continuation) transcript).frame.current.state.reserve0.val =
      balance0.toNat ∧
    (drive fuel (.suspended frame request continuation) transcript).frame.current.state.reserve1.val =
      balance1.toNat

/-- The last balance call supplies the base of the complete burn observation chain. -/
theorem drive_burnFinalBalance1_outcome {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {balance0 : B256} {owner : Adr} {transcript : Transcript}
    {returndata : Bytes} (locked : frame.current.state.unlocked = 0)
    (operation : request.operation = .balanceOf owner)
    (successful : (drive fuel (.suspended frame request (.burnFinalBalance1 priced balance0))
      transcript).status = .success returndata) :
    BurnTailOutcome fuel frame request (.burnFinalBalance1 priced balance0) transcript := by
  obtain ⟨result, turns, tail, shape, supply, reserve0, reserve1⟩ :=
    drive_burnFinalBalance1_values locked operation successful
  refine ⟨balance0, Bytes.toB256 (result.returndata.take 32), ?_, supply, reserve0, reserve1⟩
  simp only [shape, burnTailBalances]

/-- Burn's first final balance call joins both actual responses to the stored checkpoint. -/
theorem drive_burnFinalBalance0_outcome {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {owner : Adr} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (operation : request.operation = .balanceOf owner)
    (successful : (drive fuel (.suspended frame request (.burnFinalBalance0 priced))
      transcript).status = .success returndata) :
    BurnTailOutcome fuel frame request (.burnFinalBalance0 priced) transcript := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    let resumed := (frame.settleExternal fuel request result turns).beginResume request
    have resumeLocked : resumed.current.state.unlocked = 0 :=
      (congrArg (fun core => core.2.2.2.2.2) core).trans locked
    have resumeSupply : resumed.current.state.totalSupply = frame.current.state.totalSupply :=
      congrArg (fun core => core.1) core
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
        have wordEq := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded] at resumedSuccess frameEq
        obtain ⟨final0, final1, answers, supply, reserve0, reserve1⟩ :=
          drive_burnFinalBalance1_outcome resumeLocked rfl resumedSuccess
        refine ⟨final0, final1, ?_, ?_, ?_, ?_⟩
        · simpa only [shape, burnTailBalances, ← wordEq] using answers
        · rw [frameEq]
          exact supply.trans resumeSupply
        · rw [frameEq]
          exact reserve0
        · rw [frameEq]
          exact reserve1


/-- The second transfer resumes into the exact two-answer burn observation chain. -/
theorem drive_burnTransfer1_outcome {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (successful : (drive fuel (.suspended frame request (.burnTransfer1 priced))
      transcript).status = .success returndata) :
    BurnTailOutcome fuel frame request (.burnTransfer1 priced) transcript := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    let resumed := (frame.settleExternal fuel request result turns).beginResume request
    have resumeLocked : resumed.current.state.unlocked = 0 :=
      (congrArg (fun core => core.2.2.2.2.2) core).trans locked
    have resumeSupply : resumed.current.state.totalSupply = frame.current.state.totalSupply :=
      congrArg (fun core => core.1) core
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
        obtain ⟨final0, final1, answers, supply, reserve0, reserve1⟩ :=
          drive_burnFinalBalance0_outcome resumeLocked rfl resumedSuccess
        refine ⟨final0, final1, ?_, ?_, ?_, ?_⟩
        · simpa only [shape, burnTailBalances] using answers
        · rw [frameEq]
          exact supply.trans resumeSupply
        · rw [frameEq]
          exact reserve0
        · rw [frameEq]
          exact reserve1

/-- Both actual token transfers lead to the observed final stored reserves. -/
theorem drive_burnTransfer0_outcome {fuel : Nat} {frame : Frame} {request : Request}
    {priced : BurnPriced} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (successful : (drive fuel (.suspended frame request (.burnTransfer0 priced))
      transcript).status = .success returndata) :
    BurnTailOutcome fuel frame request (.burnTransfer0 priced) transcript := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    let resumed := (frame.settleExternal fuel request result turns).beginResume request
    have resumeLocked : resumed.current.state.unlocked = 0 :=
      (congrArg (fun core => core.2.2.2.2.2) core).trans locked
    have resumeSupply : resumed.current.state.totalSupply = frame.current.state.totalSupply :=
      congrArg (fun core => core.1) core
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
        obtain ⟨final0, final1, answers, supply, reserve0, reserve1⟩ :=
          drive_burnTransfer1_outcome resumeLocked resumedSuccess
        refine ⟨final0, final1, ?_, ?_, ?_, ?_⟩
        · simpa only [shape, burnTailBalances] using answers
        · rw [frameEq]
          exact supply.trans resumeSupply
        · rw [frameEq]
          exact reserve0
        · rw [frameEq]
          exact reserve1


/-- The four own call boundaries determine the final burn answers before theorem premises. -/
def burnFinalAnswers : Transcript → Option (B256 × B256)
  | .next _ _ (.next _ _ (.next result0 _ (.next result1 _ _))) =>
      some (Bytes.toB256 (result0.returndata.take 32), Bytes.toB256 (result1.returndata.take 32))
  | _ => none

/-- The continuation projection agrees with the independent four-boundary answer projection. -/
theorem burnTailBalances_transfer0 (priced : BurnPriced) (transcript : Transcript) :
    burnTailBalances (.burnTransfer0 priced) transcript = burnFinalAnswers transcript := by
  cases transcript <;> simp only [burnTailBalances, burnFinalAnswers]
  case next result0 turns0 tail0 =>
    cases tail0 <;> simp only [burnTailBalances]
    case next result1 turns1 tail1 =>
      cases tail1 <;> simp only [burnTailBalances]
      case next result2 turns2 tail2 =>
        cases tail2 <;> simp only [burnTailBalances]


/-- Burn backing and actual answer-plus-transfer cover are explicit economic premises. -/
def BurnNoShrink (observed : BurnObserved) (supply : B256) (transcript : Transcript) : Prop :=
  observed.locals.reserves.reserve0.val ≤ observed.balance0.toNat ∧
    observed.locals.reserves.reserve1.val ≤ observed.balance1.toNat ∧
    ∀ final0 final1, burnFinalAnswers transcript = some (final0, final1) →
      observed.balance0.toNat ≤ final0.toNat +
        (Nat.toB256 (AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance0.toNat
          supply.toNat)).toNat ∧
      observed.balance1.toNat ≤ final1.toNat +
        (Nat.toB256 (AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance1.toNat
          supply.toNat)).toNat

/-- Full burn pricing, transfers, observations and update realize the exact-fee product bound. -/
theorem Frame.burnAfterFee_driver_product {fuel : Nat} {frame : Frame} {observed : BurnObserved}
    {fee : FeeResult} {feeTo : Adr} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (feeAccepted : mintFee frame.current.state feeTo observed.locals.reserves.reserve0.val
      observed.locals.reserves.reserve1.val = .ok fee)
    (noShrink : BurnNoShrink observed fee.state.totalSupply transcript)
    (successful : (drive fuel (frame.burnAfterFee observed fee) transcript).status = .success returndata) :
    observed.locals.reserves.reserve0.val * observed.locals.reserves.reserve1.val *
        (drive fuel (frame.burnAfterFee observed fee) transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (drive fuel (frame.burnAfterFee observed fee) transcript).frame.current.state.reserve0.val *
        (drive fuel (frame.burnAfterFee observed fee) transcript).frame.current.state.reserve1.val *
        (frame.current.state.totalSupply.toNat + feeAmount frame.current.state feeTo
          observed.locals.reserves.reserve0.val observed.locals.reserves.reserve1.val) ^ 2 := by
  have feeSpec := mintFee_spec feeAccepted
  simp only [Frame.burnAfterFee] at successful ⊢
  cases priced : burnAmounts observed.liquidity observed.balance0 observed.balance1 fee.state.totalSupply with
  | error failure =>
    simp only [priced, Frame.fail] at successful
    exact False.elim (drive_failed_not_success fuel _ failure transcript returndata successful)
  | ok amounts =>
    rcases amounts with ⟨amount0, amount1⟩
    simp only [priced] at successful ⊢
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
        have suspension : frame.burnAfterFee observed fee =
            .suspended transferFrame
              (requestFor .burnTransfer0 observed.locals.token0
                (.transfer observed.locals.recipient pricedState.amount0))
              (.burnTransfer0 pricedState) := by
          simp only [Frame.burnAfterFee, priced, ite_eq_left positive, burned, Frame.suspend]
          rfl
        have entrySupply := Frame.burnAfterFee_supply feeAccepted suspension
        have transferLocked : transferFrame.current.state.unlocked = 0 :=
          supplySpec.2.2.trans (feeSpec.2.1.trans locked)
        obtain ⟨balance0, balance1, projected, supply, reserve0, reserve1⟩ :=
          drive_burnTransfer0_outcome transferLocked successful
        have actualAnswers : burnFinalAnswers transcript = some (balance0, balance1) :=
          (burnTailBalances_transfer0 pricedState transcript).symm.trans projected
        obtain ⟨debit0, debit1⟩ := noShrink.2.2 balance0 balance1 actualAnswers
        have prices := burnAmounts_spec priced
        rw [← prices.1, B256.toNat_toB256_of_lt prices.2.2.1] at debit0
        rw [← prices.2.1, B256.toNat_toB256_of_lt prices.2.2.2] at debit1
        have finalSupply :
            (drive fuel
              (.suspended transferFrame
                (requestFor .burnTransfer0 observed.locals.token0
                  (.transfer observed.locals.recipient pricedState.amount0))
                (.burnTransfer0 pricedState)) transcript).frame.current.state.totalSupply.toNat =
              frame.current.state.totalSupply.toNat + fee.minted - observed.liquidity.toNat :=
          (congrArg B256.toNat supply).trans entrySupply.2
        rw [finalSupply, reserve0, reserve1, ← feeSpec.2.2, ← feeSpec.1]
        exact burnAmounts_product priced noShrink.1 noShrink.2.1 entrySupply.1 debit0 debit1
    · simp only [ite_eq_right positive, Frame.fail] at successful
      exact False.elim
        (drive_failed_not_success fuel _ (.sourceGuard "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED")
          transcript returndata successful)


/-- A later mint completes or rolls back without another owned external call. -/
theorem Frame.mintAfterFee_terminal_later (frame : Frame) (observed : MintObserved) (fee : FeeResult)
    (positiveSupply : fee.state.totalSupply ≠ 0) :
    (frame.mintAfterFee observed fee).Terminal := by
  rw [Frame.mintAfterFee]
  cases priced : mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val with
  | error failure => simp only [Frame.fail, SegmentResult.Terminal]
  | ok liquidity =>
    simp only [ite_eq_right positiveSupply]
    by_cases positive : liquidity > 0
    · rw [ite_eq_left positive]
      cases minted : fee.state.mintLP observed.recipient (Nat.toB256 liquidity) with
      | error failure => simp only [Frame.fail, SegmentResult.Terminal]
      | ok result =>
        rcases result with ⟨post, events⟩
        exact Frame.finishUpdated_terminal _ observed.balance0 observed.balance1 observed.reserves
          fee.feeOn (some (.mint frame.context.sender observed.amount0 observed.amount1))
          (encodeWords [Nat.toB256 liquidity])
    · simp only [ite_eq_right positive, Frame.fail, SegmentResult.Terminal]

/-- The later-mint actual driver checkpoint obeys the exact integer fee correction. -/
theorem Frame.mintAfterFee_driver_product {fuel : Nat} {frame : Frame} {observed : MintObserved}
    {fee : FeeResult} {feeTo : Adr} {transcript : Transcript} {returndata : Bytes}
    (feeAccepted : mintFee frame.current.state feeTo observed.reserves.reserve0.val
      observed.reserves.reserve1.val = .ok fee)
    (positiveSupply : fee.state.totalSupply ≠ 0)
    (amount0 : observed.reserves.reserve0.val + observed.amount0.toNat = observed.balance0.toNat)
    (amount1 : observed.reserves.reserve1.val + observed.amount1.toNat = observed.balance1.toNat)
    (successful : (drive fuel (frame.mintAfterFee observed fee) transcript).status = .success returndata) :
    observed.reserves.reserve0.val * observed.reserves.reserve1.val *
        (drive fuel (frame.mintAfterFee observed fee) transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (drive fuel (frame.mintAfterFee observed fee) transcript).frame.current.state.reserve0.val *
        (drive fuel (frame.mintAfterFee observed fee) transcript).frame.current.state.reserve1.val *
        (frame.current.state.totalSupply.toNat +
          feeAmount frame.current.state feeTo observed.reserves.reserve0.val observed.reserves.reserve1.val) ^ 2 := by
  obtain ⟨final, finished, frameEq⟩ :=
    drive_terminal_success (Frame.mintAfterFee_terminal_later frame observed fee positiveSupply) successful
  rw [frameEq]
  exact Frame.mintAfterFee_product feeAccepted positiveSupply amount0 amount1 finished

/-- Static external settlement keeps the exact pre-query Frame, even on call failure. -/
theorem Frame.settleExternal_static_frame (frame : Frame) (fuel : Nat) (request : Request)
    (result : ExternalResult) (turns : Transcript)
    (staticExternal : externalStatic frame request = true) :
    frame.settleExternal fuel request result turns = frame := by
  rw [Frame.settleExternal, driveTurns_static_frame fuel frame request 0 turns staticExternal]
  cases result.success <;> rfl

/-- The fee recipient is the address decoded from the actual first return word. -/
theorem decodeExternal_feeTo_address {request : Request} {result : ExternalResult}
    {recipient : Adr} (operation : request.operation = .feeTo)
    (accepted : decodeExternal request result = .ok (.address recipient)) :
    recipient = (Bytes.toB256 (result.returndata.take 32)).toAdr := by
  simp only [decodeExternal, operation] at accepted
  by_cases missing : (request.requiresCode && !result.codeExists) = true
  · rw [ite_eq_left missing] at accepted
    cases accepted
  · rw [ite_eq_right missing] at accepted
    by_cases success : result.success = true
    · rw [ite_eq_left success] at accepted
      by_cases length : 32 ≤ result.returndata.length
      · rw [ite_eq_left length] at accepted
        exact (DecodedResult.address.inj (Except.ok.inj accepted)).symm
      · rw [ite_eq_right length] at accepted
        cases accepted
    · rw [ite_eq_right success] at accepted
      cases accepted

/-- Own-call projections read input bytes independently of successful execution. -/
def Transcript.firstWord : Transcript → B256
  | .next result _ _ => Bytes.toB256 (result.returndata.take 32)
  | _ => 0

def Transcript.ownTail : Transcript → Transcript
  | .next _ _ tail => tail
  | _ => .done

/-- Fee-query-stage backing uses the independently projected recipient and final answers. -/
def BurnFeeNoShrink (st : State) (observed : BurnObserved) (transcript : Transcript) : Prop :=
  observed.locals.reserves.reserve0.val ≤ observed.balance0.toNat ∧
    observed.locals.reserves.reserve1.val ≤ observed.balance1.toNat ∧
    ∀ final0 final1, burnFinalAnswers transcript.ownTail = some (final0, final1) →
      observed.balance0.toNat ≤ final0.toNat +
        (Nat.toB256 (AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance0.toNat
          (st.totalSupply.toNat + feeAmount st transcript.firstWord.toAdr
            observed.locals.reserves.reserve0.val observed.locals.reserves.reserve1.val))).toNat ∧
      observed.balance1.toNat ≤ final1.toNat +
        (Nat.toB256 (AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance1.toNat
          (st.totalSupply.toNat + feeAmount st transcript.firstWord.toAdr
            observed.locals.reserves.reserve0.val observed.locals.reserves.reserve1.val))).toNat


/-- Burn's actual fee query connects independent input backing to the completed burn driver. -/
theorem drive_burnFee_product {fuel : Nat} {frame : Frame} {request : Request}
    {observed : BurnObserved} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (operation : request.operation = .feeTo) (kind : request.kind = .staticCall)
    (noShrink : BurnFeeNoShrink frame.current.state observed transcript)
    (successful : (drive fuel (.suspended frame request (.burnFee observed))
      transcript).status = .success returndata) :
    observed.locals.reserves.reserve0.val * observed.locals.reserves.reserve1.val *
        (drive fuel (.suspended frame request (.burnFee observed))
          transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (drive fuel (.suspended frame request (.burnFee observed))
        transcript).frame.current.state.reserve0.val *
        (drive fuel (.suspended frame request (.burnFee observed))
          transcript).frame.current.state.reserve1.val *
        (frame.current.state.totalSupply.toNat + feeAmount frame.current.state
          transcript.firstWord.toAdr observed.locals.reserves.reserve0.val
          observed.locals.reserves.reserve1.val) ^ 2 := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
        cases charged : mintFee (frame.beginResume request).current.state feeTo
            observed.locals.reserves.reserve0.val observed.locals.reserves.reserve1.val with
        | error failure =>
          simp only [resumeSegment, decoded, charged, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _ failure tail returndata resumedSuccess)
        | ok fee =>
          simp only [resumeSegment, decoded, charged] at resumedSuccess frameEq
          have feeSpec := mintFee_spec charged
          simp only [BurnFeeNoShrink, shape, Transcript.ownTail, Transcript.firstWord,
            ← recipientEq] at noShrink
          have backing : BurnNoShrink observed fee.state.totalSupply tail := by
            simpa only [BurnNoShrink, feeSpec.1, feeSpec.2.2, Frame.beginResume] using noShrink
          have economic := Frame.burnAfterFee_driver_product (frame := frame.beginResume request)
            locked charged backing resumedSuccess
          rw [frameEq]
          simpa only [shape, Transcript.firstWord, ← recipientEq, Frame.beginResume] using economic


/-- The second initial burn balance query supplies the exact observed balance and LP amount. -/
theorem drive_burnInitialBalance1_product {fuel : Nat} {frame : Frame} {request : Request}
    {locals : BurnLocals} {balance0 : B256} {owner : Adr} {transcript : Transcript}
    {returndata : Bytes} (locked : frame.current.state.unlocked = 0)
    (operation : request.operation = .balanceOf owner) (kind : request.kind = .staticCall)
    (noShrink : BurnFeeNoShrink frame.current.state
      { locals := locals, balance0 := balance0, balance1 := transcript.firstWord,
        liquidity := frame.current.state.balanceOf frame.context.pair } transcript.ownTail)
    (successful : (drive fuel (.suspended frame request (.burnInitialBalance1 locals balance0))
      transcript).status = .success returndata) :
    locals.reserves.reserve0.val * locals.reserves.reserve1.val *
        (drive fuel (.suspended frame request (.burnInitialBalance1 locals balance0))
          transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (drive fuel (.suspended frame request (.burnInitialBalance1 locals balance0))
        transcript).frame.current.state.reserve0.val *
        (drive fuel (.suspended frame request (.burnInitialBalance1 locals balance0))
          transcript).frame.current.state.reserve1.val *
        (frame.current.state.totalSupply.toNat + feeAmount frame.current.state
          transcript.ownTail.firstWord.toAdr locals.reserves.reserve0.val
          locals.reserves.reserve1.val) ^ 2 := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
      | address recipient =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance1 =>
        have wordEq := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess frameEq
        have backing : BurnFeeNoShrink (frame.beginResume request).current.state
            { locals := locals, balance0 := balance0, balance1 := balance1,
              liquidity := (frame.beginResume request).current.state.balanceOf
                (frame.beginResume request).context.pair } tail := by
          simpa only [shape, Transcript.ownTail, Transcript.firstWord, ← wordEq, Frame.beginResume] using noShrink
        have economic := drive_burnFee_product (frame := frame.beginResume request)
          locked rfl rfl backing resumedSuccess
        rw [frameEq]
        simpa only [shape, Transcript.ownTail, Frame.beginResume] using economic


/-- Both initial burn observations and the fee query feed the actual completed economic result. -/
theorem drive_burnInitialBalance0_product {fuel : Nat} {frame : Frame} {request : Request}
    {locals : BurnLocals} {owner : Adr} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (operation : request.operation = .balanceOf owner) (kind : request.kind = .staticCall)
    (noShrink : BurnFeeNoShrink frame.current.state
      { locals := locals, balance0 := transcript.firstWord,
        balance1 := transcript.ownTail.firstWord,
        liquidity := frame.current.state.balanceOf frame.context.pair }
      transcript.ownTail.ownTail)
    (successful : (drive fuel (.suspended frame request (.burnInitialBalance0 locals))
      transcript).status = .success returndata) :
    locals.reserves.reserve0.val * locals.reserves.reserve1.val *
        (drive fuel (.suspended frame request (.burnInitialBalance0 locals))
          transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (drive fuel (.suspended frame request (.burnInitialBalance0 locals))
        transcript).frame.current.state.reserve0.val *
        (drive fuel (.suspended frame request (.burnInitialBalance0 locals))
          transcript).frame.current.state.reserve1.val *
        (frame.current.state.totalSupply.toNat + feeAmount frame.current.state
          transcript.ownTail.ownTail.firstWord.toAdr locals.reserves.reserve0.val
          locals.reserves.reserve1.val) ^ 2 := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
      | address recipient =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance0 =>
        have wordEq := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess frameEq
        have backing : BurnFeeNoShrink (frame.beginResume request).current.state
            { locals := locals, balance0 := balance0, balance1 := tail.firstWord,
              liquidity := (frame.beginResume request).current.state.balanceOf
                (frame.beginResume request).context.pair } tail.ownTail := by
          simpa only [shape, Transcript.ownTail, Transcript.firstWord, ← wordEq, Frame.beginResume] using noShrink
        have economic := drive_burnInitialBalance1_product (frame := frame.beginResume request)
          locked rfl rfl backing resumedSuccess
        rw [frameEq]
        simpa only [shape, Transcript.ownTail, Frame.beginResume] using economic


/-- Whole-entry burn backing reads the own balance answers and fee answer independently. -/
def BurnEntryNoShrink (st : State) (pair recipient : Adr) (transcript : Transcript) : Prop :=
  BurnFeeNoShrink st
    { locals := { recipient := recipient, reserves := st.cachedReserves, token0 := st.token0, token1 := st.token1 },
      balance0 := transcript.firstWord, balance1 := transcript.ownTail.firstWord,
      liquidity := st.balanceOf pair } transcript.ownTail.ownTail

/-- Every successful typed burn entry satisfies the exact-fee economic checkpoint inequality. -/
theorem drive_startTyped_burn_product {fuel : Nat} {current : Checkpoint} {ctx : Context}
    {recipient : Adr} {transcript : Transcript} {returndata : Bytes}
    (noShrink : BurnEntryNoShrink current.state ctx.pair recipient transcript)
    (successful : (drive fuel (startTyped current ctx (.burn recipient)) transcript).status =
      .success returndata) :
    current.state.reserve0.val * current.state.reserve1.val *
        (drive fuel (startTyped current ctx (.burn recipient)) transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (drive fuel (startTyped current ctx (.burn recipient)) transcript).frame.current.state.reserve0.val *
        (drive fuel (startTyped current ctx (.burn recipient)) transcript).frame.current.state.reserve1.val *
        (current.state.totalSupply.toNat + feeAmount current.state
          transcript.ownTail.ownTail.firstWord.toAdr current.state.reserve0.val
          current.state.reserve1.val) ^ 2 := by
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
        have backing : BurnFeeNoShrink lockedFrame.current.state
            { locals := locals, balance0 := transcript.firstWord,
              balance1 := transcript.ownTail.firstWord,
              liquidity := lockedFrame.current.state.balanceOf lockedFrame.context.pair }
            transcript.ownTail.ownTail := by
          simpa only [BurnEntryNoShrink, BurnFeeNoShrink, feeAmount, lockedFrame, locals,
            Frame.enter] using noShrink
        have suspendedSuccess :
            (drive fuel (.suspended lockedFrame
              (requestFor .burnInitialBalance0 locals.token0 (.balanceOf ctx.pair))
              (.burnInitialBalance0 locals)) transcript).status = .success returndata := by
          simpa only [stage, Frame.suspend] using successful
        have economic := drive_burnInitialBalance0_product (frame := lockedFrame)
          (by rfl) rfl rfl backing suspendedSuccess
        have initialSupply : lockedFrame.current.state.totalSupply.toNat =
            current.state.totalSupply.toNat := rfl
        have initialFee : feeAmount lockedFrame.current.state
            transcript.ownTail.ownTail.firstWord.toAdr locals.reserves.reserve0.val
            locals.reserves.reserve1.val =
            feeAmount current.state transcript.ownTail.ownTail.firstWord.toAdr
              current.state.reserve0.val current.state.reserve1.val := rfl
        rw [initialSupply, initialFee] at economic
        rw [stage, Frame.suspend]
        simpa only [locals, State.cachedReserves] using economic
    · have enteredLocked : ¬(Frame.enter current ctx (.burn recipient)).current.state.unlocked = 1 :=
        unlocked
      have closed : (Frame.enter current ctx (.burn recipient)).lock =
          .error (.sourceGuard "UniswapV2: LOCKED") := by
        rw [Frame.lock, ite_eq_right enteredLocked]
      simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, closed, Frame.fail] at successful
      exact False.elim (drive_failed_not_success fuel _
        (.sourceGuard "UniswapV2: LOCKED") transcript returndata successful)

/-- The public finite typed driver consumes the whole burn-entry economic proof. -/
theorem runTyped_burn_product {st : State} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {returndata : Bytes}
    (noShrink : BurnEntryNoShrink st ctx.pair recipient transcript)
    (successful : (runTyped st ctx (.burn recipient) transcript).status = .success returndata) :
    st.reserve0.val * st.reserve1.val *
        (runTyped st ctx (.burn recipient) transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (runTyped st ctx (.burn recipient) transcript).frame.current.state.reserve0.val *
        (runTyped st ctx (.burn recipient) transcript).frame.current.state.reserve1.val *
        (st.totalSupply.toNat + feeAmount st transcript.ownTail.ownTail.firstWord.toAdr
          st.reserve0.val st.reserve1.val) ^ 2 := by
  exact drive_startTyped_burn_product noShrink successful

/-- A successful later-mint fee query preserves the positive-supply branch and exact fee bound. -/
theorem drive_mintFee_product {fuel : Nat} {frame : Frame} {request : Request}
    {observed : MintObserved} {transcript : Transcript} {returndata : Bytes}
    (positiveSupply : 0 < frame.current.state.totalSupply.toNat)
    (operation : request.operation = .feeTo) (kind : request.kind = .staticCall)
    (amount0 : observed.reserves.reserve0.val + observed.amount0.toNat = observed.balance0.toNat)
    (amount1 : observed.reserves.reserve1.val + observed.amount1.toNat = observed.balance1.toNat)
    (successful : (drive fuel (.suspended frame request (.mintFee observed))
      transcript).status = .success returndata) :
    observed.reserves.reserve0.val * observed.reserves.reserve1.val *
        (drive fuel (.suspended frame request (.mintFee observed))
          transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (drive fuel (.suspended frame request (.mintFee observed))
        transcript).frame.current.state.reserve0.val *
        (drive fuel (.suspended frame request (.mintFee observed))
          transcript).frame.current.state.reserve1.val *
        (frame.current.state.totalSupply.toNat + feeAmount frame.current.state
          transcript.firstWord.toAdr observed.reserves.reserve0.val
          observed.reserves.reserve1.val) ^ 2 := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
        cases charged : mintFee (frame.beginResume request).current.state feeTo
            observed.reserves.reserve0.val observed.reserves.reserve1.val with
        | error failure =>
          simp only [resumeSegment, decoded, charged, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _ failure tail returndata resumedSuccess)
        | ok fee =>
          simp only [resumeSegment, decoded, charged] at resumedSuccess frameEq
          have feeSpec := mintFee_spec charged
          have feePositive : 0 < fee.state.totalSupply.toNat := by
            rw [feeSpec.1]
            exact Nat.add_pos_left positiveSupply fee.minted
          have feeNonzero : fee.state.totalSupply ≠ 0 := by
            intro zero
            have impossible : 0 < 0 := by
              simpa only [zero, B256.toNat_zero] using feePositive
            exact Nat.lt_irrefl 0 impossible
          have economic := Frame.mintAfterFee_driver_product (frame := frame.beginResume request)
            charged feeNonzero amount0 amount1 resumedSuccess
          rw [frameEq]
          simpa only [shape, Transcript.firstWord, ← recipientEq, Frame.beginResume] using economic


/-- The checked second mint observation derives both exact amount equations from backing. -/
theorem drive_mintBalance1_product {fuel : Nat} {frame : Frame} {request : Request}
    {recipient : Adr} {reserves : CachedReserves} {balance0 : B256}
    {transcript : Transcript} {returndata : Bytes}
    (positiveSupply : 0 < frame.current.state.totalSupply.toNat)
    (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.mintBalance1 recipient reserves balance0))
      transcript).status = .success returndata) :
    reserves.reserve0.val * reserves.reserve1.val *
        (drive fuel (.suspended frame request (.mintBalance1 recipient reserves balance0))
          transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (drive fuel (.suspended frame request (.mintBalance1 recipient reserves balance0))
        transcript).frame.current.state.reserve0.val *
        (drive fuel (.suspended frame request (.mintBalance1 recipient reserves balance0))
          transcript).frame.current.state.reserve1.val *
        (frame.current.state.totalSupply.toNat + feeAmount frame.current.state
          transcript.ownTail.firstWord.toAdr reserves.reserve0.val reserves.reserve1.val) ^ 2 := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
        simp only [resumeSegment, decoded] at resumedSuccess frameEq
        by_cases backing : reserves.reserve0.val ≤ balance0.toNat ∧
            reserves.reserve1.val ≤ balance1.toNat
        · rw [ite_eq_left backing] at resumedSuccess frameEq
          simp only [Frame.suspend] at resumedSuccess frameEq
          let observed : MintObserved :=
            { recipient := recipient, reserves := reserves, balance0 := balance0, balance1 := balance1,
              amount0 := balance0 - Nat.toB256 reserves.reserve0.val,
              amount1 := balance1 - Nat.toB256 reserves.reserve1.val }
          have bound0 : reserves.reserve0.val < 2 ^ 256 :=
            Nat.lt_trans reserves.reserve0.isLt (by decide)
          have bound1 : reserves.reserve1.val < 2 ^ 256 :=
            Nat.lt_trans reserves.reserve1.isLt (by decide)
          have covered0 : Nat.toB256 reserves.reserve0.val ≤ balance0 :=
            B256.le_of_toNat_le_toNat (by
              rw [B256.toNat_toB256_of_lt bound0]
              exact backing.1)
          have covered1 : Nat.toB256 reserves.reserve1.val ≤ balance1 :=
            B256.le_of_toNat_le_toNat (by
              rw [B256.toNat_toB256_of_lt bound1]
              exact backing.2)
          have amount0 : reserves.reserve0.val + observed.amount0.toNat = balance0.toNat := by
            rw [B256.toNat_sub_eq_of_le _ _ covered0, B256.toNat_toB256_of_lt bound0]
            exact Nat.add_sub_of_le backing.1
          have amount1 : reserves.reserve1.val + observed.amount1.toNat = balance1.toNat := by
            rw [B256.toNat_sub_eq_of_le _ _ covered1, B256.toNat_toB256_of_lt bound1]
            exact Nat.add_sub_of_le backing.2
          have economic := drive_mintFee_product (frame := frame.beginResume request)
            (observed := observed) positiveSupply rfl rfl amount0 amount1 resumedSuccess
          rw [frameEq]
          simpa only [observed, shape, Transcript.ownTail, Frame.beginResume] using economic
        · simp only [ite_eq_right backing, Frame.fail] at resumedSuccess
          exact False.elim
            (drive_failed_not_success fuel _ (.sourceGuard "ds-math-sub-underflow")
              tail returndata resumedSuccess)


/-- The first mint balance query feeds the fully checked later-mint observation chain. -/
theorem drive_mintBalance0_product {fuel : Nat} {frame : Frame} {request : Request}
    {recipient : Adr} {reserves : CachedReserves} {transcript : Transcript} {returndata : Bytes}
    (positiveSupply : 0 < frame.current.state.totalSupply.toNat)
    (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.mintBalance0 recipient reserves))
      transcript).status = .success returndata) :
    reserves.reserve0.val * reserves.reserve1.val *
        (drive fuel (.suspended frame request (.mintBalance0 recipient reserves))
          transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (drive fuel (.suspended frame request (.mintBalance0 recipient reserves))
        transcript).frame.current.state.reserve0.val *
        (drive fuel (.suspended frame request (.mintBalance0 recipient reserves))
          transcript).frame.current.state.reserve1.val *
        (frame.current.state.totalSupply.toNat + feeAmount frame.current.state
          transcript.ownTail.ownTail.firstWord.toAdr reserves.reserve0.val reserves.reserve1.val) ^ 2 := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
        have economic := drive_mintBalance1_product (frame := frame.beginResume request)
          positiveSupply rfl resumedSuccess
        rw [frameEq]
        simpa only [shape, Transcript.ownTail, Frame.beginResume] using economic

/-- Every successful later-mint entry derives backing and realizes the exact-fee bound. -/
theorem drive_startTyped_mint_product {fuel : Nat} {current : Checkpoint} {ctx : Context}
    {recipient : Adr} {transcript : Transcript} {returndata : Bytes}
    (positiveSupply : 0 < current.state.totalSupply.toNat)
    (successful : (drive fuel (startTyped current ctx (.mint recipient)) transcript).status =
      .success returndata) :
    current.state.reserve0.val * current.state.reserve1.val *
        (drive fuel (startTyped current ctx (.mint recipient)) transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (drive fuel (startTyped current ctx (.mint recipient)) transcript).frame.current.state.reserve0.val *
        (drive fuel (startTyped current ctx (.mint recipient)) transcript).frame.current.state.reserve1.val *
        (current.state.totalSupply.toNat + feeAmount current.state
          transcript.ownTail.ownTail.firstWord.toAdr current.state.reserve0.val
          current.state.reserve1.val) ^ 2 := by
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
        have economic := drive_mintBalance0_product (frame := lockedFrame)
          positiveSupply rfl suspendedSuccess
        have initialSupply : lockedFrame.current.state.totalSupply.toNat =
            current.state.totalSupply.toNat := rfl
        have initialFee : feeAmount lockedFrame.current.state
            transcript.ownTail.ownTail.firstWord.toAdr reserves.reserve0.val reserves.reserve1.val =
            feeAmount current.state transcript.ownTail.ownTail.firstWord.toAdr
              current.state.reserve0.val current.state.reserve1.val := rfl
        rw [initialSupply, initialFee] at economic
        rw [stage, Frame.suspend]
        simpa only [reserves, State.cachedReserves] using economic
    · have enteredLocked : ¬(Frame.enter current ctx (.mint recipient)).current.state.unlocked = 1 :=
        unlocked
      have closed : (Frame.enter current ctx (.mint recipient)).lock =
          .error (.sourceGuard "UniswapV2: LOCKED") := by
        rw [Frame.lock, ite_eq_right enteredLocked]
      simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, closed, Frame.fail] at successful
      exact False.elim (drive_failed_not_success fuel _
        (.sourceGuard "UniswapV2: LOCKED") transcript returndata successful)

/-- The public finite typed driver consumes the complete later-mint economic proof. -/
theorem runTyped_mint_product {st : State} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {returndata : Bytes}
    (positiveSupply : 0 < st.totalSupply.toNat)
    (successful : (runTyped st ctx (.mint recipient) transcript).status = .success returndata) :
    st.reserve0.val * st.reserve1.val *
        (runTyped st ctx (.mint recipient) transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (runTyped st ctx (.mint recipient) transcript).frame.current.state.reserve0.val *
        (runTyped st ctx (.mint recipient) transcript).frame.current.state.reserve1.val *
        (st.totalSupply.toNat + feeAmount st transcript.ownTail.ownTail.firstWord.toAdr
          st.reserve0.val st.reserve1.val) ^ 2 := by
  exact drive_startTyped_mint_product
    (current := { state := st, logs := [], updates := [] }) (ctx := ctx) (recipient := recipient)
    (fuel := transcript.work + 2) (transcript := transcript) (returndata := returndata)
    positiveSupply successful

/-- Sync stores its final returned balance word and preserves the pre-query supply. -/
theorem drive_syncBalance1_values {fuel : Nat} {frame : Frame} {request : Request}
    {reserves : CachedReserves} {balance0 : B256} {owner : Adr} {transcript : Transcript}
    {returndata : Bytes} (kind : request.kind = .staticCall)
    (operation : request.operation = .balanceOf owner)
    (successful : (drive fuel (.suspended frame request (.syncBalance1 reserves balance0))
      transcript).status = .success returndata) :
    (drive fuel (.suspended frame request (.syncBalance1 reserves balance0))
      transcript).frame.current.state.totalSupply = frame.current.state.totalSupply ∧
      (drive fuel (.suspended frame request (.syncBalance1 reserves balance0))
        transcript).frame.current.state.reserve0.val = balance0.toNat ∧
      (drive fuel (.suspended frame request (.syncBalance1 reserves balance0))
        transcript).frame.current.state.reserve1.val = transcript.firstWord.toNat := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
        have wordEq := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded] at resumedSuccess frameEq
        have terminal := Frame.finishUpdated_terminal (frame.beginResume request)
          balance0 balance1 reserves false none []
        obtain ⟨final, finished, finalEq⟩ := drive_terminal_success terminal resumedSuccess
        have fields := Frame.finishUpdated_supply_reserves finished
        rw [frameEq, finalEq]
        refine ⟨?_, fields.2.1, ?_⟩
        · simpa only [Frame.beginResume] using fields.1
        · rw [shape, Transcript.firstWord]
          exact fields.2.2.trans (congrArg B256.toNat wordEq)


/-- Sync's two actual static observations are its final reserves, with unchanged supply. -/
theorem drive_syncBalance0_values {fuel : Nat} {frame : Frame} {request : Request}
    {reserves : CachedReserves} {owner : Adr} {transcript : Transcript} {returndata : Bytes}
    (kind : request.kind = .staticCall) (operation : request.operation = .balanceOf owner)
    (successful : (drive fuel (.suspended frame request (.syncBalance0 reserves))
      transcript).status = .success returndata) :
    (drive fuel (.suspended frame request (.syncBalance0 reserves))
      transcript).frame.current.state.totalSupply = frame.current.state.totalSupply ∧
      (drive fuel (.suspended frame request (.syncBalance0 reserves))
        transcript).frame.current.state.reserve0.val = transcript.firstWord.toNat ∧
      (drive fuel (.suspended frame request (.syncBalance0 reserves))
        transcript).frame.current.state.reserve1.val = transcript.ownTail.firstWord.toNat := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
        have wordEq := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess frameEq
        have fields := drive_syncBalance1_values (frame := frame.beginResume request)
          rfl rfl resumedSuccess
        rw [frameEq]
        simpa only [shape, Transcript.firstWord, Transcript.ownTail, Frame.beginResume, wordEq]
          using fields


/-- Successful sync derives the entry guards and stores both independent observations. -/
theorem drive_startTyped_sync_values {fuel : Nat} {current : Checkpoint} {ctx : Context}
    {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (startTyped current ctx .sync) transcript).status = .success returndata) :
    (drive fuel (startTyped current ctx .sync) transcript).frame.current.state.totalSupply =
        current.state.totalSupply ∧
      (drive fuel (startTyped current ctx .sync) transcript).frame.current.state.reserve0.val =
        transcript.firstWord.toNat ∧
      (drive fuel (startTyped current ctx .sync) transcript).frame.current.state.reserve1.val =
        transcript.ownTail.firstWord.toNat := by
  by_cases paid : ctx.value ≠ 0
  · simp only [startTyped, startImmediate, ite_eq_left paid, Frame.fail] at successful
    exact False.elim (drive_failed_not_success fuel _ .emptyRevert transcript returndata successful)
  · by_cases unlocked : current.state.unlocked = 1
    · by_cases staticContext : ctx.isStatic = true
      · simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, Frame.lock,
          Frame.enter, ite_eq_left unlocked, staticContext, ite_true, Frame.fail] at successful
        exact False.elim (drive_failed_not_success fuel _ .staticWrite transcript returndata successful)
      · let lockedFrame : Frame :=
          { Frame.enter current ctx .sync with
            current := { current with state := { current.state with unlocked := 0 } } }
        let reserves := current.state.cachedReserves
        have enteredUnlocked : (Frame.enter current ctx .sync).current.state.unlocked = 1 := unlocked
        have enteredStatic : ¬(Frame.enter current ctx .sync).context.isStatic = true := staticContext
        have opened : (Frame.enter current ctx .sync).lock = .ok lockedFrame := by
          rw [Frame.lock, ite_eq_left enteredUnlocked, ite_eq_right enteredStatic]
          rfl
        have stage : startTyped current ctx .sync =
            lockedFrame.suspend .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
              (.syncBalance0 reserves) := by
          simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, opened]
          rfl
        have suspendedSuccess :
            (drive fuel (.suspended lockedFrame
              (requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair))
              (.syncBalance0 reserves)) transcript).status = .success returndata := by
          simpa only [stage, Frame.suspend] using successful
        have fields := drive_syncBalance0_values (frame := lockedFrame) rfl rfl suspendedSuccess
        rw [stage, Frame.suspend]
        exact fields
    · have enteredLocked : ¬(Frame.enter current ctx .sync).current.state.unlocked = 1 := unlocked
      have closed : (Frame.enter current ctx .sync).lock =
          .error (.sourceGuard "UniswapV2: LOCKED") := by
        rw [Frame.lock, ite_eq_right enteredLocked]
      simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, closed, Frame.fail] at successful
      exact False.elim (drive_failed_not_success fuel _
        (.sourceGuard "UniswapV2: LOCKED") transcript returndata successful)


/-- Sync's branch-specific environmental premise concerns only its two returned words. -/
def SyncEntryNoShrink (st : State) (transcript : Transcript) : Prop :=
  st.reserve0.val ≤ transcript.firstWord.toNat ∧
    st.reserve1.val ≤ transcript.ownTail.firstWord.toNat

/-- Actual successful sync satisfies the supply-scaled product bound under NoShrink. -/
theorem runTyped_sync_product {st : State} {ctx : Context} {transcript : Transcript}
    {returndata : Bytes} (noShrink : SyncEntryNoShrink st transcript)
    (successful : (runTyped st ctx .sync transcript).status = .success returndata) :
    st.reserve0.val * st.reserve1.val *
        (runTyped st ctx .sync transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (runTyped st ctx .sync transcript).frame.current.state.reserve0.val *
        (runTyped st ctx .sync transcript).frame.current.state.reserve1.val * st.totalSupply.toNat ^ 2 := by
  have fields :
      (runTyped st ctx .sync transcript).frame.current.state.totalSupply = st.totalSupply ∧
        (runTyped st ctx .sync transcript).frame.current.state.reserve0.val = transcript.firstWord.toNat ∧
        (runTyped st ctx .sync transcript).frame.current.state.reserve1.val =
          transcript.ownTail.firstWord.toNat :=
    drive_startTyped_sync_values (current := { state := st, logs := [], updates := [] })
      (ctx := ctx) (fuel := transcript.work + 2) (transcript := transcript)
      (returndata := returndata) successful
  rcases fields with ⟨supply, reserve0, reserve1⟩
  rw [supply, reserve0, reserve1]
  exact Nat.mul_le_mul_right (st.totalSupply.toNat ^ 2) (Nat.mul_le_mul noShrink.1 noShrink.2)


/-- The two economic observations carried through actual swap continuations. -/
def SwapRunOutcome (supply : B256) (reserves : CachedReserves) (result : RunResult) : Prop :=
  result.frame.current.state.totalSupply = supply ∧
    reserves.reserve0.val * reserves.reserve1.val ≤
      result.frame.current.state.reserve0.val * result.frame.current.state.reserve1.val

/-- Successful swap checking and the real final update preserve supply and grow product. -/
theorem drive_swapBalance1_outcome {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {balance0 : B256} {transcript : Transcript} {returndata : Bytes}
    (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.swapBalance1 locals balance0))
      transcript).status = .success returndata) :
    SwapRunOutcome frame.current.state.totalSupply locals.reserves
      (drive fuel (.suspended frame request (.swapBalance1 locals balance0)) transcript) := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
          dsimp only [inputs] at checked
          simp only [checked] at resumedSuccess frameEq
          have terminal := Frame.finishUpdated_terminal (frame.beginResume request)
            balance0 balance1 locals.reserves false
            (some (.swap (frame.beginResume request).context.sender
              (Nat.toB256 inputs.1) (Nat.toB256 inputs.2)
              locals.amount0Out locals.amount1Out locals.recipient)) []
          obtain ⟨final, finished, finalEq⟩ := drive_terminal_success terminal resumedSuccess
          have fields := Frame.finishUpdated_supply_reserves finished
          rw [SwapRunOutcome, frameEq, finalEq]
          refine ⟨?_, ?_⟩
          · simpa only [Frame.beginResume] using fields.1
          · rw [fields.2.1, fields.2.2]
            exact swapCheck_product checked


/-- Both actual static balance queries consume the successful checked swap update. -/
theorem drive_swapBalance0_outcome {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.swapBalance0 locals))
      transcript).status = .success returndata) :
    SwapRunOutcome frame.current.state.totalSupply locals.reserves
      (drive fuel (.suspended frame request (.swapBalance0 locals)) transcript) := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
        have fields := drive_swapBalance1_outcome (frame := frame.beginResume request) rfl resumedSuccess
        rw [SwapRunOutcome, frameEq]
        exact fields


/-- Actual callback reentries retain locked supply before the checked observation chain. -/
theorem drive_swapCallback_outcome {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (successful : (drive fuel (.suspended frame request (.swapCallback locals))
      transcript).status = .success returndata) :
    SwapRunOutcome frame.current.state.totalSupply locals.reserves
      (drive fuel (.suspended frame request (.swapCallback locals)) transcript) := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    have supply : (frame.settleExternal fuel request result turns).current.state.totalSupply =
        frame.current.state.totalSupply := congrArg (fun core => core.1) core
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
        have fields := drive_swapBalance0_outcome rfl resumedSuccess
        rw [SwapRunOutcome, frameEq]
        exact ⟨fields.1.trans supply, fields.2⟩

/-- The actual post-transfer source branch includes the callback precisely when requested. -/
theorem Frame.afterSwapTransfer1_outcome {fuel : Nat} {frame : Frame}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (successful : (drive fuel (frame.afterSwapTransfer1 locals) transcript).status = .success returndata) :
    SwapRunOutcome frame.current.state.totalSupply locals.reserves
      (drive fuel (frame.afterSwapTransfer1 locals) transcript) := by
  by_cases callback : locals.data.length > 0
  · simp only [Frame.afterSwapTransfer1, ite_eq_left callback, Frame.suspend] at successful ⊢
    exact drive_swapCallback_outcome locked successful
  · simp only [Frame.afterSwapTransfer1, ite_eq_right callback, Frame.suspend] at successful ⊢
    exact drive_swapBalance0_outcome rfl successful


/-- The second actual transfer preserves locked supply and resumes the callback branch. -/
theorem drive_swapTransfer1_outcome {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (successful : (drive fuel (.suspended frame request (.swapTransfer1 locals))
      transcript).status = .success returndata) :
    SwapRunOutcome frame.current.state.totalSupply locals.reserves
      (drive fuel (.suspended frame request (.swapTransfer1 locals)) transcript) := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    let resumed := (frame.settleExternal fuel request result turns).beginResume request
    have resumeLocked : resumed.current.state.unlocked = 0 :=
      (congrArg (fun core => core.2.2.2.2.2) core).trans locked
    have supply : resumed.current.state.totalSupply = frame.current.state.totalSupply :=
      congrArg (fun core => core.1) core
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
        have fields := Frame.afterSwapTransfer1_outcome resumeLocked resumedSuccess
        rw [SwapRunOutcome, frameEq]
        exact ⟨fields.1.trans supply, fields.2⟩

/-- The actual post-first-transfer branch performs the second transfer exactly when nonzero. -/
theorem Frame.afterSwapTransfer0_outcome {fuel : Nat} {frame : Frame}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (successful : (drive fuel (frame.afterSwapTransfer0 locals) transcript).status = .success returndata) :
    SwapRunOutcome frame.current.state.totalSupply locals.reserves
      (drive fuel (frame.afterSwapTransfer0 locals) transcript) := by
  by_cases payout1 : locals.amount1Out > 0
  · simp only [Frame.afterSwapTransfer0, ite_eq_left payout1, Frame.suspend] at successful ⊢
    exact drive_swapTransfer1_outcome locked successful
  · simp only [Frame.afterSwapTransfer0, ite_eq_right payout1] at successful ⊢
    exact Frame.afterSwapTransfer1_outcome locked successful

/-- Both token transfers and arbitrary retained callback turns feed the actual swap check. -/
theorem drive_swapTransfer0_outcome {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SwapLocals} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (successful : (drive fuel (.suspended frame request (.swapTransfer0 locals))
      transcript).status = .success returndata) :
    SwapRunOutcome frame.current.state.totalSupply locals.reserves
      (drive fuel (.suspended frame request (.swapTransfer0 locals)) transcript) := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    let resumed := (frame.settleExternal fuel request result turns).beginResume request
    have resumeLocked : resumed.current.state.unlocked = 0 :=
      (congrArg (fun core => core.2.2.2.2.2) core).trans locked
    have supply : resumed.current.state.totalSupply = frame.current.state.totalSupply :=
      congrArg (fun core => core.1) core
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
        have fields := Frame.afterSwapTransfer0_outcome resumeLocked resumedSuccess
        rw [SwapRunOutcome, frameEq]
        exact ⟨fields.1.trans supply, fields.2⟩


/-- Every successful swap entry consumes its actual guarded transfer/callback/update chain. -/
theorem drive_startTyped_swap_outcome {fuel : Nat} {current : Checkpoint} {ctx : Context}
    {amount0Out amount1Out : B256} {recipient : Adr} {data : Bytes}
    {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (startTyped current ctx (.swap amount0Out amount1Out recipient data))
      transcript).status = .success returndata) :
    SwapRunOutcome current.state.totalSupply current.state.cachedReserves
      (drive fuel (startTyped current ctx (.swap amount0Out amount1Out recipient data)) transcript) := by
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
            by_cases validRecipient : recipient ≠ current.state.token0 ∧ recipient ≠ current.state.token1
            · rw [ite_eq_left validRecipient] at successful ⊢
              by_cases payout0 : amount0Out > 0
              · rw [ite_eq_left payout0, Frame.suspend] at successful ⊢
                exact drive_swapTransfer0_outcome rfl successful
              · rw [ite_eq_right payout0] at successful ⊢
                exact Frame.afterSwapTransfer0_outcome rfl successful
            · rw [ite_eq_right validRecipient, Frame.fail] at successful
              exact False.elim (drive_failed_not_success fuel _
                (.sourceGuard "UniswapV2: INVALID_TO") transcript returndata successful)
          · rw [ite_eq_right liquidity, Frame.fail] at successful
            exact False.elim (drive_failed_not_success fuel _
              (.sourceGuard "UniswapV2: INSUFFICIENT_LIQUIDITY") transcript returndata successful)
        · rw [ite_eq_right positiveOutput, Frame.fail] at successful
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


/-- Actual successful swaps grow the supply-scaled reserve product without a NoShrink premise. -/
theorem runTyped_swap_product {st : State} {ctx : Context} {amount0Out amount1Out : B256}
    {recipient : Adr} {data : Bytes} {transcript : Transcript} {returndata : Bytes}
    (successful : (runTyped st ctx (.swap amount0Out amount1Out recipient data) transcript).status =
      .success returndata) :
    st.reserve0.val * st.reserve1.val *
        (runTyped st ctx (.swap amount0Out amount1Out recipient data) transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (runTyped st ctx (.swap amount0Out amount1Out recipient data) transcript).frame.current.state.reserve0.val *
        (runTyped st ctx (.swap amount0Out amount1Out recipient data) transcript).frame.current.state.reserve1.val *
        st.totalSupply.toNat ^ 2 := by
  have fields : SwapRunOutcome st.totalSupply st.cachedReserves
      (runTyped st ctx (.swap amount0Out amount1Out recipient data) transcript) :=
    drive_startTyped_swap_outcome (current := { state := st, logs := [], updates := [] })
      (ctx := ctx) (amount0Out := amount0Out) (amount1Out := amount1Out)
      (recipient := recipient) (data := data) (fuel := transcript.work + 2)
      (transcript := transcript) (returndata := returndata) successful
  rw [fields.1]
  exact Nat.mul_le_mul_right (st.totalSupply.toNat ^ 2) fields.2


/-- Supply and reserves, excluding the lock released after a successful skim. -/
def State.liquidityCore (st : State) : B256 × (Fin (2 ^ 112) × Fin (2 ^ 112)) :=
  (st.totalSupply, (st.reserve0, st.reserve1))

/-- The final actual skim transfer settles nested turns before releasing only the lock. -/
theorem drive_skimTransfer1_liquidity {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SkimLocals} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (successful : (drive fuel (.suspended frame request (.skimTransfer1 locals))
      transcript).status = .success returndata) :
    (drive fuel (.suspended frame request (.skimTransfer1 locals))
      transcript).frame.current.state.liquidityCore = frame.current.state.liquidityCore := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    let resumed := (frame.settleExternal fuel request result turns).beginResume request
    have liquidity : resumed.current.state.liquidityCore = frame.current.state.liquidityCore :=
      congrArg (fun core => (core.1, core.2.1)) core
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
        have finished := congrArg (fun current : Checkpoint => current.state.liquidityCore)
          (drive_terminal_current fuel (resumed.finishLocked []) tail True.intro)
        rw [frameEq]
        exact finished.trans liquidity


/-- Skim's second balance guard feeds the real final transfer without changing stored liquidity. -/
theorem drive_skimBalance1_liquidity {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SkimLocals} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (successful : (drive fuel (.suspended frame request (.skimBalance1 locals))
      transcript).status = .success returndata) :
    (drive fuel (.suspended frame request (.skimBalance1 locals))
      transcript).frame.current.state.liquidityCore = frame.current.state.liquidityCore := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    let resumed := (frame.settleExternal fuel request result turns).beginResume request
    have resumeLocked : resumed.current.state.unlocked = 0 :=
      (congrArg (fun core => core.2.2.2.2.2) core).trans locked
    have liquidity : resumed.current.state.liquidityCore = frame.current.state.liquidityCore :=
      congrArg (fun core => (core.1, core.2.1)) core
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
        simp only [resumeSegment, decoded] at resumedSuccess frameEq
        by_cases covered : resumed.current.state.reserve1.val ≤ balance1.toNat
        · dsimp only [resumed] at covered
          simp only [ite_eq_left covered, Frame.suspend] at resumedSuccess frameEq
          have preserved := drive_skimTransfer1_liquidity resumeLocked resumedSuccess
          rw [frameEq]
          exact preserved.trans liquidity
        · dsimp only [resumed] at covered
          simp only [ite_eq_right covered, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _
            (.sourceGuard "ds-math-sub-underflow") tail returndata resumedSuccess)


/-- Skim's first actual transfer resumes the remaining observation/transfer chain. -/
theorem drive_skimTransfer0_liquidity {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SkimLocals} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (successful : (drive fuel (.suspended frame request (.skimTransfer0 locals))
      transcript).status = .success returndata) :
    (drive fuel (.suspended frame request (.skimTransfer0 locals))
      transcript).frame.current.state.liquidityCore = frame.current.state.liquidityCore := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    let resumed := (frame.settleExternal fuel request result turns).beginResume request
    have resumeLocked : resumed.current.state.unlocked = 0 :=
      (congrArg (fun core => core.2.2.2.2.2) core).trans locked
    have liquidity : resumed.current.state.liquidityCore = frame.current.state.liquidityCore :=
      congrArg (fun core => (core.1, core.2.1)) core
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
        have preserved := drive_skimBalance1_liquidity resumeLocked resumedSuccess
        rw [frameEq]
        exact preserved.trans liquidity


/-- Skim's first balance guard feeds the real first transfer without changing stored liquidity. -/
theorem drive_skimBalance0_liquidity {fuel : Nat} {frame : Frame} {request : Request}
    {locals : SkimLocals} {transcript : Transcript} {returndata : Bytes}
    (locked : frame.current.state.unlocked = 0)
    (successful : (drive fuel (.suspended frame request (.skimBalance0 locals))
      transcript).status = .success returndata) :
    (drive fuel (.suspended frame request (.skimBalance0 locals))
      transcript).frame.current.state.liquidityCore = frame.current.state.liquidityCore := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
      drive_suspended_success successful
    have core := Frame.settleExternal_locked_core locked fuel request result turns
    let resumed := (frame.settleExternal fuel request result turns).beginResume request
    have resumeLocked : resumed.current.state.unlocked = 0 :=
      (congrArg (fun core => core.2.2.2.2.2) core).trans locked
    have liquidity : resumed.current.state.liquidityCore = frame.current.state.liquidityCore :=
      congrArg (fun core => (core.1, core.2.1)) core
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
        simp only [resumeSegment, decoded] at resumedSuccess frameEq
        by_cases covered : resumed.current.state.reserve0.val ≤ balance0.toNat
        · dsimp only [resumed] at covered
          simp only [ite_eq_left covered, Frame.suspend] at resumedSuccess frameEq
          have preserved := drive_skimTransfer0_liquidity resumeLocked resumedSuccess
          rw [frameEq]
          exact preserved.trans liquidity
        · dsimp only [resumed] at covered
          simp only [ite_eq_right covered, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _
            (.sourceGuard "ds-math-sub-underflow") tail returndata resumedSuccess)


/-- Actual successful skim preserves stored supply/reserves through its guarded four-call chain. -/
theorem drive_startTyped_skim_liquidity {fuel : Nat} {current : Checkpoint} {ctx : Context}
    {recipient : Adr} {transcript : Transcript} {returndata : Bytes}
    (successful : (drive fuel (startTyped current ctx (.skim recipient)) transcript).status =
      .success returndata) :
    (drive fuel (startTyped current ctx (.skim recipient))
      transcript).frame.current.state.liquidityCore = current.state.liquidityCore := by
  by_cases paid : ctx.value ≠ 0
  · simp only [startTyped, startImmediate, ite_eq_left paid, Frame.fail] at successful
    exact False.elim (drive_failed_not_success fuel _ .emptyRevert transcript returndata successful)
  · by_cases unlocked : current.state.unlocked = 1
    · by_cases staticContext : ctx.isStatic = true
      · simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, Frame.lock,
          Frame.enter, ite_eq_left unlocked, staticContext, ite_true, Frame.fail] at successful
        exact False.elim (drive_failed_not_success fuel _ .staticWrite transcript returndata successful)
      · let lockedFrame : Frame :=
          { Frame.enter current ctx (.skim recipient) with
            current := { current with state := { current.state with unlocked := 0 } } }
        let locals : SkimLocals :=
          { recipient := recipient, token0 := current.state.token0, token1 := current.state.token1 }
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
        have suspendedSuccess :
            (drive fuel (.suspended lockedFrame
              (requestFor .skimBalance0 locals.token0 (.balanceOf ctx.pair))
              (.skimBalance0 locals)) transcript).status = .success returndata := by
          simpa only [stage, Frame.suspend] using successful
        have preserved := drive_skimBalance0_liquidity (frame := lockedFrame) rfl suspendedSuccess
        rw [stage, Frame.suspend]
        exact preserved
    · have enteredLocked : ¬(Frame.enter current ctx (.skim recipient)).current.state.unlocked = 1 :=
        unlocked
      have closed : (Frame.enter current ctx (.skim recipient)).lock =
          .error (.sourceGuard "UniswapV2: LOCKED") := by
        rw [Frame.lock, ite_eq_right enteredLocked]
      simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, closed, Frame.fail] at successful
      exact False.elim (drive_failed_not_success fuel _
        (.sourceGuard "UniswapV2: LOCKED") transcript returndata successful)


/-- Any actual immediate source segment feeds the driver with the original economic core. -/
theorem drive_startTyped_immediate_core {fuel : Nat} {current : Checkpoint} {ctx : Context}
    {entry : Entry} {segment : SegmentResult} {transcript : Transcript}
    (immediate : startImmediate current ctx entry = some segment) :
    (drive fuel (startTyped current ctx entry) transcript).frame.current.state.economicCore =
      current.state.economicCore := by
  have laws := startImmediate_core entry immediate
  rw [startTyped, immediate]
  exact (congrArg (fun current : Checkpoint => current.state.economicCore)
    (drive_terminal_current fuel segment transcript laws.1)).trans laws.2

/-- The public driver consumes a real immediate segment without changing supply/reserves. -/
theorem runTyped_immediate_liquidity {st : State} {ctx : Context} {entry : Entry}
    {transcript : Transcript}
    (immediate : ∃ segment, startImmediate { state := st, logs := [], updates := [] } ctx entry =
      some segment) :
    (runTyped st ctx entry transcript).frame.current.state.liquidityCore = st.liquidityCore := by
  rcases immediate with ⟨segment, found⟩
  exact congrArg (fun core => (core.1, core.2.1))
    (drive_startTyped_immediate_core (current := { state := st, logs := [], updates := [] })
      (ctx := ctx) (entry := entry) (segment := segment) (fuel := transcript.work + 2)
      (transcript := transcript) found)

/-- Permit's actual nonce prefix and static recovery retain the original economic core. -/
theorem drive_startTyped_permit_core {fuel : Nat} {current : Checkpoint} {ctx : Context}
    {owner spender : Adr} {value deadline : B256} {v : UInt8} {r s : B256} {transcript : Transcript} :
    (drive fuel (startTyped current ctx (.permit owner spender value deadline v r s))
      transcript).frame.current.state.economicCore = current.state.economicCore := by
  cases immediate : startImmediate current ctx (.permit owner spender value deadline v r s) with
  | some segment => exact drive_startTyped_immediate_core immediate
  | none =>
    simp only [startTyped, immediate]
    by_cases timely : ctx.timestamp ≤ deadline
    · rw [ite_eq_left timely]
      by_cases staticContext : ctx.isStatic = true
      · rw [ite_eq_left staticContext]
        exact congrArg (fun current : Checkpoint => current.state.economicCore)
          (drive_terminal_current fuel
            ((Frame.enter current ctx (.permit owner spender value deadline v r s)).fail .staticWrite)
            transcript True.intro)
      · rw [ite_eq_right staticContext]
        let nonce := current.state.nonces owner
        let post : State := { current.state with nonces := Function.update current.state.nonces owner (nonce + 1) }
        let prior := (Frame.enter current ctx (.permit owner spender value deadline v r s)).withEvents post []
        let request := requestFor .permitRecovery 1
          (.recover (permitDigest current.state owner spender value nonce deadline) v r s)
        have staticExternal : externalStatic prior request = true := by
          rw [externalStatic]
          cases prior.context.isStatic <;> rfl
        have checkpointCore : prior.checkpoint.state.economicCore = prior.current.state.economicCore := rfl
        exact drive_permit_core fuel prior request owner spender value transcript staticExternal checkpointCore
    · rw [ite_eq_right timely]
      exact congrArg (fun current : Checkpoint => current.state.economicCore)
        (drive_terminal_current fuel
          ((Frame.enter current ctx (.permit owner spender value deadline v r s)).fail
            (.sourceGuard "UniswapV2: EXPIRED")) transcript True.intro)


/-- Independent answer conditions for the two entries that can consume an unbacked observation. -/
def EntryNoShrink (st : State) (ctx : Context) (entry : Entry) (transcript : Transcript) : Prop :=
  match entry with
  | .burn recipient => BurnEntryNoShrink st ctx.pair recipient transcript
  | .sync => SyncEntryNoShrink st transcript
  | _ => True

/-- Exact fee minted at the actual third own observation of mint and burn. -/
def entryFeeAmount (st : State) (entry : Entry) (transcript : Transcript) : Nat :=
  match entry with
  | .mint _ | .burn _ =>
    feeAmount st transcript.ownTail.ownTail.firstWord.toAdr st.reserve0.val st.reserve1.val
  | _ => 0

/-- Fee-off constrains the fee-recipient answer only for entries that query it. -/
def EntryFeeOff (entry : Entry) (transcript : Transcript) : Prop :=
  match entry with
  | .mint _ | .burn _ => transcript.ownTail.ownTail.firstWord.toAdr = 0
  | _ => True

/-- The all-entry product consumer uses actual supply/reserve preservation for other entries. -/
theorem runTyped_product_of_liquidityCore {st : State} {ctx : Context} {entry : Entry}
    {transcript : Transcript}
    (zeroFee : entryFeeAmount st entry transcript = 0)
    (preserved : (runTyped st ctx entry transcript).frame.current.state.liquidityCore =
      st.liquidityCore) :
    st.reserve0.val * st.reserve1.val *
        (runTyped st ctx entry transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (runTyped st ctx entry transcript).frame.current.state.reserve0.val *
        (runTyped st ctx entry transcript).frame.current.state.reserve1.val *
        (st.totalSupply.toNat + entryFeeAmount st entry transcript) ^ 2 := by
  have supply := congrArg (fun core => core.1) preserved
  have reserve0 := congrArg (fun core => core.2.1.val) preserved
  have reserve1 := congrArg (fun core => core.2.2.val) preserved
  dsimp only [State.liquidityCore] at supply reserve0 reserve1
  rw [zeroFee, Nat.add_zero, supply, reserve0, reserve1]

/-- Every successful typed entry satisfies the exact-fee supply-scaled product bound. -/
theorem runTyped_product {st : State} {ctx : Context} {entry : Entry}
    {transcript : Transcript} {returndata : Bytes}
    (positiveSupply : 0 < st.totalSupply.toNat)
    (noShrink : EntryNoShrink st ctx entry transcript)
    (successful : (runTyped st ctx entry transcript).status = .success returndata) :
    st.reserve0.val * st.reserve1.val *
        (runTyped st ctx entry transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (runTyped st ctx entry transcript).frame.current.state.reserve0.val *
        (runTyped st ctx entry transcript).frame.current.state.reserve1.val *
        (st.totalSupply.toNat + entryFeeAmount st entry transcript) ^ 2 := by
  cases entry
  case mint recipient =>
    exact runTyped_mint_product positiveSupply successful
  case burn recipient =>
    exact runTyped_burn_product noShrink successful
  case sync =>
    simpa only [entryFeeAmount, Nat.add_zero] using runTyped_sync_product noShrink successful
  case swap amount0Out amount1Out recipient data =>
    simpa only [entryFeeAmount, Nat.add_zero] using runTyped_swap_product successful
  case skim recipient =>
    apply runTyped_product_of_liquidityCore rfl
    exact drive_startTyped_skim_liquidity
      (current := { state := st, logs := [], updates := [] }) (ctx := ctx)
      (recipient := recipient) (fuel := transcript.work + 2) (transcript := transcript)
      (returndata := returndata) successful
  case permit owner spender value deadline v r s =>
    apply runTyped_product_of_liquidityCore rfl
    exact congrArg (fun core => (core.1, core.2.1))
      (drive_startTyped_permit_core (current := { state := st, logs := [], updates := [] })
        (ctx := ctx) (owner := owner) (spender := spender) (value := value)
        (deadline := deadline) (v := v) (r := r) (s := s)
        (fuel := transcript.work + 2) (transcript := transcript))
  case «initialize» token0 token1 =>
    apply runTyped_product_of_liquidityCore rfl
    apply runTyped_immediate_liquidity
    by_cases paid : ctx.value ≠ 0
    · rw [startImmediate, ite_eq_left paid]
      exact ⟨_, rfl⟩
    · simp only [startImmediate, ite_eq_right paid, getterResult]
      by_cases authorized : ctx.sender = st.factory
      · rw [ite_eq_left authorized]
        cases ctx.isStatic <;> exact ⟨_, rfl⟩
      · rw [ite_eq_right authorized]
        exact ⟨_, rfl⟩
  all_goals
    apply runTyped_product_of_liquidityCore rfl
    apply runTyped_immediate_liquidity
    by_cases paid : ctx.value ≠ 0
    · rw [startImmediate, ite_eq_left paid]
      exact ⟨_, rfl⟩
    · simp only [startImmediate, ite_eq_right paid, getterResult]
      exact ⟨_, rfl⟩

/-- The independent fee-off answer makes the exact entry charge zero. -/
theorem entryFeeAmount_eq_zero {st : State} {entry : Entry} {transcript : Transcript}
    (feeOff : EntryFeeOff entry transcript) : entryFeeAmount st entry transcript = 0 := by
  cases entry
  case mint recipient =>
    change transcript.ownTail.ownTail.firstWord.toAdr = 0 at feeOff
    rw [entryFeeAmount, feeAmount, ite_eq_left (Or.inl feeOff)]
  case burn recipient =>
    change transcript.ownTail.ownTail.firstWord.toAdr = 0 at feeOff
    rw [entryFeeAmount, feeAmount, ite_eq_left (Or.inl feeOff)]
  all_goals rfl

/-- Every successful fee-off typed entry satisfies the original product bound. -/
theorem runTyped_feeOff_product {st : State} {ctx : Context} {entry : Entry}
    {transcript : Transcript} {returndata : Bytes}
    (positiveSupply : 0 < st.totalSupply.toNat)
    (feeOff : EntryFeeOff entry transcript)
    (noShrink : EntryNoShrink st ctx entry transcript)
    (successful : (runTyped st ctx entry transcript).status = .success returndata) :
    st.reserve0.val * st.reserve1.val *
        (runTyped st ctx entry transcript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (runTyped st ctx entry transcript).frame.current.state.reserve0.val *
        (runTyped st ctx entry transcript).frame.current.state.reserve1.val *
        st.totalSupply.toNat ^ 2 := by
  have zeroFee : entryFeeAmount st entry transcript = 0 := entryFeeAmount_eq_zero feeOff
  simpa only [zeroFee, Nat.add_zero] using runTyped_product positiveSupply noShrink successful


/-- Initial pricing uses the checked product and its exact floor root minus the locked minimum. -/
theorem mintAmount_initial_spec {amount0 amount1 supply : B256}
    {reserve0 reserve1 liquidity : Nat} (zeroSupply : supply = 0)
    (accepted : mintAmount amount0 amount1 supply reserve0 reserve1 = .ok liquidity) :
    liquidity = Nat.sqrt (amount0.toNat * amount1.toNat) - 1000 ∧
      liquidity < 2 ^ 256 ∧ 1000 ≤ Nat.sqrt (amount0.toNat * amount1.toNat) ∧
      amount0.toNat * amount1.toNat < 2 ^ 256 := by
  rw [mintAmount, ite_eq_left zeroSupply] at accepted
  by_cases productBound : amount0.toNat * amount1.toNat < 2 ^ 256
  · rw [ite_eq_left productBound] at accepted
    by_cases minimumCovered : 1000 ≤ Nat.sqrt (amount0.toNat * amount1.toNat)
    · rw [ite_eq_left minimumCovered] at accepted
      have liquidityEq := (Except.ok.inj accepted).symm
      refine ⟨liquidityEq, ?_, minimumCovered, productBound⟩
      rw [liquidityEq]
      exact Nat.lt_of_le_of_lt
        ((Nat.sub_le _ _).trans (Nat.sqrt_le_self _)) productBound
    · rw [ite_eq_right minimumCovered] at accepted
      cases accepted
  · rw [ite_eq_right productBound] at accepted
    cases accepted

/-- At zero supply a successful protocol-fee query issues no LP credit or fee event. -/
theorem mintFee_zero_supply {st : State} {feeTo : Adr} {reserve0 reserve1 : Nat}
    {fee : FeeResult} (zeroSupply : st.totalSupply = 0)
    (accepted : mintFee st feeTo reserve0 reserve1 = .ok fee) :
    fee.state.totalSupply = 0 ∧ fee.state.balanceOf = st.balanceOf ∧
      fee.minted = 0 ∧ fee.events = [] := by
  rw [mintFee] at accepted
  by_cases feeOff : feeTo = 0
  · rw [ite_eq_left feeOff] at accepted
    rw [← Except.ok.inj accepted]
    exact ⟨zeroSupply, rfl, rfl, rfl⟩
  · rw [ite_eq_right feeOff] at accepted
    by_cases noLast : st.kLast = 0
    · rw [ite_eq_left noLast] at accepted
      rw [← Except.ok.inj accepted]
      exact ⟨zeroSupply, rfl, rfl, rfl⟩
    · rw [ite_eq_right noLast] at accepted
      by_cases growing : Nat.sqrt st.kLast.toNat < Nat.sqrt (reserve0 * reserve1)
      · rw [ite_eq_left growing] at accepted
        have zeroBound : 0 < 2 ^ 256 := by decide
        simp only [zeroSupply, B256.toNat_zero, Nat.zero_mul, zeroBound, ite_true,
          Nat.zero_div, Nat.lt_irrefl, ite_false] at accepted
        by_cases scaledRootBound : Nat.sqrt (reserve0 * reserve1) * 5 < 2 ^ 256
        · rw [ite_eq_left scaledRootBound] at accepted
          by_cases denominatorBound :
              Nat.sqrt (reserve0 * reserve1) * 5 + Nat.sqrt st.kLast.toNat < 2 ^ 256
          · rw [ite_eq_left denominatorBound] at accepted
            rw [← Except.ok.inj accepted]
            exact ⟨zeroSupply, rfl, rfl, rfl⟩
          · rw [ite_eq_right denominatorBound] at accepted
            cases accepted
        · rw [ite_eq_right scaledRootBound] at accepted
          cases accepted
      · rw [ite_eq_right growing] at accepted
        rw [← Except.ok.inj accepted]
        exact ⟨zeroSupply, rfl, rfl, rfl⟩

/-- A successful checked LP mint retains the exact sequential ledger credit and event. -/
theorem State.mintLP_ledger {st post : State} {recipient : Adr} {value : B256}
    {events : List Event} (accepted : st.mintLP recipient value = .ok (post, events)) :
    post.balanceOf = Blanc.ledgerCredit st.balanceOf recipient value ∧
      events = [.transfer 0 recipient value] := by
  rw [State.mintLP] at accepted
  by_cases supplyBound : st.totalSupply.toNat + value.toNat < 2 ^ 256
  · rw [ite_eq_left supplyBound] at accepted
    by_cases balanceBound : (st.balanceOf recipient).toNat + value.toNat < 2 ^ 256
    · rw [ite_eq_left balanceBound] at accepted
      have fields := Prod.mk.inj (Except.ok.inj accepted)
      rw [← fields.1, ← fields.2]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right balanceBound] at accepted
      cases accepted
  · rw [ite_eq_right supplyBound] at accepted
    cases accepted


/-- Reserve accounting retains the already-issued LP ledger. -/
theorem State.update_ledger {st post : State} {ctx : Context}
    {balance0 balance1 : B256} {reserve0 reserve1 : Nat} {event : Event} {update : OracleUpdate}
    (accepted : st.update ctx balance0 balance1 reserve0 reserve1 = .ok (post, event, update)) :
    post.balanceOf = st.balanceOf := by
  rw [State.update] at accepted
  by_cases bound0 : balance0.toNat < 2 ^ 112
  · rw [dite_eq_left bound0] at accepted
    by_cases bound1 : balance1.toNat < 2 ^ 112
    · rw [dite_eq_left bound1] at accepted
      exact (congrArg (fun result : State × Event × OracleUpdate => result.1.balanceOf)
        (Except.ok.inj accepted)).symm
    · rw [dite_eq_right bound1] at accepted
      cases accepted
  · rw [dite_eq_right bound0] at accepted
    cases accepted

/-- Completing an update retains the LP ledger and the selected return bytes. -/
theorem Frame.finishUpdated_ledger_output {frame final : Frame} {balance0 balance1 : B256}
    {reserves : CachedReserves} {feeOn : Bool} {lastEvent : Option Event} {returndata output : Bytes}
    (accepted : frame.finishUpdated balance0 balance1 reserves feeOn lastEvent returndata =
      .finished final output) :
    final.current.state.balanceOf = frame.current.state.balanceOf ∧ output = returndata := by
  rw [Frame.finishUpdated] at accepted
  cases updated : frame.current.state.update frame.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val with
  | error failure =>
    simp only [updated, Frame.fail] at accepted
    cases accepted
  | ok result =>
    rcases result with ⟨post, event, update⟩
    simp only [updated] at accepted
    have ledger := State.update_ledger updated
    cases feeOn <;> cases lastEvent <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, Frame.withUpdate, Frame.withEvents,
        Frame.finishLocked, Frame.finish, SegmentResult.finished.injEq] at accepted
    all_goals
      rw [← accepted.1]
      exact ⟨ledger, accepted.2.symm⟩

/-- Exact first-mint economics, with two sequential credits even when the addresses alias. -/
def InitialMintResult (prior : State) (observed : MintObserved) (post : State)
    (returndata : Bytes) : Prop :=
  let root := Nat.sqrt (observed.amount0.toNat * observed.amount1.toNat)
  1000 < root ∧ observed.amount0.toNat * observed.amount1.toNat < 2 ^ 256 ∧
    post.totalSupply.toNat = root ∧
    post.balanceOf = Blanc.ledgerCredit (Blanc.ledgerCredit prior.balanceOf 0 1000)
      observed.recipient (Nat.toB256 (root - 1000)) ∧
    post.reserve0.val = observed.balance0.toNat ∧ post.reserve1.val = observed.balance1.toNat ∧
    returndata = encodeWords [Nat.toB256 (root - 1000)]


/-- A successful first-mint continuation realizes its floor root, locked credit and return. -/
theorem Frame.mintAfterFee_initial {frame final : Frame} {observed : MintObserved}
    {fee : FeeResult} {feeTo : Adr} {returndata : Bytes}
    (zeroSupply : frame.current.state.totalSupply = 0)
    (feeAccepted : mintFee frame.current.state feeTo observed.reserves.reserve0.val
      observed.reserves.reserve1.val = .ok fee)
    (accepted : frame.mintAfterFee observed fee = .finished final returndata) :
    InitialMintResult frame.current.state observed final.current.state returndata := by
  have feeSpec := mintFee_zero_supply zeroSupply feeAccepted
  rw [Frame.mintAfterFee] at accepted
  cases priced : mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val with
  | error failure =>
    simp only [priced, Frame.fail] at accepted
    cases accepted
  | ok liquidity =>
    simp only [priced, ite_eq_left feeSpec.1] at accepted
    cases minimumMinted : fee.state.mintLP 0 1000 with
    | error failure =>
      simp only [minimumMinted, Frame.fail] at accepted
      cases accepted
    | ok minimumResult =>
      rcases minimumResult with ⟨postMinimum, minimumEvents⟩
      simp only [minimumMinted] at accepted
      by_cases positive : liquidity > 0
      · rw [ite_eq_left positive] at accepted
        cases userMinted : postMinimum.mintLP observed.recipient (Nat.toB256 liquidity) with
        | error failure =>
          simp only [userMinted, Frame.fail] at accepted
          cases accepted
        | ok userResult =>
          rcases userResult with ⟨post, events⟩
          simp only [userMinted] at accepted
          have pricing := mintAmount_initial_spec feeSpec.1 priced
          have minimumSupply := State.mintLP_supply minimumMinted
          have userSupply := State.mintLP_supply userMinted
          have minimumNat : (1000 : B256).toNat = 1000 := by decide
          rw [feeSpec.1, B256.toNat_zero, minimumNat, Nat.zero_add] at minimumSupply
          rw [B256.toNat_toB256_of_lt pricing.2.1] at userSupply
          have minimumLedger := State.mintLP_ledger minimumMinted
          have userLedger := State.mintLP_ledger userMinted
          have finalFields := Frame.finishUpdated_supply_reserves accepted
          have finalLedger := Frame.finishUpdated_ledger_output accepted
          have rootPositive : 1000 < Nat.sqrt (observed.amount0.toNat * observed.amount1.toNat) := by
            have increasing := Nat.add_lt_add_left positive 1000
            rw [pricing.1, Nat.add_zero, Nat.add_sub_of_le pricing.2.2.1] at increasing
            exact increasing
          rw [InitialMintResult]
          refine ⟨rootPositive, pricing.2.2.2, ?_, ?_,
            finalFields.2.1, finalFields.2.2, ?_⟩
          · rw [finalFields.1]
            change post.totalSupply.toNat = Nat.sqrt (observed.amount0.toNat * observed.amount1.toNat)
            rw [userSupply, minimumSupply, pricing.1]
            exact Nat.add_sub_of_le pricing.2.2.1
          · rw [finalLedger.1]
            change post.balanceOf = _
            rw [userLedger.1, minimumLedger.1, feeSpec.2.1, pricing.1]
          · rw [finalLedger.2, pricing.1]
      · simp only [ite_eq_right positive, Frame.fail] at accepted
        cases accepted

/-- The first-mint continuation always terminates without another external request. -/
theorem Frame.mintAfterFee_terminal_initial (frame : Frame) (observed : MintObserved)
    (fee : FeeResult) (zeroSupply : fee.state.totalSupply = 0) :
    (frame.mintAfterFee observed fee).Terminal := by
  rw [Frame.mintAfterFee]
  cases priced : mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val with
  | error failure => simp only [Frame.fail, SegmentResult.Terminal]
  | ok liquidity =>
    simp only [ite_eq_left zeroSupply]
    cases minimumMinted : fee.state.mintLP 0 1000 with
    | error failure => simp only [Frame.fail, SegmentResult.Terminal]
    | ok minimumResult =>
      rcases minimumResult with ⟨postMinimum, minimumEvents⟩
      dsimp only []
      by_cases positive : liquidity > 0
      · rw [ite_eq_left positive]
        cases userMinted : postMinimum.mintLP observed.recipient (Nat.toB256 liquidity) with
        | error failure => simp only [Frame.fail, SegmentResult.Terminal]
        | ok userResult =>
          rcases userResult with ⟨post, events⟩
          exact Frame.finishUpdated_terminal _ observed.balance0 observed.balance1 observed.reserves
            fee.feeOn (some (.mint frame.context.sender observed.amount0 observed.amount1))
            (encodeWords [Nat.toB256 liquidity])
      · simp only [ite_eq_right positive, Frame.fail, SegmentResult.Terminal]

/-- The finite driver consumes the actual first-mint completion, including its aliased credits. -/
theorem Frame.mintAfterFee_driver_initial {fuel : Nat} {frame : Frame} {observed : MintObserved}
    {fee : FeeResult} {feeTo : Adr} {transcript : Transcript} {returndata : Bytes}
    (zeroSupply : frame.current.state.totalSupply = 0)
    (feeAccepted : mintFee frame.current.state feeTo observed.reserves.reserve0.val
      observed.reserves.reserve1.val = .ok fee)
    (successful : (drive fuel (frame.mintAfterFee observed fee) transcript).status = .success returndata) :
    InitialMintResult frame.current.state observed
      (drive fuel (frame.mintAfterFee observed fee) transcript).frame.current.state returndata := by
  have feeSpec := mintFee_zero_supply zeroSupply feeAccepted
  obtain ⟨final, finished, frameEq⟩ :=
    drive_terminal_success
      (Frame.mintAfterFee_terminal_initial frame observed fee feeSpec.1) successful
  rw [frameEq]
  exact Frame.mintAfterFee_initial zeroSupply feeAccepted finished


/-- The two balance observations determine mint's cached deposit words. -/
def mintObservation (recipient : Adr) (reserves : CachedReserves)
    (balance0 balance1 : B256) : MintObserved :=
  { recipient := recipient, reserves := reserves, balance0 := balance0, balance1 := balance1,
    amount0 := balance0 - Nat.toB256 reserves.reserve0.val,
    amount1 := balance1 - Nat.toB256 reserves.reserve1.val }

/-- A successful initial fee query consumes the actual decoded recipient and completion. -/
theorem drive_mintFee_initial {fuel : Nat} {frame : Frame} {request : Request}
    {observed : MintObserved} {transcript : Transcript} {returndata : Bytes}
    (zeroSupply : frame.current.state.totalSupply = 0)
    (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.mintFee observed))
      transcript).status = .success returndata) :
    InitialMintResult frame.current.state observed
      (drive fuel (.suspended frame request (.mintFee observed))
        transcript).frame.current.state returndata := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
        cases charged : mintFee (frame.beginResume request).current.state feeTo
            observed.reserves.reserve0.val observed.reserves.reserve1.val with
        | error failure =>
          simp only [resumeSegment, decoded, charged, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _ failure tail returndata resumedSuccess)
        | ok fee =>
          simp only [resumeSegment, decoded, charged] at resumedSuccess frameEq
          have initial := Frame.mintAfterFee_driver_initial
            (frame := frame.beginResume request) zeroSupply charged resumedSuccess
          rw [frameEq]
          exact initial

/-- Initial mint's checked second observation reaches the exact source fee/completion result. -/
theorem drive_mintBalance1_initial {fuel : Nat} {frame : Frame} {request : Request}
    {recipient owner : Adr} {reserves : CachedReserves} {balance0 : B256}
    {transcript : Transcript} {returndata : Bytes}
    (zeroSupply : frame.current.state.totalSupply = 0)
    (operation : request.operation = .balanceOf owner) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.mintBalance1 recipient reserves balance0))
      transcript).status = .success returndata) :
    InitialMintResult frame.current.state (mintObservation recipient reserves balance0 transcript.firstWord)
      (drive fuel (.suspended frame request (.mintBalance1 recipient reserves balance0))
        transcript).frame.current.state returndata := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
          have initial := drive_mintFee_initial (frame := frame.beginResume request)
            zeroSupply rfl resumedSuccess
          rw [frameEq]
          simpa only [shape, Transcript.firstWord, ← observedWord, mintObservation,
            Frame.beginResume] using initial
        · simp only [ite_eq_right backing, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _
            (.sourceGuard "ds-math-sub-underflow") tail returndata resumedSuccess)


/-- The first mint balance query preserves its ledger and selects both actual returned words. -/
theorem drive_mintBalance0_initial {fuel : Nat} {frame : Frame} {request : Request}
    {recipient owner : Adr} {reserves : CachedReserves} {transcript : Transcript} {returndata : Bytes}
    (zeroSupply : frame.current.state.totalSupply = 0)
    (operation : request.operation = .balanceOf owner) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.mintBalance0 recipient reserves))
      transcript).status = .success returndata) :
    InitialMintResult frame.current.state
      (mintObservation recipient reserves transcript.firstWord transcript.ownTail.firstWord)
      (drive fuel (.suspended frame request (.mintBalance0 recipient reserves))
        transcript).frame.current.state returndata := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, complete, resumedSuccess, frameEq⟩ :=
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
        have initial := drive_mintBalance1_initial (frame := frame.beginResume request)
          zeroSupply rfl rfl resumedSuccess
        rw [frameEq]
        simpa only [shape, Transcript.firstWord, Transcript.ownTail, ← observedWord,
          Frame.beginResume] using initial

/-- Successful zero-supply entries derive their source guards and complete the first-mint formula. -/
theorem drive_startTyped_mint_initial {fuel : Nat} {current : Checkpoint} {ctx : Context}
    {recipient : Adr} {transcript : Transcript} {returndata : Bytes}
    (zeroSupply : current.state.totalSupply = 0)
    (successful : (drive fuel (startTyped current ctx (.mint recipient)) transcript).status =
      .success returndata) :
    InitialMintResult current.state
      (mintObservation recipient current.state.cachedReserves
        transcript.firstWord transcript.ownTail.firstWord)
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
        have initial := drive_mintBalance0_initial (frame := lockedFrame)
          zeroSupply rfl rfl suspendedSuccess
        rw [stage, Frame.suspend]
        simpa only [InitialMintResult, lockedFrame, Frame.enter, reserves] using initial
    · have enteredLocked : ¬(Frame.enter current ctx (.mint recipient)).current.state.unlocked = 1 :=
        unlocked
      have closed : (Frame.enter current ctx (.mint recipient)).lock =
          .error (.sourceGuard "UniswapV2: LOCKED") := by
        rw [Frame.lock, ite_eq_right enteredLocked]
      simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, closed, Frame.fail] at successful
      exact False.elim (drive_failed_not_success fuel _
        (.sourceGuard "UniswapV2: LOCKED") transcript returndata successful)

/-- Actual first mint returns floor sqrt minus 1000 and credits the minimum before the recipient. -/
theorem runTyped_mint_initial {st : State} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {returndata : Bytes} (zeroSupply : st.totalSupply = 0)
    (successful : (runTyped st ctx (.mint recipient) transcript).status = .success returndata) :
    InitialMintResult st
      (mintObservation recipient st.cachedReserves transcript.firstWord transcript.ownTail.firstWord)
      (runTyped st ctx (.mint recipient) transcript).frame.current.state returndata := by
  exact drive_startTyped_mint_initial
    (current := { state := st, logs := [], updates := [] }) (ctx := ctx) (recipient := recipient)
    (fuel := transcript.work + 2) (transcript := transcript) (returndata := returndata)
    zeroSupply successful


/-- The first-mint final supply is the floor-root reference integer for the checked deposits. -/
theorem runTyped_mint_initial_floor {st : State} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {returndata : Bytes} (zeroSupply : st.totalSupply = 0)
    (successful : (runTyped st ctx (.mint recipient) transcript).status = .success returndata) :
    let observed := mintObservation recipient st.cachedReserves
      transcript.firstWord transcript.ownTail.firstWord
    let product := observed.amount0.toNat * observed.amount1.toNat
    (runTyped st ctx (.mint recipient) transcript).frame.current.state.totalSupply.toNat ^ 2 ≤ product ∧
      product < ((runTyped st ctx (.mint recipient) transcript).frame.current.state.totalSupply.toNat + 1) ^ 2 := by
  dsimp only []
  exact Nat.eq_sqrt'.mp (runTyped_mint_initial zeroSupply successful).2.2.1

end Blanc.Lift.UniswapV2Pair
