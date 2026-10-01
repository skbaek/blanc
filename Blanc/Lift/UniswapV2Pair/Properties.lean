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

end Blanc.Lift.UniswapV2Pair
