import Blanc.Lift.UniswapV2Pair.Model

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

end Blanc.Lift.UniswapV2Pair
