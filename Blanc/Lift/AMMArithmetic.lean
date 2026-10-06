import Jaune.MulDiv

/-!
# Integer share-value bounds for two-reserve AMMs

These natural-number laws concern floor issuance and redemption. Word overflow,
callee acceptance and the relation between observations and stored reserves are
supplied by each consumer. No token premise is part of the pricing definitions.
-/

namespace Blanc.Lift.AMMArithmetic

/-- Two-reserve issuance floors both proportional quotients. -/
def mintLiquidity (amount0 amount1 supply reserve0 reserve1 : Nat) : Nat :=
  min (amount0 * supply / reserve0) (amount1 * supply / reserve1)

/-- Redemption floors one proportional payout. -/
def burnPayment (liquidity balance supply : Nat) : Nat :=
  liquidity * balance / supply

/-- Multiplying the two side bounds yields the cross-product share bound. -/
theorem product_share_bound {reserve0 reserve1 balance0 balance1 supply finalSupply : Nat}
    (side0 : reserve0 * finalSupply ≤ balance0 * supply)
    (side1 : reserve1 * finalSupply ≤ balance1 * supply) :
    reserve0 * reserve1 * finalSupply ^ 2 ≤ balance0 * balance1 * supply ^ 2 := by
  simpa only [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    Nat.mul_le_mul side0 side1

/-- Any issuance below a proportional floor preserves this reserve's share bound. -/
theorem mint_side_bound {reserve amount supply liquidity : Nat}
    (floorBound : liquidity ≤ amount * supply / reserve) :
    reserve * (supply + liquidity) ≤ (reserve + amount) * supply := by
  have scaledFloor : reserve * liquidity ≤ amount * supply :=
    (Nat.mul_le_mul_left reserve floorBound).trans
      (Jaune.Nat.mul_div_mul_le amount supply reserve)
  calc
    reserve * (supply + liquidity) = reserve * supply + reserve * liquidity :=
      Nat.mul_add reserve supply liquidity
    _ ≤ reserve * supply + amount * supply :=
      Nat.add_le_add_left scaledFloor (reserve * supply)
    _ = (reserve + amount) * supply := (Nat.add_mul reserve amount supply).symm

/-- Minimum-of-floors issuance preserves the two-reserve share product. -/
theorem mint_product_bound (reserve0 reserve1 amount0 amount1 supply : Nat) :
    reserve0 * reserve1 *
        (supply + mintLiquidity amount0 amount1 supply reserve0 reserve1) ^ 2 ≤
      (reserve0 + amount0) * (reserve1 + amount1) * supply ^ 2 := by
  apply product_share_bound
  · exact mint_side_bound (Nat.min_le_left _ _)
  · exact mint_side_bound (Nat.min_le_right _ _)

/-- A transfer-aware final answer retains the burned supply's share backing. -/
theorem burn_side_bound {reserve balance finalBalance supply liquidity : Nat}
    (backing : reserve ≤ balance)
    (covered : liquidity ≤ supply)
    (debit : balance ≤ finalBalance + burnPayment liquidity balance supply) :
    reserve * (supply - liquidity) ≤ finalBalance * supply := by
  have scaledFloor : burnPayment liquidity balance supply * supply ≤ liquidity * balance := by
    exact Nat.div_mul_le_self (liquidity * balance) supply
  have expanded : balance * supply ≤ finalBalance * supply + balance * liquidity := by
    calc
      balance * supply ≤ (finalBalance + burnPayment liquidity balance supply) * supply :=
        Nat.mul_le_mul_right supply debit
      _ = finalBalance * supply + burnPayment liquidity balance supply * supply :=
        Nat.add_mul finalBalance (burnPayment liquidity balance supply) supply
      _ ≤ finalBalance * supply + liquidity * balance :=
        Nat.add_le_add_left scaledFloor (finalBalance * supply)
      _ = finalBalance * supply + balance * liquidity := by rw [Nat.mul_comm liquidity balance]
  have retained : balance * (supply - liquidity) ≤ finalBalance * supply := by
    apply Nat.le_of_add_le_add_right
    calc
      balance * (supply - liquidity) + balance * liquidity = balance * supply := by
        rw [← Nat.mul_add, Nat.sub_add_cancel covered]
      _ ≤ finalBalance * supply + balance * liquidity := expanded
  exact (Nat.mul_le_mul_right (supply - liquidity) backing).trans retained

/-- Floored burn payouts and transfer-aware backing preserve the share product. -/
theorem burn_product_bound {reserve0 reserve1 balance0 balance1 final0 final1 supply liquidity : Nat}
    (backing0 : reserve0 ≤ balance0) (backing1 : reserve1 ≤ balance1)
    (covered : liquidity ≤ supply)
    (debit0 : balance0 ≤ final0 + burnPayment liquidity balance0 supply)
    (debit1 : balance1 ≤ final1 + burnPayment liquidity balance1 supply) :
    reserve0 * reserve1 * (supply - liquidity) ^ 2 ≤ final0 * final1 * supply ^ 2 := by
  exact product_share_bound (burn_side_bound backing0 covered debit0)
    (burn_side_bound backing1 covered debit1)

/-- A fee-adjusted acceptance product implies growth of the unadjusted product. -/
theorem swap_product_bound {reserve0 reserve1 balance0 balance1 adjusted0 adjusted1 scale : Nat}
    (positiveScale : 0 < scale)
    (adjustedBound0 : adjusted0 ≤ scale * balance0)
    (adjustedBound1 : adjusted1 ≤ scale * balance1)
    (accepted : scale ^ 2 * (reserve0 * reserve1) ≤ adjusted0 * adjusted1) :
    reserve0 * reserve1 ≤ balance0 * balance1 := by
  apply Nat.le_of_mul_le_mul_left (c := scale * scale)
  · calc
      scale * scale * (reserve0 * reserve1) ≤ adjusted0 * adjusted1 := by
        simpa only [Nat.pow_two] using accepted
      _ ≤ (scale * balance0) * (scale * balance1) :=
        Nat.mul_le_mul adjustedBound0 adjustedBound1
      _ = scale * scale * (balance0 * balance1) := by
        simp only [Nat.mul_left_comm, Nat.mul_comm]
  · exact Nat.mul_pos positiveScale positiveScale

end Blanc.Lift.AMMArithmetic
