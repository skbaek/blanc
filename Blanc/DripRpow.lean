-- DripRpow.lean : the exact arithmetic identity and certified error surface
-- consumed by DRIP's compiled fresh-index walk.

import Blanc.DripCore
import Jaune.RPow

/-!
# DRIP rpow arithmetic

This module instantiates Jaune's public, Nat-level rpow surface at DRIP's
frozen constants.  It keeps expanded-tree accounting, runtime operation
accounting, and outer floor composition visibly separate.  The later compiled
walk bridge discharges `RPowGuards`; none of the Nat headlines below assumes a
word-safety premise.
-/

namespace Blanc

open Jaune

namespace Drip

/-- The Nat image of DRIP's exact Maker-shaped rpow factor. -/
def factorNat (k : Nat) : Nat :=
  Jaune.rpow scale.toNat half.toNat rate.toNat k

/-- Floor-compose a realized factor onto a Nat index. -/
def freshNat (chi k : Nat) : Nat :=
  chi * factorNat k / scale.toNat

/-- Exact floor residue left by the outer index composition. -/
def compositionResidue (chi k : Nat) : Nat :=
  chi * factorNat k % scale.toNat

@[simp] theorem scaleNat_exact : scale.toNat = 1000000000000000000000000000 := by
  decide +kernel

@[simp] theorem rateNat_exact :
    rate.toNat = 1000000001547125957863212448 := by
  decide +kernel

@[simp] theorem halfNat_exact : half.toNat = 500000000000000000000000000 := by
  decide +kernel

@[simp] theorem maxElapsedNat_exact : maxElapsed.toNat = 4294967295 := by
  decide +kernel

theorem scaleNat_ne_zero : scale.toNat ≠ 0 := by
  decide +kernel

theorem rateNat_ne_zero : rate.toNat ≠ 0 := by
  decide +kernel

theorem halfNat_lt_scaleNat : half.toNat < scale.toNat := by
  decide +kernel

theorem scaleNat_le_rateNat : scale.toNat ≤ rate.toNat := by
  decide +kernel

/-- Jaune's guarded word loop has exactly DRIP's Nat factor as its image.  A
compiled-occurrence theorem later derives the guard bundle from the checks
actually crossed by the runtime. -/
theorem drip_rpow_word_exact (k : Nat)
    (guards : B256.RPowGuards scale half rate k) :
    (B256.rpow scale half rate k).toNat = factorNat k := by
  exact B256.toNat_rpow (by decide +kernel) k guards

/-- R1 exact additive identity, with expanded algebraic nodes and scale leaves
kept distinct from runtime loop operations. -/
theorem drip_rpow_exact_telescope (k : Nat) :
    scale.toNat ^ (rpowTree half.toNat k).nodes * factorNat k +
        (rpowTree half.toNat k).exactUnder scale.toNat rate.toNat 0 =
      rate.toNat ^ k *
          scale.toNat ^ (rpowTree half.toNat k).scaleCount +
        (rpowTree half.toNat k).exactOver scale.toNat rate.toNat 0 := by
  exact Jaune.rpow_exact_telescope halfNat_lt_scaleNat rate.toNat k

/-- R1's asymmetric certified two-sided band.  This is deliberately not a
minimality statement. -/
theorem drip_rpow_certified_band (k : Nat) :
    scale.toNat ^ (rpowTree half.toNat k).nodes * factorNat k ≤
        rate.toNat ^ k *
            scale.toNat ^ (rpowTree half.toNat k).scaleCount +
          (rpowTree half.toNat k).upperError scale.toNat rate.toNat 0 ∧
      rate.toNat ^ k *
            scale.toNat ^ (rpowTree half.toNat k).scaleCount ≤
        scale.toNat ^ (rpowTree half.toNat k).nodes * factorNat k +
          (rpowTree half.toNat k).lowerError scale.toNat rate.toNat 0 := by
  exact ⟨Jaune.rpow_scaled_upper _ _ _ _,
    Jaune.rpow_scaled_lower scaleNat_ne_zero _ _ _⟩

theorem factorNat_base_preserved (k : Nat) :
    scale.toNat ≤ factorNat k := by
  exact Jaune.rpow_base_preserved scaleNat_ne_zero scaleNat_le_rateNat
    half.toNat k

/-- R4's arithmetic step: composing any DRIP factor cannot lower an index. -/
theorem freshNat_mono (chi k : Nat) : chi ≤ freshNat chi k := by
  exact Jaune.le_floor_compose scaleNat_ne_zero
    (factorNat_base_preserved k) chi

/-- The frozen certified comparison of any two partitions with the same total
elapsed time. -/
theorem drip_segment_certified
    (chi : Nat) {left right : List Nat} (sameElapsed : left.sum = right.sum) :
    natDistance
        (segmentIndex scale.toNat half.toNat rate.toNat chi left)
        (segmentIndex scale.toNat half.toNat rate.toNat chi right) ≤
      max
        (segmentDriftForward scale.toNat half.toNat rate.toNat chi left right)
        (segmentDriftForward scale.toNat half.toNat rate.toNat chi right left) := by
  exact Jaune.segmentIndex_drift_le halfNat_lt_scaleNat
    rate.toNat chi sameElapsed

private theorem binaryDepth_le_of_lt_pow_two {n b : Nat}
    (h : n < 2 ^ b) : binaryDepth n ≤ b := by
  induction b generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      simp [binaryDepth]
  | succ b ih =>
      rw [binaryDepth]
      split
      · omega
      · have hhalf : n / 2 < 2 ^ b := by
          rw [pow_succ] at h
          omega
        have hrec := ih hhalf
        omega

private theorem binaryWeight_le_of_lt_pow_two {n b : Nat}
    (h : n < 2 ^ b) : binaryWeight n ≤ b := by
  induction b generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      simp [binaryWeight]
  | succ b ih =>
      rw [binaryWeight]
      split
      · omega
      · have hhalf : n / 2 < 2 ^ b := by
          rw [pow_succ] at h
          omega
        have hrec := ih hhalf
        split <;> omega

/-- The runtime loop's rounded-multiply accounting is the binary-depth plus
population count, not the expanded tree's node count. -/
theorem drip_rpow_runtime_ops_exact (k : Nat) :
    rpowOps rate.toNat k =
      if k = 0 then 0 else binaryDepth (k / 2) + binaryWeight (k / 2) := by
  rw [rpowOps_eq_depth_add_weight, if_neg rateNat_ne_zero]

/-- The frozen four-byte elapsed ceiling admits at most 62 rounded runtime
multiplications. -/
theorem drip_rpow_runtime_ops_le_62 {k : Nat}
    (hk : k ≤ maxElapsed.toNat) :
    rpowOps rate.toNat k ≤ 62 := by
  rw [maxElapsedNat_exact] at hk
  by_cases hk0 : k = 0
  · subst k
    simp [rpowOps]
  · rw [drip_rpow_runtime_ops_exact, if_neg hk0]
    have hhalf : k / 2 < 2 ^ 31 := by
      norm_num
      omega
    have hd := binaryDepth_le_of_lt_pow_two hhalf
    have hw := binaryWeight_le_of_lt_pow_two hhalf
    omega

/-! ## Frozen attained witnesses -/

theorem factorNat_three_exact :
    factorNat 3 = 1000000004641377880770433536 := by
  decide +kernel

/-- At `k = 2`, the square's rounded result lies below its exact scaled
product by the frozen nonzero amount. -/
theorem rpow_under_witness :
    rate.toNat * rate.toNat =
      scale.toNat * factorNat 2 + 494162619157761202382152704 := by
  decide +kernel

/-- At `k = 3`, the accumulator multiplication lies above its exact scaled
product by the frozen nonzero amount. -/
theorem rpow_over_witness :
    scale.toNat * factorNat 3 =
      rate.toNat * factorNat 2 + 308476035340184723845916000 := by
  decide +kernel

/-- The approved nonzero schedule-spread witness, including its nonminimal
certified bound. -/
theorem segment_spread_witness :
    segmentIndex scale.toNat half.toNat rate.toNat scale.toNat [3] =
        1000000004641377880770433536 ∧
      segmentIndex scale.toNat half.toNat rate.toNat scale.toNat [1, 2] =
        1000000004641377880770433535 ∧
      natDistance
        (segmentIndex scale.toNat half.toNat rate.toNat scale.toNat [3])
        (segmentIndex scale.toNat half.toNat rate.toNat scale.toNat [1, 2]) = 1 ∧
      max
        (segmentDriftForward scale.toNat half.toNat rate.toNat scale.toNat
          [3] [1, 2])
        (segmentDriftForward scale.toNat half.toNat rate.toNat scale.toNat
          [1, 2] [3]) = 4 := by
  decide +kernel

/-! ## Zero/exponent edge cases -/

/-- At `k = 0` the factor is the scale: same-timestamp accrual is a no-op by
arithmetic, not by a special case. -/
theorem drip_factorNat_zero : factorNat 0 = scale.toNat :=
  Jaune.rpow_exponent_zero _ _ _

/-- The frozen base word is nonzero. -/
theorem drip_rate_ne_zero : rate ≠ 0 := by
  decide +kernel

/-- The frozen base never takes the word loop's zero arm: low-bit
initialization followed by the halved loop, exactly the runtime's order. -/
theorem drip_word_rpow_unfold_nonzero {k : Nat} (hk : k ≠ 0) :
    B256.rpow scale half rate k =
      B256.rpowLoop scale half (if k % 2 = 1 then rate else scale) rate
        (k / 2) := by
  unfold B256.rpow
  rw [if_neg drip_rate_ne_zero, if_neg hk]

end Drip

end Blanc
