import Blanc.CommonProofs

/-! Unsigned word-length ABI guards under actual calldata representability. -/
namespace Blanc.Lift
open Jaune

/-- The two modular word guards are exactly a natural calldata lower bound. -/
theorem word_calldata_guards_iff {sevm : Sevm} {n : Nat}
    (representable : sevm.data.length < 2 ^ 256) (argumentBound : n < 2 ^ 256) :
    ((4 : B256) ≤ sevm.data.length.toB256 ∧
      n.toB256 ≤ sevm.data.length.toB256 - 4) ↔ n + 4 ≤ sevm.data.length := by
  constructor
  · rintro ⟨size, guard⟩
    have natGuard := B256.toNat_le_toNat guard
    rw [B256.toNat_sub_eq_of_le _ _ size, B256.toNat_toB256_of_lt representable,
      B256.toNat_toB256_of_lt argumentBound] at natGuard
    change n ≤ sevm.data.length - 4 at natGuard
    have natSize := B256.toNat_le_toNat size
    rw [B256.toNat_toB256_of_lt representable] at natSize
    change 4 ≤ sevm.data.length at natSize
    omega
  · intro length
    have size : (4 : B256) ≤ sevm.data.length.toB256 := by
      apply B256.le_of_toNat_le_toNat
      rw [B256.toNat_toB256_of_lt representable]
      change 4 ≤ sevm.data.length
      omega
    refine ⟨size, ?_⟩
    apply B256.le_of_toNat_le_toNat
    rw [B256.toNat_sub_eq_of_le _ _ size, B256.toNat_toB256_of_lt representable,
      B256.toNat_toB256_of_lt argumentBound]
    change n ≤ sevm.data.length - 4
    omega

end Blanc.Lift
