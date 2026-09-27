import Blanc.AddressSlotProofs

namespace Blanc.Lift.Weth9

open Jaune
open Blanc

/- The literal words used by the lifted WETH9 straight-line entries.  Keeping
   these facts public lets the entry proofs share the same normalization of
   bytecode literals. -/

theorem w00_eq : Bytes.toB256 [0x00] = 0 := by decide
theorem w03_eq : Bytes.toB256 [0x03] = 3 := by decide
theorem w20_eq : Bytes.toB256 [0x20] = 32 := by decide
theorem w32_add_0 : (32 : B256) + 0 = 32 := by decide
theorem w32_add_32 : (32 : B256) + 32 = 64 := by decide
theorem w0_toNat : (0 : B256).toNat = 0 := by decide
theorem w32_toNat : (32 : B256).toNat = 32 := by decide
theorem w64_toNat : (64 : B256).toNat = 64 := by decide

theorem w04_eq : Bytes.toB256 [0x04] = 4 := by decide

/-- `iszero(iszero(iszero(lt(bal, wad))))` is nonzero only when `wad ≤ bal`. -/
theorem le_of_check {bal wad : B256}
    (h : ((((bal <? wad) =? 0) =? 0) =? 0) ≠ 0) : wad ≤ bal := by
  rw [← B256.not_lt]
  intro hlt
  apply h
  rw [B256.ltCheck, ite_eq_left_of_eq_true _ _ (eq_true hlt)]
  decide

end Blanc.Lift.Weth9
